import { Source_Position, Lexer } from "./token";
import { Name, Datum, Bundle, Prefix_Expander, Operator_Nature, Operator_Arity, Infix_Expander, Slot_Specifier, Class_Nature, Class_Modifier, Function_Nature, Char, Internal_Array, Macro_Context, Type_Union } from "./datum";
import { Module, lookup, add_definition, Known_Definition, Method_Modifiers, parse_body, parse_expression, parse_name, lookup_known_definition, parse_actualparameters, Unresolved_Type, datum_string, datum_print,  in_type_union, in_type_intersection, lte_type_union, lte_type_intersection, Scope, parse_anyname, parse_methodhead, parse_formalparameters, parse_operator, parse_methodmodifiers, Call_Expression, Expression } from "./expression";
import { macro_prefix_def, macro_infix_paren, macro_prefix_paren, macro_prefix_fun, macro_prefix_defmacro, macro_prefix_if, macro_infix_assigment, macro_infix_and, macro_infix_or, macro_prefix_template, macro_prefix_literal, macro_prefix_defclass, macro_infix_dot, macro_infix_bracket, macro_prefix_for, internal_list_append_token_sequence, macro_prefix_block, macro_prefix_require } from "./builtin_macros";
import { Runtime } from "./js_runtime";
import { JS_context, JS_builtin_intrinsic_methods } from "./js_compile";
import { instantiate_generic_bundle, classof, is_subclass_or_equal, is_member_of } from "./class";
import { compare_methods, Runtime_Method_Datum, Runtime_Method_Head } from "./method";

const source_position = new Source_Position('compiler', -1);

function init_polyform_Module($poly: Runtime): Module {
    const module = new Module(Name.make('polyform'));

    const name = (spelling: string) => Name.make(spelling);
    const known = (name: Name, datum: Datum) => 
        add_definition(module, name, new Known_Definition(source_position, name, datum));
    const bundle = (name: Name) => known(name, new Bundle(name));

    const bundle_names = [
        'everything',
        'nothing',

        // scope
        'scope',
        'global_scope',
        'local_scope',
        'formal_parameter_scope',
        'generic_parameter_scope',
        'macro_context',
    
        // expressions and tokens
        'newline',
        'keyword',
        'name',
        'quotation',
        'unresolved_type',
        'compound_expression',
            'exit_expression',
            'exit_call_expression',
            'prog_expression',
            'call_expression',
                'spread_call_expression',
            'definition',
                'known_definition',
                'constant_definition',
                'variable_definition',
                'formal_parameters',
                'formal_parameter_definition',
                'unresolved_generic_parameter_definition',
            'if_expression',
            'assigment_expression',
            'method_expression',
            'instance_expression',
            'slot_read_expression',
            'slot_write_expression',
        'block_scope',
            'block_head_scope',
            'block_tail_scope',
        
        // primitives
        'number',
            'integer',
            'float',
        'boolean',
            '_true',
            '_false',
        'string',
        'character',
    
        // sequences
        'sequence',
            'succession',
                'internal_list',
                'internal_array',
            'list',
    
        // bundle and bundle natures
        'type',
        'type_union',
        'type_intersection',
        'bundle',
            'class_bundle',
            'function_bundle',
            'class_function_bundle',
            'operator_bundle',
            'class_operator_bundle',
            'function_operator_bundle',
            'class_function_operator_bundle',
        'class',
        'function',
            'method',
        'operator',

        // macros
        'if',
        'fun',
        'defmacro',
        'defclass',
        'def',

        // additional...
        'token_stream',
        'internal_set',
        'class_expression',
        'superclass_expression',

        // operators
        '+',
        '-',
        '*',
        '/',
        'mod',
        '^',
        '&',
        '|',
        '~',
        '(',
        '[',
        '{',
        '.',
        '.:=',
        '..',
        '..<',
        '<..',
        '<..<',
        ':=',
        '=',
        '~=',
        '<',
        '<=',
        '>',
        '>=',
        'eq',
        '<<',
        '>>',
        '#',
        '`',
        '\\',
        'and',
        'or',
        'not',
        'in',
        'as',
    ]
    bundle_names.forEach(spelling => bundle(name(spelling)));

    const locbundle = (name: Name | string) => {
        name = typeof name == 'string' ? Name.make(name) : name;
        let defn = lookup(module, name) as any;
        if (!defn) {
            bundle(name);
            defn = lookup(module, name) as any
        }
        return defn.value as Bundle;   
    }

    type method_head = {
        required: Datum[], 
        optional: Datum[], 
        named: Map<Name, Datum>, 
        result: Datum, 
        rest?: Datum
    };

    const register_method = (name: Name, head: method_head, modifiers: Method_Modifiers[], method: Function) => {
        const method_id = $poly.method_index++;
        $poly.method_heads[method_id] = new Runtime_Method_Head(
            name,
            method_id,
            new Set(modifiers),
            head.required,
            head.optional,
            head.named,
            head.result,
            head.rest);
        $poly.method_datums[method_id] = new Runtime_Method_Datum(
            method_id,
            method);
        return $poly.method_datums[method_id];
    }

    const method = (n: Name, head: method_head, modifiers: Method_Modifiers[], method: Function) => {
        const defn = locbundle(n);
        defn.function = defn.function ? defn.function : new Function_Nature();
        defn.function.methods.push(register_method(n, head, modifiers, method));
        defn.function.methods.sort((a, b) => compare_methods(a.id, b.id));
    }

    const method_head = (result: Datum, required: Datum[], optional?: Datum[], named?: Map<Name, Datum>, rest?: Datum) => {
        const dename = (r: Datum) => r instanceof Name ? locbundle(r) : r;
        return {
            result: dename(result),
            required: required.map((r) => dename(r)), 
            optional: optional ? optional.map((r) => dename(r)) : [], 
            named: named ? new Map(Array.from(named.entries()).
                map(e => [e[0], dename(e[1])])) : new Map(), 
            rest: rest ? dename(rest) : undefined,
        };
    }

    const prefix_macro = (n: Name, prefix: Prefix_Expander) => {
        const defn = locbundle(n);
        defn.operator = defn.operator ? defn.operator : new Operator_Nature();
        defn.operator.prefix_expander = register_method(
            n,
            method_head(name('everything'), [
                name('token_stream'),
                name('integer'), 
                name('scope'), 
                name('everything'), 
                name('everything'), // module | macro_context
            ]), 
            [],
            prefix);
        defn.operator.arity.add('prefix');
    }

    const defparser = (n: Name, parser: any) => {
        method(n,
            method_head(name('everything'), [
                name('token_stream'),
                name('integer'), 
                name('scope'), 
                name('boolean'), 
            ]),
            [],
            parser);
    }

    const infix_macro = (n: Name, infix: Infix_Expander) => {
        const defn = locbundle(n);
        defn.operator = defn.operator ? defn.operator : new Operator_Nature();
        defn.operator.infix_expander = register_method(
            n,
            method_head(name('everything'), [
                name('everything'), // expression
                name('token_stream'),
                name('integer'), 
                name('scope'), 
                name('everything'), // module | macro_context
                name('boolean')
            ]), 
            [],
            infix);
        defn.operator.arity.add('infix');
    }

    const operator = (name: Name, left_precedence: number, right_precedence: number, ...arity: Operator_Arity[]) => {
        const defn = locbundle(name);
        defn.operator = defn.operator ? defn.operator : new Operator_Nature();
        defn.operator.left_precedence = left_precedence;
        defn.operator.right_precedence = right_precedence;
        for (let a of arity) {
            defn.operator.arity.add(a);
        }
    }

    const classn = (n: Name, _superclasses: Name[], slots: Slot_Specifier[], modifiers?: Class_Modifier[]) => {
        _superclasses.push(name('everything'));
        const defn = (lookup(module, n) as any).value as Bundle;
        const superclasses = _superclasses.reduce((pv: Bundle[], cv) => {
            const bundle = lookup_known_definition(module, cv) as Bundle;
            const parent_superclasses = bundle.class?.superclasses || [];
            return Array.from(new Set(pv.concat(...[bundle, ...parent_superclasses])));
        }, []);
        const class_id = $poly.class_index++;
        defn.class = new Class_Nature(
            class_id,
            n,
            superclasses,
            slots,
            modifiers ? new Set(modifiers) : new Set(),
        );
    }
    
    known(name('max_length'), Number.MAX_SAFE_INTEGER);

    operator(name('+'), 50, 50, 'unary', 'binary');
    operator(name('-'), 50, 50, 'unary', 'binary');
    operator(name('*'), 60, 60, 'binary');
    operator(name('/'), 60, 60, 'binary');
    operator(name('mod'), 50, 50, 'binary');
    operator(name('^'), 71, 70, 'binary');
    operator(name('&'), 60, 60, 'binary');
    operator(name('|'), 50, 50, 'binary');
    operator(name('~'), 50, 50, 'unary', 'binary');
    operator(name('('), 80, 80, 'prefix', 'infix');
    operator(name('['), 80, 80, 'prefix', 'infix');
    operator(name('{'), 80, 80, 'prefix', 'infix');
    operator(name('.'), 90, 90, 'infix');
    operator(name('..'), 40, 40, 'binary');
    operator(name('..<'), 40, 40, 'binary');
    operator(name('<..'), 40, 40, 'binary');
    operator(name('<..<'), 40, 40, 'binary');
    operator(name(':='), 80, 0, 'infix');
    operator(name('='), 30, 30, 'ternary');
    operator(name('~='), 30, 30, 'ternary');
    operator(name('<'), 30, 30, 'ternary');
    operator(name('<='), 30, 30, 'ternary');
    operator(name('>'), 30, 30, 'ternary');
    operator(name('>='), 30, 30, 'ternary');
    operator(name('eq'), 75, 75, 'binary');
    operator(name('<<'), 75, 75, 'binary');
    operator(name('>>'), 75, 75, 'binary');
    operator(name('and'), 20, 20, 'infix');
    operator(name('or'), 10, 10, 'infix');
    operator(name('not'), 0, 0, 'unary');
    operator(name('in'), 40, 40, 'binary');
    operator(name('as'), 0, 0, 'binary');

    prefix_macro(name('def'), macro_prefix_def);
    prefix_macro(name('defclass'), macro_prefix_defclass);
    prefix_macro(name('defmacro'), macro_prefix_defmacro);
    prefix_macro(name('fun'), macro_prefix_fun);
    prefix_macro(name('if'), macro_prefix_if);
    prefix_macro(name('`'), macro_prefix_template);
    prefix_macro(name('('), macro_prefix_paren);
    prefix_macro(name('#'), macro_prefix_literal);
    prefix_macro(name('for'), macro_prefix_for);
    prefix_macro(name('block'), macro_prefix_block);
    prefix_macro(name('require'), macro_prefix_require);
    
    infix_macro(name('('), macro_infix_paren);
    infix_macro(name('['), macro_infix_bracket);
    infix_macro(name(':='), macro_infix_assigment);
    infix_macro(name('or'), macro_infix_or);
    infix_macro(name('and'), macro_infix_and);
    infix_macro(name('.'), macro_infix_dot);

    classn(name('everything'), [], []);
    classn(name('nothing'), [], []);

    classn(name('scope'), [], []);
    classn(name('global_scope'), 
        [name('scope')], 
        []);
    classn(name('local_scope'),
        [name('scope')], 
        []);
    classn(name('formal_parameter_scope'),
        [name('scope')], 
        []);
    classn(name('macro_context'), [], []);
    classn(name('generic_parameter_scope'),
        [name('scope')],
        []);

    classn(name('newline'), [], []);
    classn(name('keyword'), [], []);
    classn(name('name'), [], []);
    classn(name('quotation'), [], []);
    classn(name('compound_expression'), [], []);
    classn(name('prog_expression'), 
        [name('compound_expression')], 
        []);
    classn(name('call_expression'), 
        [name('compound_expression')], 
        []);
    classn(name('spread_call_expression'), 
        [name('call_expression')], 
        []);
    classn(name('definition'), 
        [name('compound_expression')], 
        []);
    classn(name('known_definition'), 
        [name('definition')], 
        []);
    classn(name('constant_definition'), 
        [name('definition')], 
        []);
    classn(name('variable_definition'), 
        [name('definition')], 
        []);
    classn(name('formal_parameters'), 
        [], 
        []);
    classn(name('formal_parameter_definition'), 
        [name('definition')], 
        []);
    classn(name('if_expression'), 
        [name('compound_expression')], 
        []);
    classn(name('assigment_expression'), 
        [name('compound_expression')], 
        []);
    classn(name('method_expression'), 
        [name('compound_expression')], 
        []);
    classn(name('instance_expression'), 
        [name('compound_expression')], 
        []);
    classn(name('slot_read_expression'), 
        [name('compound_expression')], 
        []);
    classn(name('slot_write_expression'), 
        [name('compound_expression')], 
        []);
    classn(name('block_scope'), 
        [name('local_scope')], 
        []);
    classn(name('block_head_scope'), 
        [name('block_scope')], 
        []);
    classn(name('block_tail_scope'), 
        [name('block_scope')], 
        []);

    classn(name('number'), [], []);
    classn(name('integer'), 
        [name('number')], 
        []);
    classn(name('float'), 
        [name('number')], 
        []);

    classn(name('boolean'), [], []);
    classn(name('_true'), 
        [name('boolean')], 
        []); // ???
        known(name('true'), true);
    classn(name('_false'), 
        [name('boolean')], 
        []); // ???
        known(name('false'), false);

    classn(name('string'), [], []);
    classn(name('character'), 
        [], 
        []);
    method(name('character'), 
        method_head(name('character'), [name('integer')]),
        [],
        (code: number) => new Char(code));
    method(name('.'),
        method_head(name('integer'), [name('character'), new Set([name('code')])]),
        ['intrinsic', 'sealed'],
        (char: Char) => char.code);
    method(name('='), 
        method_head(name('boolean'), [name('character'), name('character')]),
        ['sealed', 'intrinsic'],
        (x: Char, y: Char) => x.code == y.code);

    classn(name('sequence'), 
        [], 
        []);
    classn(name('list'), 
        [name('sequence')], 
        []);
    classn(name('succession'), 
        [], 
        []);
    classn(name('internal_list'), 
        [name('sequence')], 
        [],
        ['sealed', 'intrinsic']);

    classn(name('type'), [], []);
        classn(name('type_union'), [name('type')], []);
        classn(name('type_intersection'), [name('type')], []);
    classn(name('class'), [name('type')], []);
    classn(name('unresolved_generic_parameter_definition'), [], []);
    classn(name('unresolved_type'), [name('type')], []);
    classn(name('function'), [], []);
    classn(name('method'), [name('function')], []);
    classn(name('operator'), [], []);

    classn(name('class_expression'), [], []);

    classn(name('bundle'), 
        [], 
        []);
    classn(name('class_bundle'), 
        [name('bundle'), name('class')], 
        []);
    classn(name('function_bundle'), 
        [name('bundle'), name('function')], 
        []);
    classn(name('class_function_bundle'), 
        [name('bundle'), name('class'), name('function')], 
        []);
    classn(name('operator_bundle'), 
        [name('bundle'), name('operator')], 
        []);
    classn(name('class_operator_bundle'), 
        [name('bundle'), name('class'), name('operator')], 
        []);
    classn(name('function_operator_bundle'), 
        [name('bundle'), name('function'), name('operator')], 
        []);
    classn(name('class_function_operator_bundle'), 
        [name('bundle'), name('function'), name('operator')], 
        []);

    classn(name('token_stream'), [], []);
    classn(name('internal_set'), [], []);

    method(name('|'),
        method_head(name('type_union'), [name('type'), name('type')]),
        [],
        (x: Datum, y: Datum) => new $poly.objmap.Type_Union(x, y));
    method(name('&'),
        method_head(name('type_intersection'), [name('type'), name('type')]),
        [],
        (x: Datum, y: Datum) => new $poly.objmap.Type_Intersection(x, y));
    method(name('in'),
        method_head(name('boolean'), [name('everything'), name('type_union')]),
        [],
        in_type_union);
    method(name('in'),
        method_head(name('boolean'), [name('everything'), name('type_intersection')]),
        [],
        in_type_intersection);
    method(name('<='),
        method_head(name('boolean'), [name('type_union'), name('type')]),
        [],
        lte_type_union);
    method(name('<='),
        method_head(name('boolean'), [name('type'), name('type_union')]),
        [],
        lte_type_union);
    method(name('<='),
        method_head(name('boolean'), [name('type_intersection'), name('type')]),
        [],
        lte_type_intersection);
        method(name('<='),
    method_head(name('boolean'), [name('class'), name('type_intersection')]),
        [],
        lte_type_intersection);

    method(name('+'), 
        method_head(name('integer'), [name('integer'), name('integer')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x + y);
    method(name('+'), 
        method_head(name('number'), [name('number'), name('float')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x + y);
    method(name('+'), 
        method_head(name('number'), [name('float'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x + y);
    method(name('+'), 
        method_head(name('string'), [name('string'), name('string')]),
        ['sealed', 'intrinsic'],
        (x: string, y: string) => x + y);
    method(name('+'), 
        method_head(name('integer'), [name('integer')]),
        ['sealed', 'intrinsic'],
        (x: number) => x);
    method(name('+'), 
        method_head(name('float'), [name('float')]),
        ['sealed', 'intrinsic'],
        (x: number) => x);
    
    method(name('-'), 
        method_head(name('integer'), [name('integer'), name('integer')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x - y);
    method(name('-'), 
        method_head(name('number'), [name('float'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x - y);
    method(name('-'), 
        method_head(name('number'), [name('number'), name('float')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x - y);
    method(name('-'), 
        method_head(name('integer'), [name('integer')]),
        ['sealed', 'intrinsic'],
        (x: number) => -x);
    method(name('-'), 
        method_head(name('float'), [name('float')]),
        ['sealed', 'intrinsic'],
        (x: number) => -x);

    method(name('*'), 
        method_head(name('integer'), [name('integer'), name('integer')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x * y);
    method(name('*'), 
        method_head(name('number'), [name('float'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x * y);
    method(name('*'), 
        method_head(name('number'), [name('number'), name('float')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x * y);
    method(name('*'), 
        method_head(name('string'), [name('string'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: string, y: number) => x.repeat(y));
    method(name('*'), 
        method_head(name('string'), [name('number'), name('string')]),
        ['sealed', 'intrinsic'],
        (x: number, y: string) => y.repeat(x));
    
    method(name('/'), 
        method_head(name('integer'), [name('integer'), name('integer')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => Math.floor(x / y));
    method(name('/'), 
        method_head(name('number'), [name('float'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x / y);
    method(name('/'), 
        method_head(name('number'), [name('number'), name('float')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x / y);

    method(name('mod'), 
        method_head(name('integer'), [name('integer'), name('integer')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x % y);

    method(name('^'), 
        method_head(name('number'), [name('number'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => Math.pow(x, y));

    method(name('&'), 
        method_head(name('number'), [name('number'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x & y);

    method(name('|'), 
        method_head(name('number'), [name('number'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x | y);

    method(name('~'), 
        method_head(name('number'), [name('number'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x ^ y);

    method(name('eq'), 
        method_head(name('boolean'), [name('everything'), name('everything')]),
        ['sealed', 'intrinsic'],
        (x: Datum, y: Datum) => x === y);

    method(name('>>'), 
        method_head(name('number'), [name('number'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x >> y);
    method(name('<<'), 
        method_head(name('number'), [name('number'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x << y);

    method(name('='), 
        method_head(name('boolean'), [name('number'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x == y);
    method(name('='), 
        method_head(name('boolean'), [name('string'), name('string')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x == y);
    method(name('='), 
        method_head(name('boolean'), [name('character'), name('character')]),
        ['sealed', 'intrinsic'],
        (x: Char, y: Char) => x.code == y.code);

    method(name('<'), 
        method_head(name('boolean'), [name('number'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x < y);

    method(name('<='), 
        method_head(name('boolean'), [name('number'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x <= y);

    method(name('>'), 
        method_head(name('boolean'), [name('number'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x > y);

    method(name('>='), 
        method_head(name('boolean'), [name('number'), name('number')]),
        ['sealed', 'intrinsic'],
        (x: number, y: number) => x >= y);

    method(name('not'), 
        method_head(name('boolean'), [name('everything')]),
        ['sealed', 'intrinsic'],
        (x: boolean) => x === false);

    method(name('next'),
        method_head(name('everything'), [name('token_stream')]),
        ['sealed'],
        (x: Lexer) => { const tok = x.read(0); return tok === undefined ? false : tok});
    method(name('next!'),
        method_head(name('everything'), [name('token_stream')]),
        ['sealed'],
        (x: Lexer) => { const tok = x.read(1); return tok === undefined ? false : tok});
    method(name('match?'),
        method_head(name('everything'), [name('token_stream'), name('name')]),
        ['sealed'],
        (x: Lexer, y: Name) => x.match_name(y) || false);
    method(name('match!'),
        method_head(name('everything'), [name('token_stream'), name('name')]),
        ['sealed'],
        (x: Lexer, y: Name) => x.must_match_name(y) || false);
    method(name('insert!'),
        method_head(name('everything'), [name('token_stream'), name('internal_list')]),
        ['sealed'],
        (lexer: Lexer, seq: any[]) => lexer.insert(seq));

    method(name('class'),
        method_head(name('class'), [name('everything')]),
        ['sealed'],
        classof);

    method(name('in'),
        method_head(name('boolean'), [name('everything'), name('class')]),
        [],
        is_member_of);
    method(name('<='),
        method_head(name('boolean'), [name('class'), name('class')]),
        [],
        is_subclass_or_equal);

    method(name('in'),
        method_head(name('boolean'), [name('everything'), name('unresolved_type')]),
        [],
        (x: Datum, type: Unresolved_Type) => true);
    method(name('<='),
        method_head(name('boolean'), [name('class'), name('unresolved_type')]),
        [],
        (x: Datum, type: Unresolved_Type) => true);

    method(name('in'),
        method_head(name('boolean'), [name('everything'), name('internal_set')]),
        [],
        (x: Datum, y: Set<any>) => y.has(x));

    method(name('internal_list'),
        method_head(name('internal_list'), []),
        ['sealed', 'intrinsic'],
        () => []);
    method(name('append!'),
        method_head(name('everything'), [
            name('internal_list')], 
            [], new Map(), 
            name('everything')),
            ['sealed', 'intrinsic'],
        (arr: Datum[], items: Internal_Array) => arr.push(...items.array));
    method(name('append_token_sequence!'),
        method_head(name('everything'), [
            name('internal_list')], 
            [name('integer')], new Map(), 
            name('everything')),
            ['sealed', 'intrinsic'],
        internal_list_append_token_sequence);
    method(name('.'),
        method_head(name('integer'), [name('internal_list'), new Set([Name.make('length')])]),
        ['sealed', 'intrinsic'],
        (seq: Datum[]) => seq.length);
    method(name('iterate'),
        method_head(name('integer'), [name('internal_list')]),
        ['sealed', 'intrinsic'],
        (seq: Datum[]) => 0);
    method(name('iterate'),
        method_head(name('integer'), [name('internal_list'), name('integer')]),
        ['sealed', 'intrinsic'],
        (seq: Datum[], i: number) => i + 1);
    method(name('more?'),
        method_head(name('integer'), [name('internal_list'), name('integer')]),
        ['sealed', 'intrinsic'],
        (seq: Datum[], i: number) => i < seq.length);
    method(name('next'),
        method_head(name('everything'), [name('internal_list'), name('integer')]),
        ['sealed', 'intrinsic'],
        (seq: Datum[], i: number) => i >= 0 && i < seq.length ? seq[i] : false);
    method(name('in'),
        method_head(name('boolean'), [name('everything'), name('internal_list')]),
        ['sealed', 'intrinsic'],
        (x: Datum, seq: Datum[]) => seq.indexOf(x) !== -1);
    method(name('['),
        method_head(name('everything'), [name('internal_list'), name('integer')]),
        ['sealed', 'intrinsic'],
        (seq: Datum[], i: number) => i >= 0 && i < seq.length ? seq[i] : false);
    method(name('[:='),
        method_head(name('everything'), [name('internal_list'), name('integer'), name('everything')]),
        ['sealed', 'intrinsic'],
        (seq: Datum[], i: number, datum: Datum) => i >= 0 && i < seq.length ? seq[i] = datum : false);

    method(name('internal_array_length'),
        method_head(name('integer'), [name ('everything')]),
        ['sealed', 'intrinsic'],
        (arr: Internal_Array) => arr.length);
    method(name('internal_array_element_get'),
        method_head(name('everything'), [name('everything'), name('everything')]),
        ['sealed', 'intrinsic'],
        (arr: Internal_Array, i: number) => arr.array[i]);
    method(name('internal_array_element_set'),
        method_head(name('everything'), [name('everything'), name('everything'), name('everything')]),
        ['sealed', 'intrinsic'],
        (arr: Internal_Array, i: number, value: Datum) => arr.array[i] = value);

    method(name('internal_string_length'),
        method_head(name('integer'), [name ('everything')]),
        ['sealed', 'intrinsic'],
        (arr: string) => arr.length);
    method(name('internal_string_character_get'),
        method_head(name('character'), [name('everything'), name('everything')]),
        ['sealed', 'intrinsic'],
        (arr: string, i: number) => new $poly.objmap.Char(arr.charCodeAt(i)));

    method(name('name'),
        method_head(name('name'), 
            [name('everything')],
            [name('everything')]),
        [],
        (x: Name | string, y?: Macro_Context | Module) => $poly.name(x, y));
    method(name('macro_context'),
        method_head(name('macro_context'), 
            [name('scope')]),
        [],
        (x: Scope) => new $poly.objmap.Macro_Context(x));

    method(name('parse_expression'),
        method_head(name('everything'), [
            name('token_stream'),
            name('integer'), 
            name('scope'), 
            name('boolean'), 
        ], [name('integer')]),
        [],
        parse_expression);
    defparser(name('parse_name'), parse_name);
    defparser(name('parse_anyname'), parse_anyname);
    defparser(name('parse_actualparameters'), parse_actualparameters);
    defparser(name('parse_methodhead'), parse_methodhead);
    defparser(name('parse_formalparameters'), parse_formalparameters);
    defparser(name('parse_operator'), parse_operator);
    defparser(name('parse_methodmodifiers'), parse_methodmodifiers);
    defparser(name('parse_body'), parse_body);

    known(name('expression'), new Type_Union(
        locbundle('name'), 
        locbundle('number'), 
        locbundle('character'),
        locbundle('string'),
        locbundle('quotation'),
        locbundle('compound_expression'),
        locbundle('block_scope')));

    method(name('call_expression'),
        method_head(name('string'), 
            [name('token_stream'), name('expression')],
            [],
            new Map(),
            name('expression')),
        [],
        (lexer: Lexer, lhs: Expression, parameters: Internal_Array) => 
            new Call_Expression(lexer.position(), lhs, parameters.array, false));

    method(name('instantiate_generic_bundle'),
        method_head(name('class'), [
            name('bundle'),
        ], 
        [], new Map(), 
        name('everything')),
        ['intrinsic', 'sealed'],
        instantiate_generic_bundle);

    method(name('string'),
        method_head(name('string'), [name('everything')]),
        [],
        datum_string)

    method(name('print'),
        method_head(name('everything'), 
        [], [], new Map(),
        name('everything')),
        ['intrinsic'],
        datum_print);

    return module;
}

export function init_modules_Module($poly?: Runtime): Module {
    const module = new Module(Name.make('modules'));
    $poly = $poly ? $poly : new Runtime(module);
    if (!Runtime.instance) {
        (typeof window === 'undefined' ? global : window as any).$poly = $poly;
        Runtime.instance = $poly;
    }

    const name = (spelling: string) => Name.make(spelling, module);
    const known = (name: Name, datum: Datum) => 
    add_definition(module, name, new Known_Definition(source_position, name, datum));

    const polyform = init_polyform_Module($poly);

    module.imports.push(
        {
            module: polyform,
            pattern: '*',
        },
    );

    known(name('modules'), module);
    known(name('polyform'), polyform);

    JS_context.builtin_intrinsics = JS_builtin_intrinsic_methods($poly);

    return module;
}
