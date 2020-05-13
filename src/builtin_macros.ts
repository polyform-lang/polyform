import { Token, Newline, Lexer, Source_Position, Parse_Error } from "./token";
import { Macro_Context, Bundle, Function_Nature, Char, Operator_Nature, Datum, Slot_Specifier, Class_Nature, Class_Modifier, Name, Generic_Class_Instance_Maker, Type } from "./datum";
import { Module, parse_expression, Quotation, parse_name, Known_Definition, evaluate_type, Variable_Definition, Definition, Constant_Definition, parse_methodhead_after_name, parse_methodhead, Method_Head, Block_Scope, Prog_Expression, Scope, Method_Expression, parse_body, Expression, parse_actualparameters, Call_Expression, parse_anyname, parse_methodmodifiers, parse_formalparameters, Formal_Parameters, Formal_Parameter_Definition, Formal_Parameter_Scope, expand_definition, lookup_known_definition, add_definition, lookup, If_Expression, Assigment_Expression, parse_denatured_name, Superclass_Expression, Class_Expression, Generic_Parameter_Scope, parse_methodhead_assigment, Unresolved_Type, source_location_of, sequence_to_internal_list, is_sequence, Compound_Expression, generate_exit_method, Exit_Expression, Unresolved_Generic_Parameter_Definition } from "./expression";
import { Runtime } from "./js_runtime";
import { generate_class_generic_instance_maker_method, evaluate_class_superclasses, combine_slots, generate_class_constructor_method, _Batch_Definer, define_class_slot_operations, instantiate_generic_bundle } from "./class";
import { method_expression_to_datum, add_method_expression } from "./method";

export function macro_prefix_literal(lexer: Lexer, indentation: number, scope: Scope, modifiers: Set<string>, previous_context?: Macro_Context | Module): Expression | Token[] {
    const anyname = parse_anyname(lexer, indentation, scope, true);
    return new Quotation(Name.make(anyname as Name));
}

export function macro_prefix_require(lexer: Lexer, indentation: number, scope: Scope, modifiers: Set<string>, previous_context?: Macro_Context | Module): Expression | Token[] {
    const $poly = Runtime.instance;

    const generic_scope = new Generic_Parameter_Scope(scope);
    const generic_parameter = new Unresolved_Generic_Parameter_Definition(
        lexer.position(), Name.make('?'), $poly.lookup('everything'));
    add_definition(generic_scope, Name.make('?'), generic_parameter);

    const head = parse_methodhead(lexer, indentation, generic_scope, true) as Method_Head;
    let defn = lookup(scope, head.name);
    let expanded_definition: Expression = head.name;
    if (defn === undefined) {
        defn = new Known_Definition(lexer.position(), head.name, new Bundle(head.name));
        expanded_definition = expand_definition(scope, head.name, defn);
    }
    if (!(defn instanceof Known_Definition && defn.value instanceof Bundle))
        throw new Error('incompatible definitions');
    let arr = $poly.requirements.get(defn);
    if (arr == undefined) {
        arr = [];
        $poly.requirements.set(defn, arr);
    }
    arr.push(head);
    return expanded_definition;
}

export function macro_prefix_defoperator(lexer: Lexer, indentation: number, scope: Scope, modifiers: Set<string>, previous_context?: Macro_Context | Module): Expression | Token[] {
    // const anyname = parse_anyname(lexer, indentation, scope, true) as Name;
    let body_newline = lexer.match_newline(indentation, true);
    if (!lexer.match_keyword('precedence')) {
        throw new Error(`expected #precedence:`);
    }
    const precedence_integers: number[] = [];
    do {
        const precedence = lexer.read(1);
        if (typeof precedence != 'number') {
            throw new Error(`precedence must be integer!`);
        }
        precedence_integers.push(precedence);
    } while(lexer.match_name(','));
    if (!body_newline) {
        body_newline = lexer.match_newline(indentation, true);
        // TODO
    }
    // TODO
    return new Quotation(false);
} 

export function macro_prefix_defmacro(lexer: Lexer, indentation: number, scope: Scope, modifiers: Set<string>, previous_context?: Macro_Context | Module): Expression | Token[] {
    const position = lexer.position();

    const anyname = parse_anyname(lexer, indentation, scope, true) as Name;
    lexer.must_match_name('=>')

    let bundle: Bundle | undefined;
    let expanded_definition: Expression | undefined;
    const existing_definition = lookup(scope, anyname);
    if (existing_definition) {
        if (existing_definition instanceof Known_Definition && existing_definition.value instanceof Bundle) {
            bundle = existing_definition.value as Bundle;
            expanded_definition = bundle.name
        } else {
            throw new Error('incompatible definitions');
        }
    } else {
        bundle = new Bundle(anyname)
        const defn = new Known_Definition(position, anyname, bundle);
        expanded_definition = expand_definition(scope, anyname, defn);
    }

    const parameters = new Formal_Parameters(scope);
    const add_parameter = (name: Name) => {
        const formal = new Formal_Parameter_Definition(
            lexer.position(),
            name,
            lookup_known_definition(scope, 'everything') as Datum);
        const new_scope = new Formal_Parameter_Scope(parameters.scope);
        add_definition(new_scope, name, formal);
        parameters.scope = new_scope;
        parameters.required.push(formal);
    }
    add_parameter(Name.make('lexer', previous_context));
    add_parameter(Name.make('indentation', previous_context));
    add_parameter(Name.make('scope', previous_context));
    add_parameter(Name.make('modifiers', previous_context));
    add_parameter(Name.make('previous_context', previous_context));

    const head_body = new Block_Scope(parameters.scope, [], 'head');
    const new_context = new Known_Definition(
        position, 
        Name.make('context', previous_context), 
        new Macro_Context(scope));
    const prog = expand_definition(head_body, new_context.name, new_context);
    head_body.expressions.push(...(prog as Prog_Expression).expressions);
    const body_tail = head_body.expressions[head_body.expressions.length - 1] as Block_Scope;

    const body = parse_body(lexer, indentation, body_tail, true);
    (body_tail as Block_Scope).expressions.push(body as Expression);

    let method_expression = new Method_Expression(
        lexer.position(),
        anyname,
        undefined,
        parameters,
        lookup_known_definition(scope, 'everything') as Datum,
        new Set(),
        head_body as Expression,
    );
    bundle.operator = bundle.operator ? bundle.operator : new Operator_Nature();
    bundle.operator.arity.add('prefix');

    bundle.operator.prefix_expander = method_expression_to_datum(method_expression);

    return expanded_definition as Expression;
}

export function macro_prefix_block(lexer: Lexer, indentation: number, scope: Scope, modifiers: Set<string>, previous_context?: Macro_Context | Module): Expression | Token[] {
    let exit_position: Source_Position | undefined;
    let exit_name: Name | undefined;
    if (lexer.match_keyword('exit')) {
        exit_position = lexer.position();
        exit_name = parse_name(lexer, indentation, scope, true) as Name;
    }
    let body = parse_body(lexer, indentation, scope, true) as Expression;
    if (exit_name && exit_position) {
        const defn = new Known_Definition(exit_position, exit_name, 0);
        const exit_expr = new Exit_Expression(exit_position, exit_name, body);
        const body_head = new Block_Scope(scope, [defn, exit_expr], 'head');
        add_definition(body_head, exit_name, defn);

        defn.value = generate_exit_method(exit_expr, body_head);

        if (body instanceof Block_Scope)
            body.parent = body_head;
        body = body_head;
    }
    return body;
}

export function macro_prefix_for(lexer: Lexer, indentation: number, scope: Scope, modifiers: Set<string>, previous_context?: Macro_Context | Module): Expression | Token[] {
    const $poly = Runtime.instance;

    const preludes: Token[] = [];
    const formals: Token[] = [];
    const initials: Token[] = [];
    const repeats: Token[] = [];
    const prefixes: Token[] = [];
    const macros: Token[] = [];
    const lhss: Expression[] = [];
    let collector_prelude: Token | false = false;
    let collector_postlude: Token | false = new Quotation(false);
    const collector_context = new Macro_Context(scope);

    indentation += 2;

    const name = Name.make;
    const nl = (i: number) => new Newline(i); 

    const parse_left_hand_sides = () => {
        do {
            const expr = parse_expression(lexer, indentation, scope, true, 70);
            lhss.push(expr as Expression);
        } while (lexer.match_name(','));
    }
    const parse_emitters = () => {
        do {
            lhss.length = 0;
            parse_left_hand_sides();
            
            const emitter_name = lexer.read(1);
            const [prelude, formal, initial, repeat, prefix] = 
                sequence_to_internal_list($poly.call(
                    source_location_of(lexer), 
                    $poly.lookup('for_emitter'),
                    emitter_name || false,
                    lhss,
                    lexer,
                    indentation,
                    scope));
            preludes.push(...sequence_to_internal_list(prelude) as Token[]);
            formals.push(formal as Token);
            initials.push(initial as Token);
            repeats.push(repeat as Token);
            prefixes.push(...sequence_to_internal_list(prefix) as Token[]);
        } while(lexer.match_name(','))
    }

    const parse_endtests = () => {
        if (lexer.match_name('while')) {
            const test = parse_expression(lexer, indentation, scope, true);
            prefixes.push(name('if'), test as Token, nl(indentation + 2));
            parse_endtests();
        } else if (lexer.match_name('until')) {
            const test = parse_expression(lexer, indentation, scope, true);
            prefixes.push(name('if'), name('not'), test as Token, nl(indentation + 2));
            parse_endtests();
        }
    }

    const parse_collectors = () => {
        const [prelude, postlude, prefix] = sequence_to_internal_list($poly.call(
            source_location_of(lexer), 
            $poly.lookup('for_collector'),
            lexer.read(1) || false,
            collector_context,
            lexer,
            indentation,
            scope));
        if (collector_prelude !== false) {
            if (collector_prelude != prelude || collector_postlude != postlude)
                throw new Parse_Error(lexer, `incompatible collectors cannot be used in the same for statement`);
        } else {
            preludes.push(prelude as Token);
            collector_prelude = prelude as Token;
            collector_postlude = postlude as Token;
        }
        macros.push(prefix as Token);
        if (lexer.match_name(',')) parse_collectors();
    }

    const parse_for_body = () => {
        for (let m of macros) {
            lexer.insert(m as any);
            lexer.insert([nl(indentation)]);
        }
        return parse_body(lexer, indentation, scope, true) as Token;
    }

    const indent_tokens = (tokens: Token[], adjust: number) => {
        for (var i = 0; i < tokens.length; i++) {
            const token = tokens[i];
            if (token instanceof Newline) 
                tokens[i] = new Newline(token.indentation + adjust, token.relative);
        }
    }

    parse_emitters();
    parse_endtests();
    if (lexer.match_name('using')) 
        parse_collectors();
    const body = parse_for_body();

    const buffer: Token[] = [];
    const buffer_push = (...seqs: (Token[] | Token)[]) => {
        for (var i = 0; i < seqs.length; i++) {
            const seq = seqs[i];
            if (Array.isArray(seq)) buffer.push(...seq);
            else buffer.push(seq);
        }
    }
    buffer_push(name('block'), nl(indentation));
    if (preludes.length == 0) 
        preludes.push(new Quotation(false));
    buffer_push(...preludes, nl(indentation));
    buffer_push(name('def'), name('loop'), name('('));
    for (var i = 0; i < formals.length; i++) {
        if (i > 0) buffer_push(name(','));
        buffer_push(formals[i]);
    }
    buffer_push(name(')'), nl(indentation + 2));
        indent_tokens(prefixes, 2);
        indent_tokens(repeats, 2);
        const tail_prefix = prefixes[prefixes.length-1];
        let tail_newline = nl(indentation + 2);
        if (tail_prefix instanceof Newline)
            tail_newline = new Newline(tail_prefix.indentation, tail_prefix.relative);
        buffer_push(...prefixes, body, tail_newline);
        buffer_push(name('loop'), name('('));
        for (var i = 0; i < repeats.length; i++) {
            if (i > 0) buffer_push(name(','));
            buffer_push(repeats[i]);
        }
        buffer_push(name(')'), nl(indentation));
    buffer_push(name('loop'), name('('));
    for (var i = 0; i < initials.length; i++) {
        if (i > 0) buffer_push(name(','));
        buffer_push(initials[i]);
    }
    buffer_push(name(')'), nl(indentation));
    buffer_push(collector_postlude);
    for (var i = 0; i < buffer.length; i++) {
        const token = buffer[i];
        if (token instanceof Newline && token.relative)
            buffer[i] = new Newline(indentation + token.indentation);
    }
    return buffer;
}

export function macro_prefix_if(lexer: Lexer, indentation: number, scope: Scope, modifiers: Set<string>, previous_context?: Macro_Context | Module): Expression | Token[] {
    const test = parse_expression(lexer, indentation, scope, true) as Expression;
    lexer.match_name('then');
    let then_body = parse_body(lexer, indentation, scope, true) as Expression;
    let else_body: Expression = new Quotation(false);

    const newline = lexer.match_newline(indentation, true);
    if (lexer.match_name('else')) {
        else_body = parse_body(lexer, indentation, scope, true) as Expression;
    } else if (newline) {
        lexer.insert([newline])
    }

    return new If_Expression(lexer.position(), test, then_body, else_body);
}

export function macro_prefix_fun(lexer: Lexer, indentation: number, scope: Scope, modifiers: Set<string>, previous_context?: Macro_Context | Module): Expression | Token[] {
    const name = parse_name(lexer, indentation, scope, false);
    lexer.must_match_name('(');
    const method_modifiers = parse_methodmodifiers(lexer, indentation, scope, false);
    const parameters = parse_formalparameters(lexer, indentation, scope, true) as Formal_Parameters;
    lexer.must_match_name(')');

    const result_type = lexer.match_name('=>') ?
        evaluate_type(parse_expression(lexer, indentation, scope, true), scope) :
        lookup_known_definition(scope, 'everything');

    const method = new Method_Expression(
        lexer.position(),
        name,
        undefined,
        parameters,
        result_type as Datum,
        method_modifiers,
        parse_body(lexer, indentation, parameters.scope, true) as Expression);

    return method
}


export function macro_infix_dot(lhs: Expression, lexer: Lexer, indentation: number, scope: Scope, previous_context?: Macro_Context | Module, method_head_flag?: boolean): Expression | Token[] {
    const rhs = parse_name(lexer, indentation, scope, true);
    return new Call_Expression(lexer.position(), 
        Name.make('.'), [lhs, new Quotation(rhs as Name)], false);
}

export function macro_infix_and(lhs: Expression, lexer: Lexer, indentation: number, scope: Scope, previous_context?: Macro_Context | Module, method_head_flag?: boolean): Expression | Token[] {
    const rhs = parse_expression(lexer, indentation, scope, true);
    return new If_Expression(lexer.position(), lhs,
        rhs as Expression, lhs)
}

export function macro_infix_or(lhs: Expression, lexer: Lexer, indentation: number, scope: Scope, previous_context?: Macro_Context | Module, method_head_flag?: boolean): Expression | Token[] {
    const rhs = parse_expression(lexer, indentation, scope, true);
    return new If_Expression(lexer.position(), lhs,
        lhs, rhs as Expression)
}

export function macro_infix_bracket(lhs: Expression, lexer: Lexer, indentation: number, scope: Scope, previous_context?: Macro_Context | Module, method_head_flag?: boolean): Expression | Token[] | Method_Head {
    if (method_head_flag) {
        let lhs_param: Formal_Parameter_Definition | undefined = undefined;
        let parameters_scope = scope;
        if (lhs instanceof Name) {
            lhs_param = new Formal_Parameter_Definition(
                lexer.position(),
                lhs, 
                lookup_known_definition(scope, 'everything') as Datum);
            parameters_scope = new Formal_Parameter_Scope(parameters_scope);
            add_definition(parameters_scope, lhs, lhs_param);
        }
        const parameters = parse_formalparameters(lexer, indentation, parameters_scope, true);
        lexer.must_match_name(']');
        if (lhs_param)
            parameters?.required.unshift(lhs_param);
        let head_name = Name.make('[');
        head_name = parse_methodhead_assigment(
            lexer, indentation, scope, head_name, parameters as Formal_Parameters);
        const head = new Method_Head(
            head_name,
            new Set(),
            parameters as Formal_Parameters,
            lookup_known_definition(scope, 'everything') as Bundle);
        return head;
    }
    const parameters = parse_actualparameters(lexer, indentation, scope, true);
    lexer.must_match_name(']');
    return new Call_Expression(lexer.position(),
        Name.make('['), [lhs, ...parameters], false);
}

export function macro_infix_paren(lhs: Expression, lexer: Lexer, indentation: number, scope: Scope, previous_context?: Macro_Context | Module, method_head_flag?: boolean): Expression | Token[] {
    const parameters = parse_actualparameters(lexer, indentation, scope, true);
    let elipsis_flag = !!lexer.match_name('...');
    lexer.must_match_name(')');
    return new Call_Expression(lexer.position(), lhs, parameters, elipsis_flag);
}

export function macro_infix_assigment(lhs: Expression, lexer: Lexer, indentation: number, scope: Scope, previous_context?: Macro_Context | Module, method_head_flag?: boolean): Expression | Token[] {
    const rhs = parse_expression(lexer, indentation, scope, true);
    if (lhs instanceof Name) {
        return new Assigment_Expression(lexer.position(), lhs, rhs as Expression);    
    }
    if (lhs instanceof Call_Expression && lhs.method instanceof Name) {
        return new Call_Expression(lexer.position(), 
            Name.make(lhs.method.spelling + ":=", lhs.method.context),
            lhs.parameters.concat(rhs as Expression),
            false);
    }
    throw new Error(`invalid left-hand side for assignment`);
}

export function macro_prefix_paren(lexer: Lexer, indentation: number, scope: Scope, modifiers: Set<string>, previous_context?: Macro_Context | Module): Expression | Token[] {
    const expr = parse_expression(lexer, indentation, scope, true);    
    lexer.must_match_name(')');
    return expr as Expression;
}

export function macro_prefix_def(lexer: Lexer, indentation: number, scope: Scope, modifiers: Set<string>, previous_context?: Macro_Context | Module): Expression | Token[] {
    let definition_type: 'unknown' | 'forward' | 'destructing' |'variable' | 'constant' | 'method' = 'unknown';
    const lookahed_buffer: Token[] = [];
    const initial_name = parse_name(lexer, indentation, scope, false);

    const position = lexer.position();
    
    const parse_balanced_stuff = (initiator: Name): boolean => {
        const terminator = Name.same_spelling(initiator, '[') ?
            Name.make(']') : (Name.same_spelling(initiator, '{') ? Name.make('}') : Name.make(')'));
        lookahed_buffer.push(initiator);
        let token = lexer.read(1);
        while (token !== undefined) {
            if (token instanceof Newline && token.indentation <= indentation) {
                lookahed_buffer.push(token);
                return false;
            }
            if (token instanceof Name && 
                (Name.same_spelling(token, '(') ||
                 Name.same_spelling(token, '[') ||
                 Name.same_spelling(token, '{'))) {
                return parse_balanced_stuff(token);
            }
            lookahed_buffer.push(token);
            if (Name.same_spelling(token, terminator)) {
                return true
            }
            token = lexer.read(1);
        }
        return false;
    }

    if (Name.same_spelling(lexer.read(0), initial_name ? Name.make('(') : Name.make('[')) && 
            parse_balanced_stuff(lexer.read(1) as any) &&
            Name.same_spelling(lexer.read(0), '#=')) {
        lexer.insert(lookahed_buffer);
        definition_type = 'destructing';
    } else {
        lexer.insert(lookahed_buffer);
        if (initial_name && lexer.match_name(':=')) {
            definition_type = 'variable';
        } else if (initial_name && lexer.match_name('=')) {
            definition_type = 'constant';
        } else if (initial_name && !Name.same_spelling(lexer.read(0), '(') &&  !Name.same_spelling(lexer.read(0), '.')) {
            const token = lexer.read(0);
            if (!token || token instanceof Newline && token.indentation <= indentation ||
                    Name.same_spelling(token, ')')) {
                definition_type = 'forward';
            } else {
                throw new Parse_Error(lexer, 'expected ) or end of statement');
            }
        } else {
            definition_type = 'method';
        }
    }

    const safe_name = initial_name as Name;
    let defn: Definition | undefined = undefined;

    switch (definition_type) {
    case 'forward': {
        defn = new Known_Definition(position, safe_name, new Bundle(initial_name));
    }    
    break;
    case 'variable': {
        const initial_value = parse_expression(lexer, indentation, scope, true);
        const type = evaluate_type(parse_expression(lexer, indentation, scope, false), scope);
        defn = new Variable_Definition(position, safe_name, type, initial_value as any);
    }
    break;
    case 'constant': {
        const expr = parse_expression(lexer, indentation, scope, true);
        if (typeof expr == 'number' || typeof expr == 'string' || expr instanceof Char) {
            defn = new Known_Definition(position, safe_name, expr);
        } else if (expr instanceof Quotation) {
            defn = new Known_Definition(position, safe_name, expr.datum);
        } else if (expr instanceof Name && lookup_known_definition(scope, expr)) {
            defn = new Known_Definition(position, safe_name, lookup_known_definition(scope, expr) as any);
        } else {
            defn = new Constant_Definition(position, safe_name, lookup_known_definition(scope, 'everything') as any, expr as any);
        }
    }
    break;
    case 'destructing': {
        throw new Error('TODO');
    }
    break;
    case 'method': {
        const head = initial_name ?
            parse_methodhead_after_name(lexer, indentation, scope, initial_name) as Method_Head :
            parse_methodhead(lexer, indentation, scope, true) as Method_Head;
        const body_scope = head.formal_parameters.scope;
        const function_name = head.name;
        const existing_definition = lookup(scope, function_name);
        for (let mod of modifiers) {
            // TODO check if modifier applicable
            head.modifiers.add(mod as any);
        }
        if (existing_definition) {
            if (existing_definition instanceof Known_Definition && existing_definition.value instanceof Bundle) {
                const bundle = existing_definition.value as Bundle;
                const method_expression = new Method_Expression(
                    lexer.position(),
                    head.name,
                    head.generic_parameters,
                    head.formal_parameters,
                    head.result_type,
                    head.modifiers,
                    parse_body(lexer, indentation, body_scope, true) as Expression);
                add_method_expression(bundle, method_expression);
                return head.name;
            }
            throw new Error('incompatible definitions');
        }
        const bundle = new Bundle(function_name);
        const defn = new Known_Definition(position, function_name, bundle);
        const expr = expand_definition(scope, function_name, defn);
        
        let new_scope = scope;
        if (scope.parent && expr instanceof Prog_Expression) {
            new_scope = expr.expressions[expr.expressions.length - 1] as Block_Scope;
        }
        let _scope: Scope | undefined = body_scope;
        while(_scope) {
            if (_scope.parent == scope) {
                _scope.parent = new_scope;
                break;
            }
            _scope = _scope.parent;
        }

        const method_expression = new Method_Expression(
            position,
            head.name,
            head.generic_parameters,
            head.formal_parameters,
            head.result_type,
            head.modifiers,
            parse_body(lexer, indentation, body_scope, true) as Expression);
        bundle.function = new Function_Nature();
        add_method_expression(bundle, method_expression);
        
        if (expr instanceof Prog_Expression) {
            return expr;
        }
        return head.name;
    }
    break;
    }
    return expand_definition(scope, initial_name as Name, defn);
}

export function parse_superclass_expression(lexer: Lexer, indentation: number, scope: Scope, required: boolean) {
    const class_name = parse_name(lexer, indentation, scope, required) as Name;
    if (!class_name && !required) {
        return undefined;
    }
    let generic_parameters: Expression[] | undefined;
    if (lexer.match_name('[')) {
        generic_parameters = parse_actualparameters(lexer, indentation, scope, true);
        lexer.must_match_name(']')
    }
    let constructor_parameters: Expression[] = [];
    let spread = false;
    if (lexer.match_name('(')) {
        constructor_parameters = parse_actualparameters(lexer, indentation, scope, false);
        spread = !!lexer.match_name('...');
        lexer.must_match_name(')');
    }
    return new Superclass_Expression(lexer.position(),
        class_name, constructor_parameters, generic_parameters, spread);
}

export function macro_prefix_defclass(lexer: Lexer, indentation: number, scope: Scope, modifiers: Set<string>, previous_context?: Macro_Context | Module): Expression | Token[] {
    const bdef = new _Batch_Definer(lexer.position());
    const $poly = Runtime.instance;

    //
    // parse class_name
    //
    const class_name = parse_name(lexer, indentation, scope, true) as Name;
    
    let generic_formal_parameters: Formal_Parameters | undefined = undefined;
    if (lexer.match_name('[')) {
        generic_formal_parameters = parse_formalparameters(lexer, indentation, scope, true);
        lexer.must_match_name(']');
    }
    const generic_parameter_scope = generic_formal_parameters ?
        Generic_Parameter_Scope.from_formal(generic_formal_parameters, scope) : undefined;
    
    // 
    // parse constructor_name
    //
    let constructor_name = class_name;
    if (lexer.match_keyword('constructor')) {
        constructor_name = parse_name(lexer, indentation, scope, true) as Name;
    }

    // 
    // parse constructor formalparameters
    //
    let constructor_formal_parameters: Formal_Parameters | undefined = undefined;
    const constructor_scope = generic_parameter_scope ?
        generic_parameter_scope: scope;
    if (lexer.match_name('(')) {
        constructor_formal_parameters = parse_formalparameters(lexer, indentation, constructor_scope, false)
        lexer.must_match_name(')');
    }
    if (!constructor_formal_parameters) {
        constructor_formal_parameters = new Formal_Parameters(constructor_scope);
    }

    //
    // parse superclass_expressions
    //
    const superclass_expressions: Superclass_Expression[] = [];
    do {
        const superclass = parse_superclass_expression(
            lexer, indentation, constructor_formal_parameters.scope, 
            superclass_expressions.length != 0);
        if (!superclass) {
            break;
        }
        superclass_expressions.push(superclass as Superclass_Expression);
    } while(lexer.match_name(','));

    //
    // forward definition
    //
    const class_bundle = bdef.lookup_nothing_or_assert_bundle(class_name, scope) ||
        bdef.define_bundle(lexer.position(), scope, class_name);

    //
    // parse slot_specifiers, slot_assigments
    //
    const slot_specifiers: Slot_Specifier[] = [];
    const slot_assigments: Assigment_Expression[] = [];
    let length_expression: Expression | undefined;

    const body_scope = constructor_formal_parameters.scope;
    const body_newline = lexer.match_newline(indentation + 1, true);
    const body_indent = body_newline?.indentation || 0;
    while(body_newline) {
        const slot_name = parse_name(lexer, body_indent, body_scope, true) as Name;
        let is_constant = false;
        let is_multislot = false;
        if (lexer.match_name('[')) {
            if (length_expression !== undefined) {
                throw new Error(`class cannot have more than 1 multislot`);
            }
            length_expression = parse_expression(lexer, body_indent, body_scope, true);
            is_multislot = true;
            lexer.match_name(']')
        }

        if (lexer.match_name('=')) is_constant = true;
        else  lexer.must_match_name(':=');

        const inital_value = parse_expression(lexer, body_indent, body_scope, true) as Expression;
        const type_expression = parse_expression(lexer, body_indent, body_scope, false);
        let type = lookup_known_definition(scope, 'everything') as Datum;
        if (type_expression) type = evaluate_type(type_expression, body_scope);
        else if (inital_value instanceof Name) {
            const defn = lookup(body_scope, inital_value);            
            if (defn instanceof Formal_Parameter_Definition)
                type = defn.type;
        }

        let reader_name = Name.make('.')
        let writer_name = is_constant ? undefined : Name.make('.:=')
        if (lexer.match_keyword('reader')) {
            reader_name = parse_name(lexer, body_indent, body_scope, true) as Name;
        }
        if (lexer.match_keyword('writer')) {
            if (is_constant) {
                throw new Error(`slot which declared as constant cannot have writer`);
            }
            writer_name = parse_name(lexer, body_indent, body_scope, true) as Name;
        }

        const multislot_type = (elem: Type) =>
            elem instanceof Unresolved_Type ?
                new Unresolved_Type(
                    new Call_Expression(lexer.position(), Name.make('['), 
                    [Name.make('internal_array'), elem.expression], false),
                    elem.context) :
                instantiate_generic_bundle($poly.lookup('internal_array'), [elem]) as Bundle
        
        const specifier = new Slot_Specifier(
            slot_name, is_multislot ? multislot_type(type) : type, class_bundle,
            reader_name, writer_name, is_multislot);
        const assigment = new Assigment_Expression(
            lexer.position(), slot_name, inital_value);
        slot_specifiers.push(specifier);
        slot_assigments.push(assigment);

        if (!lexer.match_newline(body_indent, false))
            break;
    }
    if (!body_newline && constructor_formal_parameters) {
        const formal = constructor_formal_parameters;
        if (formal.optional.length > 0 || formal.named.length > 0) {
            throw new Error(`construtor of simple class cannot accept optional or named parameters!`);
        }
        for (let p of formal.required) {
            const writer_name = !modifiers.has('constant') ? Name.make('.:=') : undefined;
            const specifier = new Slot_Specifier(
                p.name, p.type, class_bundle,
                Name.make('.'), writer_name);
            const assigment = new Assigment_Expression(
                lexer.position(), p.name, p.name);
            slot_specifiers.push(specifier);
            slot_assigments.push(assigment);
        }
    }

    const class_modifiers: Set<Class_Modifier> = new Set();
    const possible_class_modifiers: Class_Modifier[] = [
        'abstract',
        'intrinsic',
        'sealed',
        'autothrow',
        'noreturn',
    ];
    for (let modifier of possible_class_modifiers) {
        if (!modifiers.has(modifier)) {
            continue;
        }
        class_modifiers.add(modifier);
    }
    if (generic_formal_parameters) class_modifiers.add('generic');

    const class_id = $poly.class_index++;
    const class_expression = new Class_Expression(
        lexer.position(),
        class_id,
        constructor_name,
        constructor_formal_parameters,
        generic_formal_parameters,
        slot_assigments,
        superclass_expressions,
        length_expression);
    $poly.class_expressions[class_id] = class_expression;

    const superclasses = evaluate_class_superclasses(class_expression);
    const nature = new Class_Nature(
        class_id,
        constructor_name,
        superclasses,
        slot_specifiers,
        class_modifiers as Set<Class_Modifier>);
    class_bundle.class = nature;
    nature.slots = combine_slots(superclasses.concat(class_bundle));

    // generation of class constructor code
    if (!nature.abstract && !generic_formal_parameters) {
        const class_constructor_method = generate_class_constructor_method(
            class_bundle, class_expression, scope);
        const class_constructor = bdef.lookup_nothing_or_assert_bundle(constructor_name, scope) ||
            bdef.define_bundle(class_expression.position, scope, constructor_name);
        add_method_expression(class_constructor, class_constructor_method);    
    }
    if (generic_formal_parameters) {
        const constructor_bundle = bdef.lookup_nothing_or_assert_bundle(constructor_name, scope) ||
            bdef.define_bundle(class_expression.position, scope, constructor_name);

        const lbr = bdef.lookup_nothing_or_assert_bundle(Name.make('['), scope) as Bundle;
        const makers = $poly.generic_class_instance_makers;

        if (!makers.has(class_bundle)) {
            makers.set(class_bundle, new Generic_Class_Instance_Maker(class_bundle));
            const method_expr = generate_class_generic_instance_maker_method(
                class_bundle, class_expression.position, generic_formal_parameters, scope) as Method_Expression;
            add_method_expression(lbr, method_expr);
        }
        const instance_maker = makers.get(class_bundle) as Generic_Class_Instance_Maker;
        instance_maker.class_maker = class_bundle;

        if (!nature.abstract) {
            if (constructor_name != class_name) {
                if (!makers.has(constructor_bundle)) {
                    makers.set(constructor_bundle, new Generic_Class_Instance_Maker(undefined, class_bundle));
                    const method_expr = generate_class_generic_instance_maker_method(
                        constructor_bundle, class_expression.position, generic_formal_parameters, scope) as Method_Expression;
                    add_method_expression(lbr, method_expr);
                }
                const instance_constructor_maker = makers.get(constructor_bundle) as Generic_Class_Instance_Maker;
                instance_constructor_maker.constructor_maker = class_bundle;
            } else instance_maker.constructor_maker = class_bundle;
        }
    }
    define_class_slot_operations(bdef, class_bundle, class_expression, scope);
    return bdef.definitions;
}

class _Template_Element {
    position: Source_Position;

    constructor(position: Source_Position) {
        this.position = position;
    }

    compile(): Expression { return 0; }
    indentation(): number { return 0; }
}

class _Template_Token_Name_In_Context extends _Template_Element {
    name: Name;
    context: Name;

    constructor(position: Source_Position, name: Name, context: Name) {
        super(position);
        this.name = name;
        this.context = context;
    }

    compile(): Expression {
        return new Call_Expression(
            this.position, 
            Name.make('name'), 
            [this.name.spelling, this.context], false);
    }
}

class _Template_Token_Sequence extends _Template_Element {
    tokens: Token[];

    constructor(position: Source_Position, tokens: Token[]) {
        super(position);
        this.tokens = tokens;
    }

    compile(): Expression {
        return new Quotation(this.tokens);
    }
}

class _Template_Name_Interpolation extends _Template_Element {
    name: Name;
    _indentation: number;

    constructor(position: Source_Position, indentation: number, name: Name) {
        super(position);
        this.name = name;
        this._indentation = indentation;
    }

    compile(): Expression { return this.name; }
    indentation(): number { return this._indentation; }
}

class _Template_Builder {
    indentation: number;
    elements: (_Template_Element | Token)[];
    buffer: Name;
    parent?: _Template_Builder;

    constructor(indentation: number, scope: Scope, parent?: _Template_Builder) {
        this.indentation = indentation;
        if (!parent) {
            const context = new Macro_Context(scope);
            this.buffer = Name.make('buffer', context);
            this.elements = [
                'def', this.buffer, '=', 'internal_list', '(', ')', 
                new Newline(indentation),
            ].map(e => typeof e == 'string' ? Name.make(e) : e);
        } else  {
            this.buffer = parent.buffer;
            this.parent = parent;
            this.elements = [];
        }
    }

    push_element(element: _Template_Element) {
        const last = this.elements[this.elements.length - 1];
        if (element instanceof _Template_Token_Sequence && last instanceof _Template_Token_Sequence) {
            last.tokens.push(...element.tokens);
            return;
        }
        this.elements.push(element);
    }

    push_tokens(...tokens: Token[]) {
        this.elements.push(...tokens)
    }

    compile(): Token[] {
        const tokens: Token[] = [];
        for (let element of this.elements) {
            if (!(element instanceof _Template_Element)) {
                tokens.push(element);
                continue;
            }
            const compiled = element.compile();
            const call_expression = new Call_Expression(
                element.position,
                Name.make('append_token_sequence!'),
                [this.buffer, element.indentation(), compiled as Expression], 
                    compiled instanceof Quotation && Array.isArray(compiled.datum));
            tokens.push(call_expression, new Newline(this.indentation));
        }
        if (!this.parent) {
            tokens.push(this.buffer);
        }
        return tokens;
    }
}

export function internal_list_append_token_sequence(list: Datum[], indentation: number, tok: Datum) {
    if (!(tok instanceof Compound_Expression) && is_sequence(tok)) {
        const elems = sequence_to_internal_list(tok);
        for (let e of elems) internal_list_append_token_sequence(list, indentation, e);
        return;
    }
    if (tok instanceof Newline && indentation != 0)
        tok = new Newline(tok.indentation + indentation, tok.relative);
    list.push(tok);
}   

export function macro_prefix_template(lexer: Lexer, indentation: number, scope: Scope, modifiers: Set<string>, previous_context?: Macro_Context | Module): Expression | Token[] {
    const relative_indentation = lexer.position().colon;
    let   interpolation_indentation = 0;
    const body_indentation = indentation + 2; // everything will be nested in \block macro

    const parent_context_name = Name.make('context', previous_context);
    let own_context: Macro_Context | undefined = undefined;
    if (lookup(scope, parent_context_name) === undefined) 
        own_context = new Macro_Context(scope);
    
    const builder = new _Template_Builder(body_indentation, scope);
    const token_sequence = (...tokens: Token[]) => new _Template_Token_Sequence(lexer.position(), tokens);
    const token_name_interpolation = (name: Name) => new _Template_Name_Interpolation(lexer.position(), interpolation_indentation, name);
    const token_name_in_context = (name: Name) => own_context ? 
        token_sequence(Name.make(name, own_context)) :
        new _Template_Token_Name_In_Context(lexer.position(), name, parent_context_name);
    const push_tokens = (builder: _Template_Builder, ...tokens: (string | Token)[]) =>
        builder.push_tokens(...tokens.map(token => typeof token == 'string' ? Name.make(token) : token));
    
    const match_simple_token = (builder: _Template_Builder) => {
        if (lexer.match_name('\\')) {
            const name = parse_denatured_name(lexer);
            builder.push_element(token_sequence(name));
            return;
        }
        if (lexer.read(0) instanceof Name) {
            const name = lexer.read(1) as Name;
            if (!name.context)
                builder.push_element(token_name_in_context(name));  
            else builder.push_element(token_sequence(name));
            return;  
        }
        if (lexer.read(0) instanceof Newline) {
            const newline = lexer.read(1) as Newline;
            let   indentation = newline.indentation - relative_indentation;
            indentation = indentation >= 0 ? indentation : 0;
            
            const adjusted_newline = new Newline(indentation, true);
            interpolation_indentation = indentation;
            builder.push_element(token_sequence(adjusted_newline));

            return;
        }
        builder.push_element(token_sequence(lexer.read(1) as Token)); 
    }

    while(lexer.read(0) !== undefined) {
        if (lexer.match_name('`')) {
            break;
        }
        if (!lexer.match_name('$')) {
            match_simple_token(builder);
            continue;
        }
        if (!lexer.match_name('{')) {
            const token = lexer.read(0);
            if (token instanceof Name) {
                lexer.read(1);
                builder.push_element(token_name_interpolation(token));
            }
            continue;
        }

        const spacing0 = new Newline(body_indentation);
        const spacing1 = new Newline(body_indentation + 2);
        const spacing2 = new Newline(body_indentation + 4);
        const spacing3 = new Newline(body_indentation + 6);

        const builder0 = new _Template_Builder(body_indentation + 4, scope, builder);
        const builder1 = new _Template_Builder(body_indentation + 6, scope, builder);

        let sub_builder = builder0;
        while (lexer.read(0) !== undefined) {
            if (lexer.match_name('}')) {
                break;
            }
            if (lexer.match_name('&')) {
                sub_builder = builder1;
                continue;
            }
            if (lexer.match_name('$')) {
                const token = lexer.read(0);
                if (token instanceof Name) {
                    lexer.read(1);
                    sub_builder.push_element(token_name_interpolation(token));
                }
                continue
            }
            match_simple_token(sub_builder); 
        }
        const names: _Template_Name_Interpolation[] = [];
        const collect_names = (builder: _Template_Builder) => {
            for (let element of builder.elements) {
                if (!(element instanceof _Template_Name_Interpolation)) {
                    continue;
                }
                names.push(element);
            }
        }

        const context = new Macro_Context(scope);
        const sequences_buffer = Name.make('sequences', context);
        const iterator_buffer = Name.make('iterators', context);
        collect_names(builder0);
        collect_names(builder1);
        push_tokens(builder, 'block', spacing1)
        push_tokens(builder, 
            'def', sequences_buffer, '=', 'internal_list', '(', ')', spacing1);
        push_tokens(builder, 
            'def', iterator_buffer, '=', 'internal_list', '(', ')', spacing1);
        for (let name of names) {
            push_tokens(builder, 'if', name.name, 'in', 'sequence', spacing2, 
                'append!', '(', sequences_buffer, ',', name.name, ')', spacing2,
                'append!', '(', iterator_buffer, ',', 'iterate', '(', name.name, ')', ')', spacing1);
        }
        const have_more = Name.make('have_more', context);
        const iterate = Name.make('iterate_all', context);
        push_tokens(builder,
            'def', have_more, '(', ')', spacing2,
                'def', 'i', ':=', 0, spacing2,
                'def', 'more', ':=', 'false', spacing2,
                'while', 'i', '<', sequences_buffer, '.', 'length', spacing3,
                    'if', 'more?', '(', sequences_buffer, '[', 'i', ']', ',', iterator_buffer, '[', 'i', ']', ')',
                        'then', 'more', ':=', 'true', spacing3,
                    'i', ':=', 'i', '+', 1, spacing2,
                'more', spacing1);
        push_tokens(builder,
            'def', iterate, '(', ')', spacing2,
                'def', 'i', ':=', 0, spacing2,
                'while', 'i', '<', sequences_buffer, '.', 'length', spacing3,
                    iterator_buffer, '[', 'i', ']', ':=', 'iterate', '(', 
                        sequences_buffer, '[', 'i', ']', 
                        ',', 
                        iterator_buffer, '[', 'i', ']', 
                    ')', spacing3,
                    'i', ':=', 'i', '+', 1, spacing1);
        push_tokens(builder, 'def', 'insertion_index', ':=', 0, spacing1);
        push_tokens(builder, 'while', have_more, '(', ')', spacing2,
            'def', 'seq_index', ':=', -1, spacing2);
        const name_context = new Macro_Context(scope);
        for (let name of names) {
            const original_name = name.name;
            name.name = Name.make(original_name, name_context);
            push_tokens(builder, 
            'def', name.name, '=', 'if', original_name, 'in', 'sequence', spacing3,
                'seq_index', ':=', 'seq_index', '+', 1, spacing3,
                'next', '(', sequences_buffer, '[', 'seq_index', ']', ',', 
                    iterator_buffer, '[', 'seq_index', ']', ')', spacing2,
                'else', original_name, spacing2);
        }
        push_tokens(builder, 'if', 'insertion_index', '>', 0, spacing3);
            push_tokens(builder, ...builder1.compile());
            push_tokens(builder, 'false', spacing2);
        push_tokens(builder, ...builder0.compile());
        push_tokens(builder,
            'insertion_index', ':=', 'insertion_index', '+', 1, spacing2,
            iterate, '(', ')', spacing0);
    }
    const compiled = builder.compile();
    const result = [Name.make('block'), new Newline(body_indentation), ...compiled];
    return result;
}
