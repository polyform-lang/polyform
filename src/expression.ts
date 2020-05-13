import { Source_Position, Lexer, is_punctuation, Keyword, Newline, Parse_Error, Token, Poly_Error } from "./token";
import { Datum, Char, Bundle, Name, Macro_Context, Host_Datum, Host_Datum_Spec, Operator_Nature, Function_Nature, Internal_Array, Type_Union, Type_Intersection } from "./datum";
import { Runtime } from "./js_runtime";
import { method_expression_to_datum, add_method, add_method_expression, Runtime_Method_Datum, Method_Environment } from "./method";
import { is_subtype_or_equal, classof } from "./class";
import { eval_expression } from "./eval";

export const Scope_datum_spec = new Host_Datum_Spec(
    'scope', []);

export class Scope extends Host_Datum {
    parent: Scope | undefined;
    readonly definitions: Map<Name, Definition>;

    constructor(parent?: Scope, spec?: Host_Datum_Spec) {
        super(spec ? spec : Scope_datum_spec);
        this.parent = parent;
        this.definitions = new Map();
    }

    root(): Scope {
        if (!this.parent) {
            return this;
        }
        return this.parent.root();
    }
}

export function add_definition(scope: Scope, name: Name, definition: Definition): Name {
    if (name.context instanceof Module && scope != name.context) {
        if (scope.parent) {
            throw new Error(`module declaration must be done in global scope`);
        }
        return add_definition(name.context, name, definition);
    }
    if (scope.definitions.has(name)) {
        throw new Error(`name '${name.spelling}' already declared in scope`);
    }
    if (scope instanceof Module && name.context) {
        name = Name.make(name);
    }
    scope.definitions.set(name, definition);
    return name;
}   

export function expand_definition(scope: Scope, name: Name, definition: Definition): Prog_Expression | Definition {
    if (name.context instanceof Module) {
        if (scope.parent) {
            throw new Error(`module declaration must be done in global scope`);
        }
        if (scope == name.context) {
            add_definition(scope, name, definition);
            return definition;
        }
        return expand_definition(name.context, name, definition);
    }
    if (scope instanceof Block_Scope) {
        const tail: Block_Scope = new Block_Scope(scope, [], 'tail');
        add_definition(tail, name, definition);
        return new Prog_Expression(definition.position, [definition, tail]);
    }
    add_definition(scope, name, definition);
    return definition;
}

export function lookup(scope: Scope, name: Name): Definition | undefined {
    if (name.context instanceof Module && scope != name.context) 
        return lookup(name.context, Name.make(name));

    const local = scope.definitions.get(name);
    if (local !== undefined) 
        return local;
    if (scope.parent) 
        return lookup(scope.parent, name);
    if (name.context instanceof Macro_Context)
        return lookup(name.context.parent_scope, Name.make(name));

    return scope instanceof Module ? scope.search_imports(name) : undefined;
}

export function lookup_known_definition(scope: Scope, name: Name | string): Datum | undefined {
    const defn = lookup(scope, name instanceof Name ? name : Name.make(name));
    return defn && defn instanceof Known_Definition ? defn.value : undefined;
}

export class Module_Import {
    readonly module: Module;
    readonly pattern: Name | string;

    constructor(module: Module, pattern: Name | string) {
        this.module = module;
        this.pattern = pattern;
    }
}

export function asterisk_match(value: string, pattern: string): boolean {
    const expr = new RegExp(pattern.replace('*', '.*'));
    return expr.test(value);
}

export const Module_datum_spec = new Host_Datum_Spec(
    'module', []);

export class Module extends Scope {
    readonly name: Name;
    readonly imports: Module_Import[] = [];
    readonly exports: Name[] = [];
    readonly locals: (Name | string)[] = [];

    search_imports(n: Name) {
        if (!this.importable(n)) {
            return undefined;
        }
        for (let spec of this.imports) {
            if (n.equal(spec.pattern)) {
                return lookup(spec.module, n);
            } else if (typeof spec.pattern == 'string' && asterisk_match(n.spelling, spec.pattern)) {
                // TODO exports check
                return lookup(spec.module, n);
            }
        }
        return undefined;
    }

    importable(n: Name): boolean {
        for (let local of this.locals) {
            if (n.equal(local)) {
                return false;
            }
            if (typeof local == 'string') {
                if (asterisk_match(n.spelling, local)) {
                    return false;
                }
            }
        }
        return true;
    }

    lookup(name: Name): Definition | undefined {
        return lookup(this, name);
    }

    constructor(name: Name) {
        super();
        this.name = name;
    }
}

export const Block_Scope_datum_spec = new Host_Datum_Spec(
    'block_scope', [])

export class Block_Scope extends Scope {
    expressions: Expression[];
    readonly type?: 'head' | 'tail';

    constructor(parent: Scope, expressions?: Expression[], type?: 'head' | 'tail') {
        super(parent, Block_Scope_datum_spec);
        if (type) {
            this.type = type;
        }
        this.expressions = expressions ? expressions : [];
    }
    
    datumclass(): Bundle | string {
        if (!this.type) {
            return 'block_scope';
        }
        return this.type == 'head' ? 'block_head_scope' : 'block_tail_scope';
    }
}

type Literal = number | string | Char;
export type Expression = Name | Literal | Quotation | Compound_Expression | Block_Scope | Generic_Parameter_Scope;

export const Quotation_datum_spec = new Host_Datum_Spec(
    'quotation', [
        [Name.make('datum'), 'datum'],
    ]);

export class Quotation extends Host_Datum {
    readonly datum: Datum;

    constructor(datum: Datum) {
        super(Quotation_datum_spec);
        this.datum = datum;
    }
}

export class Compound_Expression extends Host_Datum {
    position: Source_Position;
    
    constructor(position: Source_Position, datum_spec: Host_Datum_Spec) {
        super(datum_spec);
        this.position = position;
    }
}

export const Call_Expression_datum_spec = new Host_Datum_Spec(
    'call_expression', [])

export class Call_Expression extends Compound_Expression {
    method: Expression;
    parameters: Expression[];
    spread: boolean;

    constructor(
        position: Source_Position, 
        method: Expression, 
        parameters: Expression[],
        spread: boolean,
    ) {
        super(position, Call_Expression_datum_spec);
        this.method = method;
        this.parameters = parameters;
        this.spread = spread;
    }
}

export const Prog_Expression_datum_spec = new Host_Datum_Spec(
    'prog_expression', []);

export class Prog_Expression extends Compound_Expression {
    expressions: Expression[];

    constructor(position: Source_Position, expressions: Expression[]) {
        super(position, Prog_Expression_datum_spec);
        this.expressions = expressions;
    }
}

export const Assigment_Expression_datum_spec = new Host_Datum_Spec(
    'assigment_expression', []);

export class Assigment_Expression extends Compound_Expression {
    lhs: Name;
    rhs: Expression;

    constructor(position: Source_Position, lhs: Name, rhs: Expression) {
        super(position, Assigment_Expression_datum_spec);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

export const If_Expression_datum_spec = new Host_Datum_Spec(
    'if_expression', []);

export class If_Expression extends Compound_Expression {
    test: Expression;
    consequent: Expression;
    alternate: Expression;

    constructor(
        position: Source_Position, 
        test: Expression, 
        consequent: Expression, alternate: Expression,
    ) {
        super(position, If_Expression_datum_spec);
        this.test = test;
        this.consequent = consequent;
        this.alternate = alternate;
    }
}

export const Definition_datum_spec = new Host_Datum_Spec(
    'definition', []);

export class Definition extends Compound_Expression {
    constructor(position: Source_Position, datum_spec?: Host_Datum_Spec) {
        super(position, datum_spec ? datum_spec: Definition_datum_spec);
    }

    assignable(): boolean { return false; }
    have_expression(): boolean { return false; }
}

export const Known_Definition_datum_spec = new Host_Datum_Spec(
    'known_definition', []);

export class Known_Definition extends Definition {
    readonly name: Name;
    value: Datum;

    constructor(position: Source_Position, name: Name, value: Datum) {
        super(position, Known_Definition_datum_spec);
        this.name = name;
        this.value = value;
    }
}

export const Constant_Definition_datum_spec = new Host_Datum_Spec(
    'constant_definition', []);

export class Constant_Definition extends Definition {
    readonly name: Name;
    type: Datum;
    expression: Expression;
    value?: Datum;

    constructor(position: Source_Position, name: Name, type: Datum, expression: Expression) {
        super(position, Constant_Definition_datum_spec);
        this.name = name;
        this.type = type;
        this.expression = expression;
    }

    have_expression(): boolean { return true; }
}

export const Variable_Definition_datum_spec = new Host_Datum_Spec(
    'variable_definition', []);

export class Variable_Definition extends Definition {
    readonly name: Name;
    type: Datum;
    expression: Expression;
    value?: Datum;

    constructor(position: Source_Position, name: Name, type: Datum, expression: Expression) {
        super(position, Variable_Definition_datum_spec);
        this.name = name;
        this.type = type;
        this.expression = expression;
    }

    assignable(): boolean { return true; }
    have_expression(): boolean { return true; }
}

export const Formal_Parameter_Definition_datum_spec = new Host_Datum_Spec(
    'formal_parameter_definition', []);

export class Formal_Parameter_Definition extends Definition {
    name: Name;
    type: Datum;
    default_expression?: Expression;
    scope_for_default_expression?: Scope;
    selector?: Name;

    constructor(
        position: Source_Position,
        name: Name,
        type: Datum,
        default_expression?: Expression,
        scope_for_default_expression?: Scope,
        selector?: Name,
    ) {
        super(position, Formal_Parameter_Definition_datum_spec);
        this.name = name;
        this.type = type;
        if (default_expression) this.default_expression = default_expression;
        if (scope_for_default_expression) this.scope_for_default_expression = scope_for_default_expression;
        if (selector) this.selector = selector;
    }
}

export type Method_Modifiers = 'sealed' | 'intrinsic' | 'dominant';

export const Method_Expression_datum_spec = new Host_Datum_Spec(
    'method_expression', []);

export class Method_Expression extends Compound_Expression {
    readonly name: Name | undefined;
    generic_parameters?: Name[];
    formal_parameters: Formal_Parameters;
    result_type: Datum;
    readonly modifiers: Set<Method_Modifiers>;
    body: Expression;

    constructor(
        position: Source_Position,
        name: Name | undefined,
        generic_parameters: Name[] | undefined,
        formal_parameters: Formal_Parameters,
        result_type: Datum,
        modifiers: Set<Method_Modifiers>,
        body: Expression,
    ) {
        super(position, Method_Expression_datum_spec);
        this.name = name;
        if (generic_parameters)
            this.generic_parameters = generic_parameters;
        this.formal_parameters = formal_parameters;
        this.result_type = result_type;
        this.modifiers = modifiers;
        this.body = body;
    }
}

export const Exit_Expression_datum_spec = new Host_Datum_Spec(
    'exit_expression', []);

export class Exit_Expression extends Compound_Expression {
    name: Name;
    expression: Expression;

    constructor(position: Source_Position, name: Name, expression: Expression) {
        super(position, Exit_Expression_datum_spec);
        this.name = name;
        this.expression = expression;
    }
}

export const Exit_Call_Expression_datum_spec = new Host_Datum_Spec(
    'exit_call_expression', []);

export class Exit_Call_Expression extends Compound_Expression {
    exit: Exit_Expression;
    expression: Expression;

    constructor(position: Source_Position, exit: Exit_Expression, expression: Expression) {
        super(position, Exit_Call_Expression_datum_spec);
        this.exit = exit;
        this.expression = expression;
    }
}

export function generate_exit_method(exit: Exit_Expression, scope: Scope) {
    const $poly = Runtime.instance;

    const param = new Formal_Parameter_Definition(
        exit.position,
        Name.make('value'),
        $poly.lookup('everything'));
    const param_scope = new Formal_Parameter_Scope(scope);
    add_definition(param_scope, Name.make('value'), param);
    const formal = new Formal_Parameters(param_scope);
    formal.required.push(param);

    const body = new Exit_Call_Expression(
        exit.position, 
        exit, 
        Name.make('value'));
    const exit_method = new Method_Expression(
        exit.position,
        exit.name,
        undefined,
        formal,
        $poly.lookup('everything'),
        new Set(),
        body);
    return exit_method;
}

export const Instance_Expression_datum_spec = new Host_Datum_Spec(
    'instance_expression', []);

export class Instance_Expression extends Compound_Expression {
    readonly bundle: Bundle;
    expressions: Expression[];

    constructor(position: Source_Position, bundle: Bundle, expressions: Expression[]) {
        super(position, Instance_Expression_datum_spec);
        this.bundle = bundle;
        this.expressions = expressions;    
    }
}

export const Slot_Read_Expression_datum_spec = new Host_Datum_Spec(
    'slot_read_expression', []);


export class Slot_Read_Expression extends Compound_Expression {
    bundle: Bundle;
    lhs: Expression;
    readonly slot: Name;

    constructor(position: Source_Position, bundle: Bundle, lhs: Expression, slot: Name) {
        super(position, Slot_Read_Expression_datum_spec);
        this.bundle = bundle;
        this.lhs = lhs;
        this.slot = slot;
    }
}

export const Slot_Write_Expression_datum_spec = new Host_Datum_Spec(
    'slot_write_expression', []);


export class Slot_Write_Expression extends Compound_Expression {
    bundle: Bundle;
    lhs: Expression;
    rhs: Expression;
    readonly slot: Name;

    constructor(position: Source_Position, bundle: Bundle, lhs: Expression, slot: Name, rhs: Expression) {
        super(position, Slot_Read_Expression_datum_spec);
        this.bundle = bundle;
        this.lhs = lhs;
        this.slot = slot;
        this.rhs = rhs;
    }
}

export const Formal_Parameters_datum_spec = new Host_Datum_Spec(
    'formal_parameters', []);

export class Formal_Parameters extends Host_Datum {
    required: Formal_Parameter_Definition[];
    optional: Formal_Parameter_Definition[];
    named: Formal_Parameter_Definition[];
    rest?: Formal_Parameter_Definition;
    scope: Scope;

    constructor(scope: Scope) {
        super(Formal_Parameters_datum_spec);
        this.required = [];
        this.optional = [];
        this.named = [];
        this.scope = scope;
    } 

    get have_parameters() {
        if (this.required.length > 0) return true;
        if (this.optional.length > 0) return true;
        if (this.named.length > 0) return true;
        return !!this.rest;
    }
}

export const Formal_Parameter_Scope_datum_spec = new Host_Datum_Spec(
    'formal_parameter_scope', []);

export class Formal_Parameter_Scope extends Scope {
    constructor(parent?: Scope) {
        super(parent, Formal_Parameter_Scope_datum_spec);
    }
}

export const Generic_Parameter_Scope_datum_spec = new Host_Datum_Spec(
    'generic_parameter_scope', []);

export class Generic_Parameter_Scope extends Scope {
    constructor(parent?: Scope) {
        super(parent, Generic_Parameter_Scope_datum_spec);
    }

    static from_formal(formal: Formal_Parameters, parent: Scope): Generic_Parameter_Scope {
        const scope = new Generic_Parameter_Scope(parent);
        const add_parameter = (p: Formal_Parameter_Definition) => 
            add_definition(scope, p.name, new Unresolved_Generic_Parameter_Definition(p.position, p.name, p.type));
        for (let p of formal.required) add_parameter(p);
        for (let p of formal.optional) add_parameter(p);
        for (let p of formal.named) add_parameter(p);
        if (formal.rest) add_parameter(formal.rest);
        return scope;
    }
}

export const Unresolved_Generic_Parameter_Definition_datum_spec = new Host_Datum_Spec(
    'unresolved_generic_parameter_definition', []);

export class Unresolved_Generic_Parameter_Definition extends Definition {
    readonly name: Name;
    readonly type: Datum;

    constructor(
        position: Source_Position,
        name: Name,
        type: Datum) {
            super(position, Unresolved_Generic_Parameter_Definition_datum_spec);
            this.name = name;
            this.type = type;
        }
}

export function parse_formalparameters(lexer: Lexer, indentation: number, scope: Scope, required: boolean) {
    let initial_name: Name | undefined = undefined;
    if (!required) {
        initial_name = parse_name(lexer, indentation, scope, false);
        if (!initial_name) {
            const token = lexer.read(0);
            if (!(token instanceof Keyword) || (token.name.spelling != 'optional' && token.name.spelling != 'named')) {
                return undefined;
            }
        }
    }

    let result = new Formal_Parameters(
        scope instanceof Formal_Parameter_Scope ? 
        scope :
        new Formal_Parameter_Scope(scope));
    let mode = 'required';

    while(true) {
        lexer.match_newline(indentation, true);
        const selector = mode == 'named' && lexer.read(0) instanceof Keyword ?
        (lexer.read(0) as Keyword).name : undefined;
        const parameter_name = initial_name || parse_name(lexer, indentation, scope, false);
        if (parameter_name) {
            initial_name = undefined;
            const default_expr = mode != 'required' ?
                (lexer.match_name('=') ? 
                    parse_expression(lexer, indentation, scope, true) : new Quotation(false)) : undefined;
            const type = evaluate_type(parse_expression(lexer, indentation, scope, false), scope);
            const selector2 = selector || (mode == 'named' ? Name.make(parameter_name.spelling) : undefined);
            const formal = new Formal_Parameter_Definition(
                lexer.position(), parameter_name, type,
                default_expr, (default_expr ? result.scope : undefined),
                selector2);

            const new_scope = new Formal_Parameter_Scope(result.scope);
            add_definition(new_scope, parameter_name, formal);
            result.scope = new_scope;

            if (lexer.match_name('...')) {
                if (default_expr) {
                    throw new Error('rest parameter cannot have a default');
                }
                if (selector) {
                    throw new Error('rest parameter cannot have a selector keyword');
                }
                result.rest = formal;
                return result;
            } else if (mode == 'required') {
                result.required.push(formal);
            } else if (mode == 'optional') {
                result.optional.push(formal);
            } else if (mode == 'named') {
                result.named.push(formal);
            }

            if (!lexer.match_name(',')) {
                return result;
            }
        } else if (lexer.match_name('#')) {
            if (mode == 'named') {
                throw new Error('# parameter cannot be named or rest');
            }
            const tempname = Name.make("temp", new Macro_Context(scope));
            const constant = parse_anyname(lexer, indentation, scope, true);
            const formal = new Formal_Parameter_Definition(
                lexer.position(), 
                tempname, new Set([constant]));
            add_definition(result.scope, tempname, formal);

            if (lexer.match_name('...')) {
                throw new Error('# parameter cannot be named or rest');
            } else if (mode == 'required') {
                result.required.push(formal);
            } else if (mode == 'optional') {
                result.optional.push(formal);
            }

            if (!lexer.match_name(',')) {
                return result;
            }
        } else if (mode == 'required' && lexer.match_keyword('optional')) {
            mode = 'optional';
        } else if ((mode == 'required' || mode == 'optional') && lexer.match_keyword('named')) {
            mode = 'named';
        } else {
            return result;
        }
    }
}

export const Method_Head_datum_spec = new Host_Datum_Spec(
    'method_head', []);

export class Method_Head extends Host_Datum {
    readonly name: Name;
    readonly modifiers: Set<Method_Modifiers>; // DM uses method_modifiers class instead of set, this allows store descriptions along with boolean flags
    generic_parameters?: Name[];
    readonly formal_parameters: Formal_Parameters;
    result_type: Datum;

    constructor(name: Name, modifiers: Set<Method_Modifiers>, parameters: Formal_Parameters, result_type: Datum, generic_parameters?: Name[]) {
        super(Method_Head_datum_spec);
        this.name = name;
        this.modifiers = modifiers;
        this.formal_parameters = parameters;
        this.result_type = result_type;
        if (generic_parameters) this.generic_parameters = generic_parameters;
    }
}

export function parse_methodmodifiers(lexer: Lexer, indentation: number, scope: Scope, required: boolean) {
    const modifiers = new Set<Method_Modifiers>()
    while (true) {
        if (lexer.match_keyword('sealed')) {
            modifiers.add('sealed');
        } else if (lexer.match_keyword('dominant')) {
            modifiers.add('dominant');
        } else if (lexer.match_keyword('intrinsic')) {
            modifiers.add('intrinsic');
        } else {
            break;
        }
    }
    if (modifiers.size == 0 && required) {
        throw new Error('expected at least 1 modifier');
    }
    return modifiers;
}

export function parse_methodhead_after_name(lexer: Lexer, indentation: number, scope: Scope, name: Name, generic_parameters?: Name[]) {
    let function_name = name
    while (lexer.match_name('.')) {
        const defn = lookup_known_definition(scope, function_name);
        if (!(defn instanceof Module)) {
            throw new Error('expected module');
        }
        function_name = Name.make(
            parse_name(lexer, indentation, scope, true) as Name, defn);
    }
    lexer.must_match_name('(');
    const modifiers = parse_methodmodifiers(lexer, indentation, scope, false);
    const parameters = parse_formalparameters(lexer, indentation, scope, true) as Formal_Parameters;
    lexer.must_match_name(')');

    function_name = parse_methodhead_assigment(lexer, indentation, scope, function_name, parameters);

    const result_type = lexer.match_name('=>') ?
        evaluate_type(parse_expression(lexer, indentation, scope, true), scope) :
        lookup_known_definition(scope, 'everything');
    
    return new Method_Head(function_name, modifiers, parameters, result_type as Datum, generic_parameters);
}

export function parse_methodhead(lexer: Lexer, indentation: number, scope: Scope, required: boolean) {
    let generic_parameters: Name[] | undefined;
    if (lexer.match_name('[')) {
        generic_parameters = [];
        do {
            const name = parse_name(lexer, indentation, scope, true);
            generic_parameters.push(name as Name);
        } while(lexer.match_name(','))
        lexer.match_name(']');
    }

    if (generic_parameters) {
        const context = new Generic_Parameter_Scope(scope);
        for (let name of generic_parameters) {
            const defn = new Unresolved_Generic_Parameter_Definition(lexer.position(), name, Runtime.instance.lookup('everything'));
            add_definition(context, name, defn);
        }
        scope = context;
    }

    let function_name = parse_name(lexer, indentation, scope, false);
    if (function_name) {
        return parse_methodhead_after_name(lexer, indentation, scope, function_name, generic_parameters);
    }
    let parameters: Formal_Parameter_Definition[] = [];
    if (lexer.match_name('(')) {
        const name1 = parse_name(lexer, indentation, scope, true) as Name;
        const type1 = evaluate_type(parse_expression(lexer, indentation, scope, true), scope);

        lexer.must_match_name(')');

        function_name = parse_operator(lexer, indentation, scope, true) as Name; // parse_operator ???
        const defn = lookup_known_definition(scope, function_name);
        const macro_expander = defn instanceof Bundle && defn.operator ? 
            defn.operator.infix_expander : undefined;
        if (macro_expander) {
            const expansion = Runtime.instance.call(0, macro_expander, 
                name1, lexer, indentation, scope, function_name.context || false, true);
            if (expansion instanceof Method_Head) {
                if (expansion.formal_parameters.required[0].name.equal(name1)) {
                    const param = expansion.formal_parameters.required[0];
                    param.position = lexer.position();
                    param.name = name1;
                    param.type = type1;
                }
                if (lexer.match_name('=>')) {
                    expansion.result_type = evaluate_type(parse_expression(lexer, indentation, scope, true), scope);
                }   
                if (generic_parameters)
                    expansion.generic_parameters = generic_parameters;
                return expansion;
            }
            if (expansion instanceof Call_Expression && 
                    expansion.parameters.length >= 1 &&
                    name1.equal(expansion.parameters[0] as any)) {
                // const operator_name = function_name;
                if (expansion.method instanceof Bundle) {
                    function_name = expansion.method.name;
                } else {
                    function_name = expansion.method as Name;
                }
                parameters = [];
                parameters.push(new Formal_Parameter_Definition(lexer.position(), name1, type1));
                for (let i = 1; i < expansion.parameters.length; i++) {
                    const arg = expansion.parameters[i];
                    if (arg instanceof Name) {
                        parameters.push(new Formal_Parameter_Definition(
                            lexer.position(), arg, lookup_known_definition(scope, 'everything') as Datum));
                    } else if (arg instanceof Quotation) {
                        parameters.push(new Formal_Parameter_Definition(
                            lexer.position(), Name.make("temp", new Macro_Context(scope)),
                            new Set([arg.datum])));
                    } else {
                        throw new Error('dont know how to convert expansion of operator into a method_head');
                    }
                }
            } else {
                throw new Error('dont know how to convert expansion of operator into a method_head');
            }
        } else {
            let name2: Name | undefined = undefined;
            let type2: Datum | undefined = undefined;
            if (lexer.match_name('(')) {
                name2 = parse_name(lexer, indentation, scope, true);
                type2 = evaluate_type(parse_expression(lexer, indentation, scope, true), scope);
                lexer.must_match_name(')');
            } else if (lexer.match_name('#')) {
                name2 = Name.make('temp', new Macro_Context(scope));
                let datum = lexer.read(1);
                if (datum instanceof Name) {
                    datum = Name.make(datum.spelling);
                }
                type2 = new Set([datum]);
            } else {
                throw new Error('expected ( or #');
            }
            parameters = [
                new Formal_Parameter_Definition(lexer.position(), name1, type1),
                new Formal_Parameter_Definition(lexer.position(), name2 as any, type2),
            ]
        }
    } else if (function_name = parse_operator(lexer, indentation, scope, true)) {
        lexer.must_match_name('(');
        const name1 = parse_name(lexer, indentation, scope, true) as Name;
        const type1 = evaluate_type(parse_expression(lexer, indentation, scope, true), scope);
        lexer.must_match_name(')');
        parameters = [
            new Formal_Parameter_Definition(lexer.position(), name1, type1),
        ];
    } else if (required) {
        throw new Error('a name, an operator, or ( to start method head');
    } else {
        return undefined;
    }
    let formal_scope = new Formal_Parameter_Scope(scope);
    for (let formal of parameters) 
        add_definition(formal_scope, formal.name, formal);
    const formal_parameters = new Formal_Parameters(formal_scope);
    formal_parameters.required = parameters;

    const final_function_name = parse_methodhead_assigment(
        lexer, indentation, scope, function_name as Name, formal_parameters);
    const result_type = lexer.match_name('=>') ?
        evaluate_type(parse_expression(lexer, indentation, scope, true), scope) :
        lookup_known_definition(scope, 'everything');
    return new Method_Head(final_function_name, new Set(), formal_parameters, result_type as Datum, generic_parameters);
}

export function parse_methodhead_assigment(lexer: Lexer, indentation: number, scope: Scope, function_name: Name, paramters: Formal_Parameters) {
    if (!lexer.match_name(':=')) {
        return function_name;
    }
    lexer.must_match_name('(');
    const new_value_name = parse_name(lexer, indentation, scope, true);
    const new_value_type = evaluate_type(parse_expression(lexer, indentation, scope, true), scope);
    lexer.must_match_name(')');
    if (paramters.optional.length > 0 || paramters.named.length > 0 || paramters.rest) {
        throw new Error(':= can be only used with required formal paramters');
    }
    const formal = new Formal_Parameter_Definition(lexer.position(), new_value_name as Name, new_value_type);
    paramters.required.push(formal);
    paramters.scope = new Formal_Parameter_Scope(paramters.scope);
    add_definition(paramters.scope, new_value_name as Name, formal);
    return Name.make(function_name.spelling + ':=', function_name.context);
}

export function parse_operator(lexer: Lexer, indentation: number, scope: Scope, required: boolean) {
    const token = lexer.read(0);
    if (token instanceof Name) {
        if (is_punctuation(token.spelling)) {
            lexer.read(1);
            return token;
        }
        const defn = lookup_known_definition(scope, token);
        if (defn && defn instanceof Bundle && defn.operator) {
            lexer.read(1);
            return token;
        }
    }
    if (required) {
        throw new Error('a name that is not punctuation, an operator, or a macro, or backslash followed by a name or a string');
    }
    return undefined;
}


export function parse_denatured_name(lexer: Lexer): Name {
    const result = lexer.read(0);
    if (result instanceof Name) {
        lexer.read(1);
        return result;
    } else if (typeof result == 'string') {
        lexer.read(1);
        return Name.make(result);
    }
    throw new Error('expected name after backslash');
}

export function evaluate_type(expr: Expression | undefined, scope: Scope): Datum | Unresolved_Type {
    const $poly = Runtime.instance;
    if (!expr) return lookup_known_definition(scope, 'everything') as Bundle;
    const generic_parameter_scope = generic_context_of(expr, scope);
    if (generic_parameter_scope.size == 0) {
        const result = eval_expression(expr, scope);
        if (!$poly.call(0, $poly.lookup('in'), result, $poly.lookup('type')))
            throw new Parse_Error(undefined, `${datum_string(result)} is not member of class type`);
        return result;
    }
    return new Unresolved_Type(expr, generic_parameter_scope);
}

export function parse_anyname(lexer: Lexer, indentation: number, scope: Scope, required: boolean) {
    if (lexer.match_name('\\')) {
        return parse_denatured_name(lexer);
    }
    if (lexer.read(0) instanceof Name) {
        return (lexer.read(1) as any) as Name;
    }
    if (required) {
        throw new Error('a name, or backslash followed by a name or a string');
    }
    return undefined;
}

export function parse_name(lexer: Lexer, indentation: number, scope: Scope, required: boolean) {
    if (lexer.match_name('\\')) {
        return parse_denatured_name(lexer);
    }
    const token = lexer.read(0)
    if (token instanceof Name && !is_punctuation(token.spelling)) {
        const defn = lookup_known_definition(scope, token);
        if (!(defn && defn instanceof Bundle && defn.operator)) {
            lexer.read(1);
            return token;
        }
    }
    if (required) {
        throw new Error('a name that is not punctuation, an operator, or a macro, or backslash followed by a name or a string');
    }
    return undefined;
}

export function parse_body(lexer: Lexer, indentation: number, scope: Scope, required: boolean) {
    const block_scope = new Block_Scope(scope, [], 'head');
    const body_newline = lexer.match_newline(indentation, true);
    if (!body_newline) {
        const expr = parse_modified_expression(lexer, indentation, block_scope, required);
        block_scope.expressions.push(expr as any);
        return block_scope;
    }
    const body_indentation = body_newline.indentation;
    const loop = (inner_scope: Block_Scope): Expression => {
        let expr = parse_modified_expression(lexer, body_indentation, inner_scope, true);
        if (expr instanceof Block_Scope && expr.parent != inner_scope) 
            expr.parent = inner_scope;
        if (expr instanceof Prog_Expression) {
            inner_scope.expressions.push(...(expr.expressions.slice(0, expr.expressions.length - 1)));
            expr = expr.expressions[expr.expressions.length - 1];
        }
        inner_scope.expressions.push(expr as any);
        if (lexer.match_newline(body_indentation, false)) {
            let newline = true;
            while (newline) 
                newline = !!lexer.match_newline(body_indentation, false)
            return loop(expr instanceof Block_Scope && expr.type == 'tail' ? expr : inner_scope);
        }
        if (block_scope.expressions.length == 0 && inner_scope.expressions.length == 1) {
            return expr as any;
        }
        return block_scope;
    }
    return loop(block_scope);
}

export function parse_modified_expression(lexer: Lexer, indentation: number, scope: Scope, required: boolean) {
    let token = lexer.read(0);
    if (!(token instanceof Keyword && token.name.spelling != 'finally')) {
        return parse_expression(lexer, indentation, scope, required);
    }
    const modifiers = new Set<string>();
    while (token instanceof Keyword) {
        modifiers.add(token.name.spelling);
        lexer.read(1);
        lexer.match_newline(indentation, false);
        token = lexer.read(0)
    }
    const result = parse_expression(lexer, indentation, scope, true, -1, modifiers);
    return result;
}

export function parse_expression(lexer: Lexer, indentation: number, scope: Scope, required: boolean, precedence: number = -1, modifiers: Set<string> = new Set()) {
    const lhs_stack: Expression[] = [];
    const unary_stack: Expression[] = [];
    const binary_stack: Expression[] = [];

    const do_unrecognized_token = () => {
        if (lhs_stack.length == 0 && binary_stack.length == 0 && unary_stack.length == 2) {
            unary_stack.pop();
            return unary_stack.pop();
        } else if (required || unary_stack.length != 0 || lhs_stack.length != 0) {
            const token = lexer.read(0);
            const message = token !== undefined ?
                `invalid token ${datum_string(lexer.read(0) as Datum)}` :
                `unexpected end of file`;
            throw new Parse_Error(lexer, message);
        } else {
            return undefined;
        }
    }

    const do_lhs = (): Expression | undefined => {
        const token = lexer.read(0);
        if (typeof token == 'number' || typeof token == 'string' || token instanceof Char) {
            lexer.read(1);
            return token;
        } 
        if (Name.same_spelling(token, '\\')) {
            lexer.read(1);
            return parse_denatured_name(lexer);
        }
        if (token !== undefined && !(token instanceof Name) && !(token instanceof Keyword) && !(token instanceof Newline)) {
            lexer.read(1);
            return token;
        }
        if (!(token instanceof Name)) {
            return do_unrecognized_token();
        } 

        const defn = lookup_known_definition(scope, token);
        const operator = defn && defn instanceof Bundle && defn.operator ?
            defn.operator : undefined;
        if (!operator) {
            if (is_punctuation(token.spelling)) {
                return do_unrecognized_token();
            }
            lexer.read(1);
            return token;
        }
        if (!operator.prefix_expander) {
            unary_stack.push(lexer.read(1) as Expression);
            unary_stack.push(defn as Expression);
            return do_lhs();
        }
        const $poly = Runtime.instance;
        const expansion = $poly.call(source_location_of(lexer), operator.prefix_expander, 
            lexer, indentation, scope, modifiers, (lexer.read(1) as Name).context || false);
        if (expansion === undefined) {
            throw new Parse_Error(lexer, `macro returned unrecognized expansion`);
        }
        if (!(expansion instanceof Compound_Expression) && is_sequence(expansion)) {
            lexer.insert(sequence_to_internal_list(expansion) as Token[]);
            return do_lhs();
        }
        return expansion;
    }

    const do_unit = (): Expression | undefined => {
        let lhs = do_lhs();
        if (lhs === undefined && unary_stack.length > 0) {
            throw new Parse_Error(lexer, 'unary operator is not followed by operand');
        }
        while (unary_stack.length > 0) {
            const bundle = unary_stack.pop();
            if (!(bundle instanceof Bundle) || !(bundle.operator)) {
                throw new Parse_Error(lexer, 'expected bundle operator to be in unary stack');
            }
            const operator = unary_stack.pop();
            if (!operator) {
                throw new Parse_Error(lexer, 'expected operator to be in unary stack');
            }
            if (!bundle.operator.arity.has('unary')) {
                throw new Parse_Error(lexer, `${JSON.stringify(bundle.name?.spelling)} is not unary operator`);
            }
            lhs = new Call_Expression(lexer.position(),
                operator, [lhs as Expression], false);
        }   
        return lhs;
    }

    const do_operator = (lhs: Expression | undefined): Expression | undefined => {
        const token = lexer.read(0);
        if (!(token instanceof Name)) {
            return drain(lhs, precedence);
        }
        const defn = lookup_known_definition(scope, token);
        if (!(defn instanceof Bundle) || !defn.operator) {
            return drain(lhs, precedence);
        }
        const arity = defn.operator.arity;
        if (!(arity.has('binary') || arity.has('infix') || arity.has('ternary') || arity.has('suffx'))) {
            // throw new Parse_Error(lexer, `token ${datum_string(token)} is not operator`);
            return drain(lhs, precedence);
        }
        const operator_precedence = defn.operator.left_precedence;
        if (operator_precedence <= precedence) {
            return drain(lhs, precedence);
        }
        if (!defn.operator.infix_expander) {
            lhs_stack.push(drain(lhs, operator_precedence) as any);
            binary_stack.push(lexer.read(1) as any);
            binary_stack.push(defn as any);
            return do_operator(do_lhs());
        }
        const _lhs = drain(lhs, operator_precedence);
        const expansion = Runtime.instance.call(source_location_of(lexer),
            defn.operator.infix_expander, _lhs as any, lexer, indentation, scope, 
            (lexer.read(1) as Name).context || false, false);
        if (is_sequence(expansion)) {
            lexer.insert(sequence_to_internal_list(expansion) as Token[]);
            return do_operator(do_lhs());
        }
        if (expansion === undefined) {
            throw new Parse_Error(lexer, "macro returned unrecognized expansion");
        }
        return do_operator(expansion);
    }

    const drain = (rhs: Expression | undefined, precedence: number) => {
        while (binary_stack.length > 0 && 
            (binary_stack[binary_stack.length - 1] as any).operator.right_precedence >= precedence) {
            binary_stack.pop();
            rhs = new Call_Expression(
                lexer.position(),
                binary_stack.pop() as any,
                [lhs_stack.pop() as any, rhs],
                false,
            );
        }
        return rhs;
    }

    const lhs = do_unit();
    const result = lhs !== undefined ? do_operator(lhs) : undefined;
    
    return result;
}

export function parse_actualparameters(lexer: Lexer, indentation: number, scope: Scope, required: boolean) {
    const result: Expression[] = [];
    const loop = () => {
        lexer.match_newline(indentation, true);
        if (lexer.read(0) instanceof Keyword) {
            result.push(new Quotation((lexer.read(1) as Keyword).name));
        }
        const expr = parse_expression(lexer, indentation, scope, result.length > 0);
        if (expr === undefined) {
            return;
        }
        result.push(expr);
        if (lexer.match_name(',')) {
            loop();
        }
    }
    loop();
    return result;
}

export function parse_file(lexer: Lexer, indentation: number, scope: Scope, required: boolean) {
    const $poly = Runtime.instance;
    let parser: Function | Datum = parse_modified_expression;
    if (lexer.match_keyword('syntax')) {
        let syntax_parser = parse_name(lexer, indentation, scope, true) as Name;
        syntax_parser = Name.make('parse_' + syntax_parser.spelling, syntax_parser.context);
        const defn = lookup_known_definition(scope, syntax_parser);
        if (!defn)
            throw new Parse_Error(lexer.position(), `syntax parser ${syntax_parser.spelling} is not defined`);
        parser = defn;
    }
            
    const prog_expression = new Prog_Expression(lexer.position(), []);
    while(lexer.read(0) !== undefined) {
        if (lexer.read(0) instanceof Newline && !lexer.match_newline(0, false)) {
            throw new Parse_Error(lexer, 'each top-level expression must be on a separate line and all top-level expressions must begin at the first column');
        }
        if (lexer.read(0) === undefined) {
            break;
        }
        try {
            const position = lexer.position();
            const location = $poly.call_stack.make_source_location(
                position.name, position.line);
            const parse_expression = () =>
                (typeof parser == 'function') ?
                        parser(lexer, indentation, scope, required) :
                        $poly.call(location, parser, lexer, indentation, scope, required);
            if (lexer.match_keyword('module')) {
                const module_expression = parse_expression();
                const module = eval_expression(module_expression, $poly.modules as Scope);
                if (!(module instanceof Module))
                    throw new Parse_Error(lexer.position(), `expresion after module: keyword must be member of class module`);
                scope = module;
                continue;
            }
            const expr = parse_expression();
            prog_expression.expressions.push(expr as Expression);
        } catch(e) {
            if (e instanceof Poly_Error && !e.position)
                e.position = lexer.position();
            throw e;
        }
    }
    return prog_expression;
}

export function sequence_to_internal_list(sequence: Datum): Datum[] {
    if (Array.isArray(sequence)) return sequence;
    if (sequence instanceof Internal_Array) return sequence.array;

    const $poly = Runtime.instance;

    const iterate = $poly.lookup('iterate');
    const more = $poly.lookup('more?');
    const next = $poly.lookup('next');

    const output: Datum[] = [];
    let i = $poly.call(0, iterate, sequence);
    while ($poly.call(0, more, sequence, i)) {
        const e = $poly.call(0, next, sequence, i);
        output.push(e)
        i = $poly.call(0, iterate, sequence, i);
    }
    return output;
}

export function is_sequence(datum: Datum): boolean {
    if (Array.isArray(datum)) return true;
    if (datum instanceof Internal_Array) return true;
    if (typeof datum != 'object') return false;

    const $poly = Runtime.instance;
    return !!$poly.call(0, $poly.lookup('in'), datum, $poly.lookup('sequence'));
}

export function tail_expression(expr: Expression): Expression {
    while (expr instanceof Block_Scope)
        expr = expr.expressions[expr.expressions.length - 1];
    return expr;
}

/*
export function cut_tail(expr: Expression, copied: Map<any, any> = new Map()): Expression | undefined {
    if (expr instanceof Block_Scope) {
        const block = copy_expression(expr, copied) as Block_Scope;
        const last = block.expressions.pop() as Expression;
        const cutted = cut_tail(last);  
        if (cutted) block.expressions.push(cutted);
        return block;
    }
    return undefined;
}
*/

/*
export function cut_tail(expr: Expression, copied: Map<any, any> = new Map()): Expression | undefined {
    if (expr instanceof Block_Scope) {
        const parent = copied?.get(expr.parent) || expr.parent;
        const block = new Block_Scope(
            parent as Scope, 
            expr.expressions.map(e => copy_expression(e, copied)),
            expr.type);
        for (let [name, defn] of expr.definitions) {
            const new_name = copy_expression(name, copied) as Name
            add_definition(block, new_name, copy_expression(defn, copied) as Definition);
        }
        const last = block.expressions.pop() as Expression;
        const cutted = cut_tail(last, copied);    
        if (cutted) block.expressions.push(cutted);
        return block;
    }
    return undefined;
}*/

export function cut_tail(expr: Expression): Expression | undefined {
    if (expr instanceof Block_Scope) {
        const last_element = expr.expressions[expr.expressions.length - 1];
        if (last_element instanceof Block_Scope) {
            cut_tail(last_element);
            return expr;
        }
        expr.expressions.pop();
    }
    return expr;
}


export const Superclass_Expression_datum_spec = new Host_Datum_Spec(
    'superclass_expression', []);

export class Superclass_Expression extends Compound_Expression {
    name: Name;
    generic_parameters?: Expression[];
    constructor_parameters: Expression[];
    spread: boolean;

    constructor(position: Source_Position, name: Name, constructor_parameters: Expression[], generic_parameters: Expression[] | undefined, spread: boolean) {
        super(position, Superclass_Expression_datum_spec);
        this.name = name;
        this.constructor_parameters = constructor_parameters;
        this.generic_parameters = generic_parameters;
        this.spread = spread;
    }
}

export const Class_Expression_datum_spec = new Host_Datum_Spec(
    'class_expression', []);

export class Class_Expression extends Compound_Expression {
    id: number;
    constructor_name: Name;
    generic_parameters?: Formal_Parameters;
    formal_parameters: Formal_Parameters;
    slot_assigments: Assigment_Expression[];
    superclasses: Superclass_Expression[];
    length_expression?: Expression;

    constructor(
        position: Source_Position,
        id: number, 
        constructor_name: Name,
        parameters: Formal_Parameters, 
        generic_parameters: Formal_Parameters | undefined,
        slot_assigments: Assigment_Expression[], 
        superclasses: Superclass_Expression[], 
        length?: Expression) {
            super(position, Class_Expression_datum_spec);
            this.id = id;
            this.constructor_name = constructor_name;
            this.formal_parameters = parameters;
            if (generic_parameters)
                this.generic_parameters = generic_parameters;
            this.slot_assigments = slot_assigments;
            this.superclasses = superclasses;
            if (length) this.length_expression = length;
        }
}

export function copy_expression(expr: Expression, copied: Map<any, any> = new Map()): Expression {
    if (copied.has(expr)) return copied.get(expr) as Expression;
    let copy = expr;
    if (expr instanceof Name) {
        if (copied.has(expr.context)) 
            copy = Name.make(expr, copied.get(expr.context));
        else if (expr.context instanceof Macro_Context && copied.has(expr.context.parent_scope)) {
            const context = new Macro_Context(copied.get(expr.context.parent_scope));
            copied.set(expr.context, context);
            copy = Name.make(expr, context);
        }
    } else if (expr instanceof If_Expression) {
        copy = new If_Expression(
            expr.position, 
            copy_expression(expr.test, copied),
            copy_expression(expr.consequent, copied),
            copy_expression(expr.alternate, copied));
    } else if (expr instanceof Method_Expression) {
        copy = new Method_Expression(
            expr.position,
            expr.name ? copy_expression(expr.name, copied) as Name : undefined,
            expr.generic_parameters ?
                expr.generic_parameters.slice() : undefined,
            copy_formalparameters(expr.formal_parameters, copied),
            copied.has(expr.result_type) ? copied.get(expr.result_type) : expr.result_type,
            new Set(expr.modifiers),
            new Quotation(false));
        copied.set(expr, copy);
        (copy as Method_Expression).body = copy_expression(expr.body, copied);
    } else if (expr instanceof Call_Expression) {
        copy = new Call_Expression(
            expr.position,
            copy_expression(expr.method, copied),
            expr.parameters.map(p => copy_expression(p, copied)),
            expr.spread)
    } else if (expr instanceof Prog_Expression) {
        copy = new Prog_Expression(
            expr.position,
            expr.expressions.map(e => copy_expression(e, copied)));
    } else if (expr instanceof Block_Scope) {
        const parent = copied.get(expr.parent) || expr.parent;
        const block = new Block_Scope(
            parent as Scope, 
            [],
            expr.type);
        copied.set(expr, block);
        for (let [name, expr_defn] of expr.definitions) {
            const new_name = copy_expression(name, copied) as Name;
            const defn = copy_expression(expr_defn, copied) as Definition;
            add_definition(block, new_name, defn);
            if (defn instanceof Known_Definition) {
                if (defn.value instanceof Bundle)
                    defn.value = copy_bundle(defn.value, copied);
                else if (defn.value instanceof Method_Expression) 
                    defn.value = copy_expression(defn.value, copied);
                else if (defn.value instanceof Runtime_Method_Datum) {
                    const method_expression = Runtime.instance.method_expressions[defn.value.id];
                    if (method_expression) defn.value = copy_expression(method_expression, copied);
                }
            }
        }
        block.expressions = expr.expressions.map(e => copy_expression(e, copied));
        copy = block;
    } else if (expr instanceof Generic_Parameter_Scope) {
        const parent = copied.get(expr.parent) || expr.parent;
        const context = new Generic_Parameter_Scope(parent);
        copied.set(expr, context);
        for (let [name, expr_defn] of expr.definitions) {
            const new_name = copy_expression(name, copied) as Name;
            const defn = copy_expression(expr_defn, copied) as Definition;
            add_definition(context, new_name, defn);
        }
        copy = context;
    } else if (expr instanceof Assigment_Expression) {
        copy = new Assigment_Expression(
            expr.position,
            copy_expression(expr.lhs, copied) as Name,
            copy_expression(expr.rhs, copied));
    } else if (expr instanceof Instance_Expression) {
        copy = new Instance_Expression(
            expr.position,
            copied.has(expr.bundle) ? copied.get(expr.bundle) : expr.bundle,
            expr.expressions.map(e => copy_expression(e, copied)));
    } else if (expr instanceof Slot_Read_Expression) {
        copy = new Slot_Read_Expression(
            expr.position,
            copied.has(expr.bundle) ? copied.get(expr.bundle) : expr.bundle,
            copy_expression(expr.lhs, copied),
            copy_expression(expr.slot, copied) as Name);
    } else if (expr instanceof Slot_Write_Expression) {
        copy = new Slot_Write_Expression(
            expr.position,
            copied.has(expr.bundle) ? copied.get(expr.bundle) : expr.bundle,
            copy_expression(expr.lhs, copied),
            copy_expression(expr.slot, copied) as Name,
            copy_expression(expr.rhs, copied));
    } else if (expr instanceof Variable_Definition) {
        copy = new Variable_Definition(
            expr.position,
            copy_expression(expr.name, copied) as Name,
            copied.has(expr.type) ? copied.get(expr.type) : expr.type,
            copy_expression(expr.expression, copied));
    } else if (expr instanceof Constant_Definition) {
        copy = new Constant_Definition(
            expr.position,
            copy_expression(expr.name, copied) as Name,
            copied.has(expr.type) ? copied.get(expr.type) : expr.type,
            copy_expression(expr.expression, copied));
    } else if (expr instanceof Formal_Parameter_Definition) {
        copy = new Formal_Parameter_Definition(
            expr.position,
            copy_expression(expr.name, copied) as Name,
            copied.has(expr.type) ? copied.get(expr.type) : expr.type,
            expr.default_expression,
            expr.scope_for_default_expression,
            expr.selector);
    } else if (expr instanceof Known_Definition) {
        copy = new Known_Definition(
            expr.position, 
            copy_expression(expr.name, copied) as Name,
            (copied.has(expr.value) ? copied.get(expr.value) : expr.value));
    } else if (expr instanceof Quotation) {
        if (expr.datum instanceof Runtime_Method_Datum) {
            const method_expr = Runtime.instance.method_expressions[expr.datum.id];
            if (method_expr && copied.has(method_expr)) copy = copied.get(method_expr);
        } else if (expr.datum instanceof Bundle) copy = new Quotation(copied.get(expr.datum) || expr.datum);
        else copy = new Quotation(expr.datum);
    } else if (expr instanceof Exit_Expression) {
        copy = new Exit_Expression(
            expr.position,
            copy_expression(expr.name, copied) as Name,
            copy_expression(expr.expression, copied));
    } else if (expr instanceof Exit_Call_Expression) {
        copy = new Exit_Call_Expression(
            expr.position,
            copy_expression(expr.exit, copied) as Exit_Expression,
            copy_expression(expr.expression, copied));
    }
    if (copy != expr) copied.set(expr, copy);
    return copy;
}

export function copy_formalparameters(formal: Formal_Parameters, copied: Map<any, any> = new Map()) {
    const path = [];
    let scope: Scope = formal.scope;
    while(scope instanceof Formal_Parameter_Scope || scope instanceof Generic_Parameter_Scope) {
        path.push(scope);
        scope = scope.parent as Scope;
    }
    
    while(path.length > 0) {
        const scope = path.pop() as Formal_Parameter_Scope | Generic_Parameter_Scope;
        if (copied.has(scope)) continue;
        const parent = copied.get(scope.parent) || scope.parent;
        const copy_scope = scope instanceof Formal_Parameter_Scope ?
            new Formal_Parameter_Scope(parent) :
            new Generic_Parameter_Scope(parent);
        copied.set(scope, copy_scope);
        for (let [name, defn] of scope.definitions) {
            const new_name = copy_expression(name, copied) as Name;
            add_definition(copy_scope, new_name, copy_expression(defn, copied) as Definition);
        }
    }

    const required = formal.required.map(p => copy_expression(p, copied) as Formal_Parameter_Definition);
    const optional = formal.optional.map(p => copy_expression(p, copied) as Formal_Parameter_Definition);
    const named = formal.named.map(p => copy_expression(p, copied) as Formal_Parameter_Definition);
    const rest = formal.rest ? copy_expression(formal.rest, copied) as Formal_Parameter_Definition : undefined;

    const parent = copied?.get(formal.scope) || formal.scope;
    const formal_copy = new Formal_Parameters(parent);
    formal_copy.required = required;
    formal_copy.optional = optional;
    formal_copy.named = named;
    formal_copy.rest = rest;
    
    return formal_copy;
}

export function copy_bundle(bundle: Bundle, copied: Map<any, any> = new Map()) {
    if (copied.has(bundle)) return copied.get(bundle) as Bundle;
    const bundle_copy = new Bundle(bundle.name ? 
        copy_expression(bundle.name, copied) as Name : undefined);
    copied.set(bundle, bundle_copy);
    if (bundle.class) bundle_copy.class = bundle.class;
    if (bundle.operator) {
        bundle_copy.operator = new Operator_Nature();
        bundle_copy.operator.arity = new Set(bundle.operator.arity);
        bundle_copy.operator.left_precedence = bundle.operator.left_precedence;
        bundle_copy.operator.right_precedence = bundle.operator.right_precedence;
        if (bundle.operator.infix_expander) {
            const method_expr = Runtime.instance.method_expressions[bundle.operator.infix_expander.id];
            if (method_expr) {
                const method_copy = copy_expression(method_expr, copied) as Method_Expression;
                bundle_copy.operator.infix_expander = method_expression_to_datum(method_copy);
            } else bundle_copy.operator.infix_expander = bundle.operator.infix_expander;
        }
        if (bundle.operator.prefix_expander) {
            const method_expr = Runtime.instance.method_expressions[bundle.operator.prefix_expander.id];
            if (method_expr) {
                const method_copy = copy_expression(method_expr, copied) as Method_Expression;
                bundle_copy.operator.prefix_expander = method_expression_to_datum(method_copy);
            } else bundle_copy.operator.prefix_expander = bundle.operator.prefix_expander;
        }
    }
    if (bundle.function) {
        bundle_copy.function = new Function_Nature();
        for (let m of bundle.function.methods) {
            const method_expr = Runtime.instance.method_expressions[m.id];
            if (!method_expr) {
                add_method(bundle_copy, m);
                continue;
            }
            const method_copy = copy_expression(method_expr, copied) as Method_Expression;
            add_method_expression(bundle_copy, method_copy);
        }
        if (bundle.function.generic_methods) for (let gm of bundle.function.generic_methods) {
            const method_expr = Runtime.instance.generic_method_expressions[gm.id];
            if (!method_expr) {
                add_method(bundle_copy, gm);
                continue;
            }
            const method_copy = copy_expression(method_expr, copied) as Method_Expression;
            add_method_expression(bundle_copy, method_copy);
        }
    }
    return bundle_copy;
}

export function flat_expressions(expr: Expression): Expression[] {
    if (expr instanceof Block_Scope) {
        const result: Expression[] = [];
        for (let body_expr of expr.expressions) 
            result.push(...flat_expressions(body_expr));
        return result;
    }
    return [expr];
}

export const Unresolved_Type_datum_spec = new Host_Datum_Spec(
    'unresolved_type', []);

export class Unresolved_Type extends Host_Datum {
    expression: Expression;
    context: Set<Unresolved_Generic_Parameter_Definition>;  

    constructor(expression: Expression, context: Set<Unresolved_Generic_Parameter_Definition>) {
        super(Unresolved_Type_datum_spec);
        this.expression = expression;
        this.context = context;
    }
}

export function generic_context_of(expr: Expression, scope: Scope, visited: Set<Expression> = new Set(), mentions: Set<Unresolved_Generic_Parameter_Definition> = new Set()): Set<Unresolved_Generic_Parameter_Definition> {
    if (expr instanceof Name) { 
        const expr_defn = lookup(scope, expr)
        if (expr_defn instanceof Unresolved_Generic_Parameter_Definition)
            mentions.add(expr_defn);
        else if (expr_defn instanceof Formal_Parameter_Definition && expr_defn.type instanceof Unresolved_Type)
            for (let elem of expr_defn.type.context) mentions.add(elem);
        else if (expr_defn instanceof Constant_Definition && expr_defn.type instanceof Unresolved_Type)
            for (let elem of expr_defn.type.context) mentions.add(elem);
        else if (expr_defn instanceof Variable_Definition && expr_defn.type instanceof Unresolved_Type)
            for (let elem of expr_defn.type.context) mentions.add(elem);
    }
    if (visited.has(expr)) return mentions;
    visited.add(expr);
    if (expr instanceof If_Expression) {
        generic_context_of(expr.test, scope, visited, mentions);
        generic_context_of(expr.consequent, scope, visited, mentions);
        generic_context_of(expr.alternate, scope, visited, mentions);
    }
    else if (expr instanceof Method_Expression) {
        const formal = expr.formal_parameters;
        for (let p of formal.required) generic_context_of(p, formal.scope, visited, mentions);
        for (let p of formal.optional) generic_context_of(p, formal.scope, visited, mentions);
        for (let p of formal.named) generic_context_of(p, formal.scope, visited, mentions);
        if (formal.rest) generic_context_of(formal.rest, formal.scope, visited, mentions)

        generic_context_of(expr.body, expr.formal_parameters.scope, visited, mentions);
    }
    else if (expr instanceof Call_Expression) {
        generic_context_of(expr.method, scope, visited, mentions);
        for (let param of expr.parameters) 
            generic_context_of(param, scope, visited, mentions);
    }
    else if (expr instanceof Prog_Expression) {
        for (let body_expr of expr.expressions) 
            generic_context_of(body_expr, scope, visited, mentions);
    }
    else if (expr instanceof Block_Scope) {
        for (let body_expr of expr.expressions) 
            generic_context_of(body_expr, expr, visited, mentions);
    }
    else if (expr instanceof Assigment_Expression) {
        generic_context_of(expr.lhs, scope, visited, mentions);
        generic_context_of(expr.rhs, scope, visited, mentions);
    }
    else if (expr instanceof Superclass_Expression) {
        generic_context_of(expr.name, scope, visited, mentions);
        for (let p of expr.constructor_parameters)
            generic_context_of(p, scope, visited, mentions);
        if (expr.generic_parameters) for (let p of expr.generic_parameters)
            generic_context_of(p, scope, visited, mentions);
    }
    else if (expr instanceof Instance_Expression) {
        for (let body_expr of expr.expressions) 
            generic_context_of(body_expr, scope, visited, mentions);
    }
    else if (expr instanceof Slot_Read_Expression) {
        generic_context_of(expr.lhs, scope, visited, mentions);
    }
    else if (expr instanceof Slot_Write_Expression) {
        generic_context_of(expr.lhs, scope, visited, mentions);
        generic_context_of(expr.rhs, scope, visited, mentions);
    } else if (expr instanceof Variable_Definition) {
        generic_context_of(expr.expression, scope, visited, mentions);
    } else if (expr instanceof Constant_Definition) {
        generic_context_of(expr.expression, scope, visited, mentions);
    } else if (expr instanceof Exit_Expression) {
        generic_context_of(expr.expression, scope, visited, mentions);
    } else if (expr instanceof Exit_Call_Expression) {
        generic_context_of(expr.expression, scope, visited, mentions);
    } else if (expr instanceof Quotation && expr.datum instanceof Runtime_Method_Datum) {
        const method_expr = Runtime.instance.method_expressions[expr.datum.id];
        if (method_expr) generic_context_of(method_expr, scope, visited, mentions);
    } else if (expr instanceof Quotation && expr.datum instanceof Bundle) {
        if (expr.datum.function) for (let m of expr.datum.function.methods) {
            const method_expr = Runtime.instance.method_expressions[m.id];
            if (method_expr) generic_context_of(method_expr, scope, visited, mentions);
        }
    } else if (expr instanceof Known_Definition && expr.value instanceof Bundle) {
        if (expr.value.function) for (let m of expr.value.function.methods) {
            const method_expr = Runtime.instance.method_expressions[m.id];
            if (method_expr) generic_context_of(method_expr, scope, visited, mentions);
        }
    }
    return mentions;
}


export function eliminate_unresolved_types(expr: Expression, scope: Scope, visited: Set<Expression> = new Set()) {
    switch (typeof expr) {
    case 'undefined':
        return;
    case 'boolean':
        return;
    case 'number':
        return;
    case 'string':
        return;
    }
    if (expr instanceof Char) return;
    if (expr instanceof Quotation) return;
    if (expr instanceof Name) return;
    if (visited.has(expr)) return;
    visited.add(expr);
    if (expr instanceof Block_Scope) {
        for (let body_expr of expr.expressions)
            eliminate_unresolved_types(body_expr, expr, visited);
        return;
    }
    if (expr instanceof Prog_Expression) {
        for (let body_expr of expr.expressions)
            eliminate_unresolved_types(body_expr, scope, visited);
        return;
    }
    if (expr instanceof If_Expression) {
        eliminate_unresolved_types(expr.test, scope, visited);
        eliminate_unresolved_types(expr.consequent, scope, visited);
        eliminate_unresolved_types(expr.alternate, scope, visited);
        return;
    }
    if (expr instanceof Call_Expression) {
        eliminate_unresolved_types(expr.method, scope, visited);
        for (let p of expr.parameters) 
            eliminate_unresolved_types(p, scope, visited);
        return;
    }
    if (expr instanceof Assigment_Expression) {         
       eliminate_unresolved_types(expr.lhs, scope, visited)
       eliminate_unresolved_types(expr.rhs, scope, visited);
       return;
    }
    if (expr instanceof Known_Definition) {
        return;
    }
    if (expr instanceof Constant_Definition) {
        eliminate_unresolved_types(expr.expression, scope, visited);
        if (expr.type instanceof Unresolved_Type)
            expr.type = evaluate_type(expr.type.expression, scope);
        return;
    }
    if (expr instanceof Variable_Definition) {
        eliminate_unresolved_types(expr.expression, scope, visited);
        if (expr.type instanceof Unresolved_Type)
            expr.type = evaluate_type(expr.type.expression, scope);
        return;
    }
    if (expr instanceof Formal_Parameter_Definition) {
        if (expr.type instanceof Unresolved_Type)
            expr.type = evaluate_type(expr.type.expression, scope);
        return;
    }
    if (expr instanceof Method_Expression) {
        const formal = expr.formal_parameters;
        const parameters: Set<Definition> = new Set();
        for (let p of formal.required) parameters.add(p);
        for (let p of formal.optional) parameters.add(p);
        for (let p of formal.named) parameters.add(p)
        if (formal.rest) parameters.add(formal.rest);

        let scope = formal.scope;
        while (scope.parent) {
            for (let defn of scope.definitions.values()) if (parameters.has(defn)) 
                eliminate_unresolved_types(defn, scope, visited);
            scope = scope.parent;
        }
        if (expr.result_type instanceof Unresolved_Type)  
            expr.result_type = evaluate_type(expr.result_type.expression, formal.scope)
        eliminate_unresolved_types(expr.body, formal.scope);
        return;
    }
    if (expr instanceof Instance_Expression) {
        for (let e of expr.expressions)
            eliminate_unresolved_types(e, scope, visited);
        return;
    }
    if (expr instanceof Slot_Read_Expression) {
        eliminate_unresolved_types(expr.lhs, scope, visited);
        return;
    }
    if (expr instanceof Slot_Write_Expression) {
        eliminate_unresolved_types(expr.lhs, scope, visited);
        eliminate_unresolved_types(expr.rhs, scope, visited);
        return;
    }
    if (expr instanceof Exit_Expression) {
        eliminate_unresolved_types(expr.expression, scope, visited);
    }
    if (expr instanceof Exit_Call_Expression) {
        eliminate_unresolved_types(expr.expression, scope, visited);
    }
    // throw new Error('unknown expression');
}

export function datum_print(x: Internal_Array) {
    console.log(...x.array.map(arr => datum_string(arr)));
}

export function datum_string(x: Datum): string {
    if (typeof x == 'number') return x.toString();
    if (typeof x == 'string') return x;
    if (typeof x == 'boolean') return x ? 'true' : 'false';
    if (x instanceof Name) return x.spelling;
    if (x instanceof Char) return String.fromCharCode(x.code);
    const $poly = Runtime.instance;
    const stringer = $poly.lookup('string');
    if (x instanceof Type_Union) {
        const elements = Array.from(x.types).map(e => $poly.call(0, stringer, e));
        return 'type_union(' + elements.join('|') + ')';
    }
    if (x instanceof Type_Intersection) {
        const elements = Array.from(x.types).map(e => $poly.call(0, stringer, e));
        return 'type_intersection(' + elements.join('&') + ')';
    }
    if (x instanceof Internal_Array) {
        const type = x.$datumclass.class?.generic_instance?.generic_actuals[0];
        const type_string = $poly.call(0, stringer, type as Datum);
        const elements = x.array.map(e => $poly.call(0, stringer, e));
        return '<' + type_string + '>' + '[' + elements.join(', ') + ']';
    }
    if (x instanceof Set) {
        const elements = Array.from(x).map(e => $poly.call(0, stringer, e));
        return '{' + elements.join(',') + '}';
    }
    if (Array.isArray(x)) {
        const elements = x.map(e => $poly.call(0, stringer, e));
        return '[' + elements.join(', ') + ']';
    }
    if (x instanceof Bundle) {
        const spelling = x.name?.spelling || 'unknown';
        if (!x.class || !x.class.generic_instance)
            return spelling;
        const parameters = x.class.generic_instance.generic_actuals.map(
            e => $poly.call(0, stringer, e));
        return spelling + '[' + parameters.join(', ') + ']';
    }
    const bundle = classof(x);

    const slots = bundle.class?.slots.
        map(e => e.name.spelling + ': ' + $poly.call(0, stringer, x.getslot(e.name)));
    return  datum_string(bundle) + '(' + slots?.join(', ') + ')';
}

export function source_location_of(position: Lexer | Source_Position): number {
    position = position instanceof Lexer ?
        position.position() : position;
    const location = Runtime.instance.call_stack.make_source_location(
        position.name, position.line);
    return location;
}

export function in_type_union(x0: Datum, x1: Type_Union) {
    x0 = classof(x0);
    for (let elem of x1.types)
        if (is_subtype_or_equal(x0, elem)) return true;
    return false;
}

export function lte_type_union(x0: Datum, x1: Datum) {
    if (x0 instanceof Type_Union) {
        for (let elem of x0.types) if (is_subtype_or_equal(elem, x1))
            return true;
        return false;   
    }
    if (x1 instanceof Type_Union) {
        for (let elem of x1.types) if (!is_subtype_or_equal(elem, x0))
            return false;
        return true;
    }   
    return false;
}

export function in_type_intersection(x0: Datum, x1: Type_Intersection) {
    x0 = classof(x0);
    for (let elem of x1.types)
        if (!is_subtype_or_equal(x0, elem)) return false;
    return true;
}

export function lte_type_intersection(x0: Datum, x1: Datum) {
    if (x0 instanceof Type_Intersection) {
        for (let elem of x0.types) if (!is_subtype_or_equal(elem, x1))
            return false;
        return true; 
    }
    if (x1 instanceof Type_Intersection) {
        for (let elem of x1.types) if (is_subtype_or_equal(elem, x0))
            return true;
        return false;
    }
    return false;
}