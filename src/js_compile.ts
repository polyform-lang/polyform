import { Source_Position, Poly_Error } from "./token";
import { Module, Block_Scope, lookup, Expression, Quotation, If_Expression, Prog_Expression, Scope, Call_Expression, Assigment_Expression, Known_Definition, Constant_Definition, Variable_Definition, Method_Expression, Instance_Expression, Slot_Read_Expression, Definition, Formal_Parameters, tail_expression, Slot_Write_Expression, cut_tail, copy_expression, Formal_Parameter_Scope, Unresolved_Generic_Parameter_Definition, Compound_Expression, copy_formalparameters, Generic_Parameter_Scope, Exit_Expression, Exit_Call_Expression } from "./expression";
import { Macro_Context, Char, Class_Nature, Name, Host_Datum, Host_Datum_Spec, Slot_Specifier, Type, Datum, Bundle, Internal_Array } from "./datum";
import { JS_object_reconstructor, JS_object_mapper, isolated_reconstructor } from "./js_reconstruct";
import { Runtime } from "./js_runtime";
import { is_subtype_or_equal } from "./class";
import { Runtime_Method_Datum, Runtime_Method_Head, Method_Environment, method_expression_to_datum  } from './method';

export class JS_statement {
    readonly original_position?: Source_Position;

    constructor(position?: Source_Position) {
        if (position) {
            this.original_position = position;
        }
    }

    compile_statement(): string { return `false;`; }
    possible_side_effect(): boolean { return true; }
    can_unroll(): boolean { return true; }
}

export class JS_expression extends JS_statement {
    constructor(position?: Source_Position) {
        super(position);
    }

    compile(): string { return `false`; }

    compile_statement(): string { return `${this.compile()};`; }

    possible_side_effect(): boolean { return true; }
}

export function JS_is_valid_alphanumeric(str: string) {
    if (str.length == 0)
        return false;
    const is_letter = (c: string = ''): boolean => 
        c == '_' || c == '$' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
    const is_number = (c: string = ''): boolean => 
        c >= '0' && c <= '9';
    
    if (!is_letter(str.charAt(0))) 
        return false;
    for (let char of str)
        if (!is_letter(char) && !is_number(char)) 
            return false;
    return true;
}

export class JS_codeblock_statement extends JS_statement {
    block: string;

    constructor(block: string, position?: Source_Position) {
        super(position);
        this.block = block;
    }

    compile_statement(): string {
        return '\n' + this.block + '\n';
    }
}

export class JS_object_expression extends JS_expression {
    properties: {[key: string]: JS_expression};

    constructor(properties: {[key: string]: JS_expression}, position?: Source_Position) {
        super(position);
        this.properties = properties;
    }

    compile(): string {
        const kv_expressions: string[] = [];
        for (let key in this.properties) {
            const property = this.properties[key].compile();
            if (JS_is_valid_alphanumeric(key)) {
                kv_expressions.push(`${key}: ${property}`);
            } else {
                kv_expressions.push(`${JSON.stringify(key)}: ${property}`);
            }
        }
        return `{${kv_expressions.join()}}`;
    }

    possible_side_effect(): boolean {
        for (let key in this.properties) {
            const prop = this.properties[key];
            if (prop === undefined || prop.possible_side_effect()) {
                return true;
            }
        }
        return false;
    }
}

export class JS_array_expression extends JS_expression {
    elements: JS_expression[];

    constructor(elements: JS_expression[], position?: Source_Position) {
        super(position);
        this.elements = elements;
    }

    compile(): string {
        const element_expressions = this.elements.map(e => e.compile());
        for (var i = 0; i < element_expressions.length; i++) if (element_expressions[i] === undefined)
            element_expressions[i] = 'undefined';
        return `[${element_expressions.join()}]`;
    }

    possible_side_effect(): boolean {
        return !!this.elements.find(e => e === undefined || e.possible_side_effect());
    }
}

export class JS_binary_operator_expression extends JS_expression {
    lhs: JS_expression;
    operator: string; 
    rhs: JS_expression;

    constructor(lhs: JS_expression, operator: string, rhs: JS_expression, position?: Source_Position) {
        super(position);
        this.lhs = lhs;
        this.operator = operator;
        this.rhs = rhs;
    }

    compile(): string {
        const lhs = this.lhs.compile();
        const rhs = this.rhs.compile();
        return `(${lhs} ${this.operator} ${rhs})`;
    }

    possible_side_effect() {
        return this.lhs.possible_side_effect() || this.rhs.possible_side_effect() || this.operator == '='
    }
}

export class JS_unary_operator_expression extends JS_expression {
    operator: string; 
    rhs: JS_expression;

    constructor(operator: string, rhs: JS_expression, position?: Source_Position) {
        super(position);
        this.operator = operator;
        this.rhs = rhs;
    }

    compile(): string {
        const rhs = this.rhs.compile();
        return `(${this.operator}${rhs})`;
    }

    possible_side_effect() {
        return this.rhs.possible_side_effect();
    }
}

export class JS_new_expression extends JS_expression {
    rhs: JS_expression;

    constructor(rhs: JS_expression, position?: Source_Position) {
        super(position);
        this.rhs = rhs;
    }

    compile(): string {
        const rhs = this.rhs.compile();
        return `new ${rhs}`;
    }

    possible_side_effect() { return true;}
}


export class JS_throw_expression extends JS_expression {
    rhs: JS_expression;

    constructor(rhs: JS_expression, position?: Source_Position) {
        super(position);
        this.rhs = rhs;
    }

    compile(): string {
        const rhs = this.rhs.compile();
        return `throw ${rhs}`;
    }

    possible_side_effect() { return true; }
}

export class JS_binding extends JS_expression {
    name: Name;
    binding: string;

    constructor(name: Name, binding: string, position?: Source_Position) {
        super(position);
        this.name = name;
        this.binding = binding;
    }

    compile(): string { return this.binding; }
    possible_side_effect(): boolean { return false; }
}

export class JS_reconstructable_binding extends JS_binding {
    object: Object;
    object_path: string[];
    reconstructor?: JS_object_reconstructor;

    constructor(name: Name, compiled: string, object: Object, path: string[], cons?: JS_object_reconstructor, position?: Source_Position) {
        super(name, compiled, position);
        this.object = object;
        this.object_path = path;
        this.reconstructor = cons;
    }

    compile(): string {
        if (!this.reconstructor || !this.reconstructor.lookup(this.object)) {
            return this.binding;
        }
        let expression = this.reconstructor.reconstructor_of(this.object);
        for (let property of this.object_path) {
            expression = new JS_property_access_expression(expression, property);
        }
        return expression.compile();
    }
}

export class JS_dynamic_statement extends JS_statement {
    _compile: () => string;

    constructor(compile: () => string, position?: Source_Position) {
        super(position);
        this._compile = compile;
    }

    compile_statement(): string {
        return this._compile();
    }
}

export class JS_dynamic_expression extends JS_expression {
    _compile: () => string;

    constructor(compile: () => string, position?: Source_Position) {
        super(position);
        this._compile = compile;
    }

    compile(): string {
        return this._compile();
    }
}

export class JS_plain_expression extends JS_expression {
    compiled: string;
    side_effect: boolean;

    constructor(compiled: string, side_effect: boolean, position?: Source_Position) {
        super(position);
        this.compiled = compiled;
        this.side_effect = side_effect;
    }

    compile(): string {
        return this.compiled;
    }

    possible_side_effect(): boolean {
        return this.side_effect;
    }
}

export class JS_stack_push_statement extends JS_statement {
    method: JS_expression;
    binding: JS_binding;

    constructor(method: JS_expression, bind: JS_binding, position: Source_Position) {
        super(position);
        this.method = method;
        this.binding = bind;
    }

    can_unroll() { return false; }
    compile_statement() {
        const _plain = (s: string) => new JS_plain_expression(s, false);

        const position = this.original_position as Source_Position;
        const push_expr = new JS_plain_expression('$poly.call_stack.push', false);
        const source_location = Runtime.instance.call_stack.make_source_location(
            position.name, position.line);
        const call = new JS_call_expression(push_expr, [
            this.method, 
            _plain(`${(source_location)}`)]);
        const decl = new JS_var_declartion_statement(
            'const', this.binding, call);
        return decl.compile_statement();
    }
}

export class JS_stack_pop_statement extends JS_statement {
    binding: JS_binding;

    constructor(binding: JS_binding, position?: Source_Position) {
        super(position);
        this.binding = binding;
    }
    
    can_unroll() { return false; }
    compile_statement() {
        const pop_expr = new JS_plain_expression('$poly.call_stack.pop', false);
        const call = new JS_call_expression(pop_expr, [this.binding]);
        return call.compile_statement();
    }
}

export const JS_undefined = new JS_plain_expression(`undefined`, false);
export const JS_true = new JS_plain_expression(`true`, false);
export const JS_false = new JS_plain_expression(`false`, false);

export class JS_property_access_expression extends JS_expression {
    lhs: JS_expression;
    rhs: string | number;

    constructor(lhs: JS_expression, rhs: string | number, position?: Source_Position) {
        super(position);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    compile(): string {
        let rhs: string | number = typeof this.rhs == 'string' ? parseInt(this.rhs, 10) : this.rhs;
        if (Number.isNaN(rhs)) {
            rhs = this.rhs;
        }
        if (typeof rhs == 'string') {
            if (JS_is_valid_alphanumeric(rhs)) {
                return `${this.lhs.compile()}.${rhs}`;
            }
            return `${this.lhs.compile()}[${JSON.stringify(rhs)}]`
        }
        return `${this.lhs.compile()}[${rhs}]`;
    }

    possible_side_effect(): boolean {
        return this.lhs.possible_side_effect();
    }
}

export class JS_index_expression extends JS_expression {
    lhs: JS_expression;
    rhs: JS_expression;

    constructor(lhs: JS_expression, rhs: JS_expression, position?: Source_Position) {
        super(position);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    compile(): string {
        return `${this.lhs.compile()}[${this.rhs.compile()}]`;
    }

    possible_side_effect(): boolean {
        return this.lhs.possible_side_effect();
    }
}

export class JS_call_expression extends JS_expression {
    method: JS_expression;
    parameters: JS_expression[];
    side_effect: boolean;

    constructor(method: JS_expression, parameters: JS_expression[], side_effect = true, position?: Source_Position) {
        super(position);
        this.method = method;
        this.parameters = parameters;
        this.side_effect = side_effect;
    }

    possible_side_effect() {
        return this.side_effect;
    }

    compile(): string {
        return `${this.method.compile()}(${this.parameters.map(p => p.compile()).join()})`;
    }
}

export class JS_assigment_expression extends JS_expression {
    lhs: JS_expression;
    rhs: JS_expression;

    constructor(lhs: JS_expression, rhs: JS_expression, position?: Source_Position) {
        super(position);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    compile(): string {
        return `${this.lhs.compile()} = ${this.rhs.compile()}`;
    }
}

export class JS_closure_expression extends JS_expression {
    parameters: JS_binding[];
    body: JS_statement;

    constructor(parameters: JS_binding[], body: JS_statement, position?: Source_Position) {
        super(position);
        this.parameters = parameters;
        this.body = body;
    }

    compile(): string {
        const parameters = this.parameters.map(p => p.compile()).join();
        return `(${parameters}) => {${this.body.compile_statement()}}`;
    }
}

export class JS_function_expression extends JS_closure_expression {
    name?: JS_binding

    constructor(parameters: JS_binding[], body: JS_statement, name?: JS_binding, position?: Source_Position) {
        super(parameters, body, position);
        this.name = name;
    }

    compile(): string {
        const parameters = this.parameters.map(p => p.compile()).join();
        const name = this.name ? this.name.compile() : '';
        return `function ${name}(${parameters}) {${this.body.compile_statement()}}`;
    }
}

export class JS_class_expression extends JS_expression {
    name: JS_binding;
    constructor_body: JS_statement;
    constructor_parameters: JS_binding[];
    extends_class?: JS_expression;

    constructor(name: JS_binding, constructor_body: JS_statement, constructor_parameters: JS_binding[], extends_class?: JS_expression, position?: Source_Position) {
        super(position);
        this.name = name;
        this.constructor_body = constructor_body;
        this.constructor_parameters = constructor_parameters;
        this.extends_class = extends_class;
    }

    compile(): string {
        const constructor_parameters = this.constructor_parameters.map(p => p.compile()).join();
        const constructor_body = this.constructor_body.compile_statement();
        const name = this.name.compile();
        const extends_class = this.extends_class ? `extends ${this.extends_class.compile()}` : '';
        return `class ${name} ${extends_class} {constructor(${constructor_parameters}) {${constructor_body}}}`;
    }
}

export class JS_return_statement extends JS_statement {
    expression: JS_expression;

    constructor(expression: JS_expression, position?: Source_Position) {
        super(position);
        this.expression = expression;
    }

    compile_statement(): string {
        return `return ${this.expression.compile()};`;
    }
}

export class JS_while_statement extends JS_statement {
    label?: JS_binding;
    test: JS_expression;
    body_stmt: JS_statement

    constructor(test: JS_expression, body_stmt: JS_statement, label?: JS_binding, position?: Source_Position) {
        super(position);
        this.label = label;
        this.test = test;
        this.body_stmt = body_stmt;
    }

    compile_statement(): string {
        const label = this.label ? `${this.label.compile()}: ` : ``;
        const test = this.test.compile();
        const body_stmt = this.body_stmt.compile_statement();
        return `${label}while(${test} !== false) {${body_stmt}}`;
    }
}

export class JS_try_catch_statement extends JS_statement {
    try_stmt: JS_statement;
    error_label: JS_binding;
    catch_stmt: JS_statement;
    finally_stmt?: JS_statement;

    constructor(try_stmt: JS_statement, error_label: JS_binding, catch_stmt: JS_statement, finally_stmt?: JS_statement, position?: Source_Position) {
        super(position);
        this.try_stmt = try_stmt;
        this.error_label = error_label;
        this.catch_stmt = catch_stmt;
        if (finally_stmt) this.finally_stmt = finally_stmt;
    }

    compile_statement(): string {
        const try_stmt = this.try_stmt.compile_statement();
        const error_label = this.error_label.compile();
        const catch_stmt = this.catch_stmt.compile_statement();
        const finally_stmt = this.finally_stmt ?
            this.finally_stmt.compile_statement() : undefined;
        return `try{${try_stmt}} catch(${error_label}) {${catch_stmt}}` +
            (finally_stmt ? ` finally ${finally_stmt}` : ``);
    }
}

export class JS_if_statement extends JS_statement {
    test: JS_expression;
    then_stmt: JS_statement;
    else_stmt: JS_statement; 

    constructor(test: JS_expression, then_stmt: JS_statement, else_stmt: JS_statement, position?: Source_Position) {
        super(position);
        this.test = test;
        this.then_stmt = then_stmt;
        this.else_stmt = else_stmt;
    }

    compile_statement(): string {
        const test = this.test.compile();
        const then_stmt = this.then_stmt.compile_statement();
        const else_stmt = this.else_stmt.compile_statement();
        return `if (${test} !== false) {${then_stmt}} else {${else_stmt}}`;
    }
}

export class JS_if_expression extends JS_expression {
    test: JS_expression;
    then_expr: JS_expression;
    else_expr: JS_expression; 

    constructor(test: JS_expression, then_expr: JS_expression, else_expr: JS_expression, position?: Source_Position) {
        super(position);
        this.test = test;
        this.then_expr = then_expr;
        this.else_expr = else_expr;
    }

    compile(): string {
        const test = this.test.compile();
        const then_expr = this.then_expr.compile();
        const else_expr = this.else_expr.compile();
        return `(${test} !== false ? ${then_expr} : ${else_expr})`;
    }
}

export class JS_body_statement extends JS_statement {
    body: JS_statement[];

    constructor(body: JS_statement[], position?: Source_Position) {
        super(position);
        this.body = body;
    }

    compile_statement(): string {
        return this.body.map(b => b.compile_statement()).join('');
    }
}

export type JS_var_kind = 'var' | 'let' | 'const'

export class JS_var_declartion_statement extends JS_statement {
    declaration_kind: JS_var_kind;
    name: JS_binding;
    expression: JS_expression;

    constructor(declaration_kind: JS_var_kind, name: JS_binding, expression: JS_expression, position?: Source_Position) {
        super(position);
        this.declaration_kind = declaration_kind;
        this.name = name;
        this.expression = expression;
    }

    compile_statement(): string {
        return `${this.declaration_kind} ${this.name.compile()} = ${this.expression.compile()};`;
    }
}

export class JS_symbol_mangler {
    indices: Map<string, Map<any, number>[]>;
    
    constructor() {
        this.indices = new Map();
    }

    _index(prefix: string, object: any, dimension: number): number {
        if (!this.indices.has(prefix))
        this.indices.set(prefix, []);
            const indices = this.indices.get(prefix) as Map<any, number>[];
        if (indices.length <= dimension)
            indices.push(new Map());
        let index = indices[dimension].get(object);
        if (index !== undefined) return index;
        index = indices[dimension].size + 1;
        indices[dimension].set(object, index);
        return index;
    }

    mangle(prefix: string, ...suffix: any[]) {
        const _prefix = prefix.
            replace('.', 'dot').
            replace('+', 'add').
            replace('-', 'sub').
            replace('=', 'eq').
            replace(':', 'col').
            replace('[', 'lbr').
            replace(/\W/g, '$');
        const _suffix = suffix.
            filter(k => k !== undefined).
            map((k, i) => '_' + this._index(_prefix, k, i).toString(16)).join('');
        return `${_prefix}${_suffix}`;
    }
}

export class JS_context {
    parent: JS_context | Module;
    bindings: Map<Name, JS_binding>;

    static symbols = new JS_symbol_mangler();
    static builtin_intrinsics: JS_intrinsic_method[];

    constructor(parent: JS_context | Module) {
        this.parent = parent;
        this.bindings = new Map();
    }

    get module(): Module {
        return this.parent instanceof Module ? 
            this.parent : this.parent.module;
    }

    mangled_binding(name: Name, ...suffix: any[]) {
        const mangled = JS_context.symbols.mangle(name.spelling, name.context, ...suffix);
        const binding = new JS_binding(name, mangled);
        this.bindings.set(name, binding);
        return binding;
    }

    temp_binding(hint: string): JS_binding {
        const name = Name.make(hint, new Macro_Context(this.module));
        const mangled = JS_context.symbols.mangle(name.spelling, name.context);
        const binding = new JS_binding(name, mangled);
        this.bindings.set(name, binding);
        return binding;
    }

    consume_definition(name: Name, defn: Definition) {
        const mangled = JS_context.symbols.mangle(name.spelling, name.context, defn);
        const binding = new JS_binding(name, mangled, defn.position);
        this.bindings.set(name, binding);
        return binding;
    }

    consume_scope(scope: Scope) {
        for (let [name, defn] of scope.definitions)
            this.consume_definition(name, defn);
    }

    consume_formal_parameters(formal_parameters: Formal_Parameters) {
        for (let param of formal_parameters.required)
            this.consume_definition(param.name, param);
        for (let param of formal_parameters.optional)
            this.consume_definition(param.name, param);
        for (let param of formal_parameters.named)
            this.consume_definition(param.name, param);
        if (formal_parameters.rest)
            this.consume_definition(formal_parameters.rest.name, formal_parameters.rest);
    }

    static from_scope(scope: Scope): JS_context {
        const path: Scope[] = [];
        let next: Scope | undefined = scope;
        while (next) {
            path.push(next);
            next = next.parent;
        }
        let context = new JS_context(path.pop() as Module);
        while (path.length > 0) {
            const next = path.pop() as Scope;
            context = new JS_context(context);
            context.consume_scope(next);
        }
        return context;
    }

    lookup(name: Name, reconstructor?: JS_object_reconstructor): JS_expression | undefined {
        if (this.bindings.has(name))
            return this.bindings.get(name) as JS_binding;
        if (this.parent instanceof JS_context)
            return this.parent.lookup(name, reconstructor);
        if (name.context instanceof Macro_Context)
            return JS_context.from_scope(name.context.parent_scope).
                lookup(Name.make(name), reconstructor);
        const module_definition = lookup(this.parent, name);
        if (!module_definition) return undefined;
        return new JS_reconstructable_binding(
            name, `$poly.lookup(${JSON.stringify(name.spelling)})`,
            module_definition, ['value'], reconstructor);
    }

    must_lookup(name: Name, reconstructor?: JS_object_reconstructor): JS_expression {
        const result = this.lookup(name, reconstructor)
        if (!result) 
            throw new Compilation_Error(`unknown reference ${JSON.stringify(name.spelling)}`);
        return result;
    }
}

export function JS_unroll_statement(body: JS_statement[], context: JS_context): void {
    let defer_index = body.length;
    for (var i = body.length - 1; i >= 0 && !body[i].can_unroll(); i--)
        defer_index = i;
    if (body.length == 0 || defer_index == 0)
        return;
    const defer = body.slice(defer_index);
    body.length = defer_index;
    const stmt = body[body.length - 1] as JS_statement;
    if (stmt instanceof JS_expression) {
        if (defer.length == 0) return;
        JS_unroll_statement_safe(body, context);
        const safe_stmt = body.pop() as JS_statement;
        body.push(...defer);
        body.push(safe_stmt);
        return;
    }
    if (stmt instanceof JS_if_statement) {
        body.pop();
        const temp = context.temp_binding('if');
        
        const then_stmt = new JS_body_statement([stmt.then_stmt]);
        JS_unroll_statement(then_stmt.body, context);

        const else_stmt = new JS_body_statement([stmt.else_stmt]);
        JS_unroll_statement(else_stmt.body, context);

        body.push(new JS_var_declartion_statement('let', temp, JS_undefined));
        then_stmt.body.push(new JS_assigment_expression(temp, then_stmt.body.pop() as JS_expression));
        else_stmt.body.push(new JS_assigment_expression(temp, else_stmt.body.pop() as JS_expression));

        body.push(new JS_if_statement(stmt.test, then_stmt, else_stmt, stmt.original_position));
        body.push(...defer);
        body.push(temp);
        return;
    }
    if (stmt instanceof JS_while_statement) {
        body.pop();
        const temp = context.temp_binding('while');
        const while_body = new JS_body_statement([stmt.body_stmt]);
        JS_unroll_statement(while_body.body, context);
        body.push(new JS_var_declartion_statement('let', temp, JS_undefined));
        while_body.body.push(new JS_assigment_expression(temp, while_body.body.pop() as JS_expression));
        body.push(new JS_while_statement(stmt.test, while_body, stmt.label, stmt.original_position));
        body.push(...defer);
        body.push(temp);
        return;
    }
    if (stmt instanceof JS_try_catch_statement) {
        body.pop();
        const temp = context.temp_binding('try');
        body.push(new JS_var_declartion_statement('let', temp, JS_undefined));
        
        const try_body = new JS_body_statement([stmt.try_stmt]);
        JS_unroll_statement(try_body.body, context);
        try_body.body.push(new JS_assigment_expression(temp, try_body.body.pop() as JS_expression));

        const catch_body = new JS_body_statement([stmt.catch_stmt]);
        JS_unroll_statement(catch_body.body, context);
        catch_body.body.push(new JS_assigment_expression(temp, catch_body.body.pop() as JS_expression));

        body.push(new JS_try_catch_statement(
            try_body, 
            stmt.error_label, 
            catch_body, 
            stmt.finally_stmt,
            stmt.original_position));
        body.push(...defer);
        body.push(temp);
        return
    }
    if (stmt instanceof JS_body_statement) {
        body.pop();
        if (stmt.body.length == 0) {
            body.push(...defer);
            body.push(JS_false);
            return;
        }
        for (let body_stmt of stmt.body) 
            body.push(body_stmt);
        body.push(...defer);
        return JS_unroll_statement(body, context);
    }
    if (stmt instanceof JS_var_declartion_statement) {
        body.push(...defer);
        body.push(stmt.name);
        return;
    }
    if (stmt instanceof JS_return_statement)  {
        throw new Error('cannot unroll return statement');
    }
    body.push(...defer);
}

export function JS_unroll_statement_safe(body: JS_statement[], ctx: JS_context, hint?: string | JS_binding): void {
    JS_unroll_statement(body, ctx);
    if (body[body.length - 1].possible_side_effect()) {
        const prep_final = body.pop() as JS_expression;
        const temp = hint ? (hint instanceof JS_binding ? hint : ctx.temp_binding(hint)) : ctx.temp_binding(`temp`);
        body.push(new JS_var_declartion_statement('const', temp, prep_final));
        body.push(temp);
    }
}

export function JS_optimize(stmt: JS_statement, visited: Set<JS_statement> = new Set()): JS_statement {
    if (visited.has(stmt)) {
        return stmt;
    }
    visited.add(stmt);
    if (stmt instanceof JS_body_statement) {
        const optimized_body = [];
        for (let body_stmt of stmt.body) {
            const optimized_stmt = JS_optimize(body_stmt, visited);
            if (optimized_stmt.possible_side_effect()) {
                optimized_body.push(optimized_stmt);
            }
        }
        if (optimized_body.length == 0) {
            return JS_false;
        }
        return new JS_body_statement(optimized_body, stmt.original_position);
    }
    if (stmt instanceof JS_if_statement) {
        const optimized_test = JS_optimize(stmt.test, visited) as JS_expression;
        const optimized_then = JS_optimize(stmt.then_stmt, visited);
        const optimized_else = JS_optimize(stmt.else_stmt, visited);

        if (optimized_then instanceof JS_expression && optimized_else instanceof JS_expression)
            return new JS_if_expression(
                optimized_test, optimized_then, optimized_else,
                stmt.original_position)

        return new JS_if_statement(
            optimized_test, optimized_then, optimized_else, 
            stmt.original_position);
    }
    if (stmt instanceof JS_while_statement) {
        const optimized_test = JS_optimize(stmt.test, visited) as JS_expression;
        const optimized_body = JS_optimize(stmt.body_stmt, visited);
        return new JS_while_statement(
            optimized_test,
            optimized_body,
            stmt.label,
            stmt.original_position);
    }
    if (stmt instanceof JS_try_catch_statement) {
        const optimized_try = JS_optimize(stmt.try_stmt, visited);
        const optimized_catch = JS_optimize(stmt.catch_stmt, visited);
        const optimized_finally = stmt.finally_stmt ?
            JS_optimize(stmt.finally_stmt, visited) : undefined;
        return new JS_try_catch_statement(
            optimized_try,
            stmt.error_label,
            optimized_catch,
            optimized_finally,
            stmt.original_position);
    }
    if (stmt instanceof JS_closure_expression) {
        const optimized_body = JS_optimize(stmt.body, visited);
        return new JS_closure_expression(
            stmt.parameters,
            optimized_body,
            stmt.original_position);
    }
    if (stmt instanceof JS_var_declartion_statement) {
        return new JS_var_declartion_statement(
            stmt.declaration_kind,
            stmt.name,
            JS_optimize(stmt.expression, visited) as JS_expression,
            stmt.original_position)
    }
    if (stmt instanceof JS_call_expression) {
        return new JS_call_expression(
            JS_optimize(stmt.method, visited) as JS_expression,
            stmt.parameters.map(p => JS_optimize(p, visited) as JS_expression),
            stmt.side_effect,
            stmt.original_position);
    }
    if (stmt instanceof JS_assigment_expression) {
        const assigment = new JS_assigment_expression(
            JS_optimize(stmt.lhs, visited) as JS_expression,
            JS_optimize(stmt.rhs, visited) as JS_expression,
            stmt.original_position);
        if (stmt.rhs instanceof JS_throw_expression)
            return stmt.rhs;
        return assigment;
    }
    if (stmt instanceof JS_return_statement) {
        if (stmt.expression instanceof JS_throw_expression)
            return stmt.expression;
    }
    if (stmt instanceof JS_object_expression) {
        const properties: any = {};
        for (let key in stmt.properties)
            properties[key] = JS_optimize(stmt.properties[key], visited) as JS_expression;
        return new JS_object_expression(properties, stmt.original_position);
    }
    if (stmt instanceof JS_array_expression) {
        return new JS_array_expression(
            stmt.elements.map(e => JS_optimize(e, visited) as JS_expression),
            stmt.original_position);
    }
    return stmt;
}

export function JS_compile(expr: Expression | undefined, context: JS_context, reconstructor: JS_object_reconstructor): JS_statement {
    try {
        return _JS_compile(expr, context, reconstructor);
    } catch(e) {
        if (e instanceof Poly_Error && !e.position && expr instanceof Compound_Expression)
            e.position = expr.position;
        throw e;
    }
}

export function _JS_compile(expr: Expression | undefined, context: JS_context, reconstructor: JS_object_reconstructor): JS_statement {
    switch (typeof expr) {
    case 'undefined':
        return JS_false;
    case 'boolean':
        return expr ? JS_true : JS_false;
    case 'number':
        return new JS_plain_expression(`${expr}`, false);
    case 'string':
        return new JS_plain_expression(`${JSON.stringify(expr)}`, false);
    }
    if (expr instanceof Char) {
        return reconstructor.reconstructor_of(expr);
    }
    if (expr instanceof Name) {
        const name = context.lookup(expr, reconstructor)
        if (!name) 
            throw new Compilation_Error(`unknown reference ${JSON.stringify(expr.spelling)}`);
        return name;
    }
    if (expr instanceof Quotation) {
        return reconstructor.reconstructor_of(expr.datum);
    }
    if (expr instanceof Block_Scope) {
        const body_context = JS_context.from_scope(expr);

        let should_use_parent_reconstructor = true;
        let scope: Scope | undefined = expr
        while (scope) {
            if (scope instanceof Formal_Parameter_Scope) {
                should_use_parent_reconstructor = false;
                break;
            }
            scope = scope.parent;
        }   
        if (reconstructor.environment == Method_Environment.Isolated)
            should_use_parent_reconstructor = false;

        const body_reconstructor = should_use_parent_reconstructor ? 
            reconstructor : 
            new JS_object_reconstructor(body_context, reconstructor.mapper, reconstructor);
        const body = new JS_body_statement(should_use_parent_reconstructor ? [] : body_reconstructor.init_statements);
        for (let body_expr of expr.expressions) {
            body.body.push(JS_compile(body_expr, body_context, body_reconstructor));
        }
        return body;
    }
    if (expr instanceof Prog_Expression) {
        const body = new JS_body_statement([]);
        for (let body_expr of expr.expressions) {
            body.body.push(JS_compile(body_expr, context, reconstructor));
        }
        return body;
    }
    if (expr instanceof If_Expression) {
        const test_stmt = JS_compile(expr.test, 
            context, reconstructor);
        const then_body = JS_compile(expr.consequent, 
            context, reconstructor);
        const else_body = JS_compile(expr.alternate, 
            context, reconstructor);
        
        const prep = [test_stmt];
        JS_unroll_statement(prep, context);
        const test_expr = prep.pop() as JS_expression;

        if (then_body instanceof JS_expression && else_body instanceof JS_expression) {
            prep.push(new JS_if_expression(test_expr, then_body, else_body, expr.position));
            return prep.length > 1 ? new JS_body_statement(prep) : prep[0];
        }

        prep.push(new JS_if_statement(test_expr, then_body, else_body, expr.position));
        return prep.length > 1 ? new JS_body_statement(prep) : prep[0];
    }
    if (expr instanceof Call_Expression) {
        return JS_compile_call_expression(expr, context, reconstructor);
    }
    if (expr instanceof Assigment_Expression) {
        const prep = [JS_compile(expr.rhs, context, reconstructor)];
        JS_unroll_statement(prep, context);
        prep.push(new JS_assigment_expression(
            context.must_lookup(expr.lhs, reconstructor), 
            prep.pop() as JS_expression));
        return prep.length > 1 ? new JS_body_statement(prep) : prep[0];
    }
    if (expr instanceof Unresolved_Generic_Parameter_Definition) {
        // ?
        return JS_undefined;
    }
    if (expr instanceof Known_Definition) {
        if (context.parent instanceof JS_context)
            context.consume_definition(expr.name, expr);
        const binding = context.must_lookup(expr.name);
        const defn: JS_statement[] = [reconstructor.reconstructor_of(expr.value)];
        JS_unroll_statement(defn, context);
        if (binding instanceof JS_binding && context.parent instanceof JS_context)
            defn.push(new JS_var_declartion_statement(
                'const', binding, 
                defn.pop() as JS_expression,
                expr.position));
        return defn.length > 1 ? new JS_body_statement(defn) : defn[0];
    }
    if (expr instanceof Constant_Definition || expr instanceof Variable_Definition) {
        const defn = expr.value !== undefined ? 
            [reconstructor.reconstructor_of(expr.value)]
            :
            [JS_compile(expr.expression, context, reconstructor)];
        if (context.parent instanceof JS_context)
            context.consume_definition(expr.name, expr);
        const binding = context.must_lookup(expr.name);
        JS_unroll_statement(defn, context);
        if (binding instanceof JS_binding && context.parent instanceof JS_context) 
            defn.push(new JS_var_declartion_statement(
                expr instanceof Variable_Definition ? 'let' : 'const', binding, 
                defn.pop() as JS_expression));
        else defn.push(new JS_assigment_expression(
            new JS_property_access_expression(reconstructor.reconstructor_of(expr), 'value'), 
            defn.pop() as JS_expression));
        return defn.length > 1 ? new JS_body_statement(defn) : defn[0];
    }
    if (expr instanceof Method_Expression) {
        const datum = method_expression_to_datum(expr);
        return reconstructor.reconstructor_of(datum);
    }
    if (expr instanceof Instance_Expression) {
        const prep: JS_statement[] = [];
        const params = expr.expressions.map((p, i) => {
            prep.push(JS_compile(p, context, reconstructor));
            JS_unroll_statement_safe(prep, context, `arg_${i}`);
            return prep.pop() as JS_expression;
        });
        if (expr.bundle.class?.generic_instance?.generic_class.name?.spelling == 'internal_array') {
            const elements = new JS_array_expression(params as JS_expression[]);
            prep.push(new JS_call_expression(
                new JS_new_expression(reconstructor.reconstructor_of(Internal_Array)), 
                [reconstructor.reconstruction_of_instance_bundle(expr.bundle), elements]));
            return prep.length > 1 ? new JS_body_statement(prep) : prep[0];
        }
        const jsclass = JS_generate_class_prototype(expr.bundle, context.module, reconstructor.mapper);
        prep.push(new JS_call_expression(
            new JS_property_access_expression(new JS_plain_expression(`new $poly.objmap`, false), jsclass.key), 
            [...params as JS_expression[]]));
        return prep.length > 1 ? new JS_body_statement(prep) : prep[0];
    }
    if (expr instanceof Slot_Read_Expression) {
        const slot = expr.bundle.class?.slots.find(slot => slot.name == expr.slot) as Slot_Specifier;
        const prep = [JS_compile(expr.lhs, context, reconstructor)];
        JS_unroll_statement(prep, context);
        const property = JS_context.from_scope(context.module).
            mangled_binding(slot.name, slot.root_origin).compile();
        prep.push(new JS_property_access_expression(prep.pop() as JS_expression, property));
        return prep.length > 1 ? new JS_body_statement(prep) : prep[0];
    }
    if (expr instanceof Slot_Write_Expression) {
        const slot = expr.bundle.class?.slots.find(slot => slot.name == expr.slot) as Slot_Specifier;
        const prep = [JS_compile(expr.lhs, context, reconstructor)];
        JS_unroll_statement(prep, context);
        const lhs = prep.pop() as JS_expression;
        
        prep.push(JS_compile(expr.rhs, context, reconstructor));
        const rhs = prep.pop() as JS_expression;

        const property_expr = JS_context.from_scope(context.module).
            mangled_binding(slot.name, slot.root_origin).compile();
        const property_access_expr = new JS_property_access_expression(lhs, property_expr);
        const property_assigment = new JS_assigment_expression(
            property_access_expr,
            rhs,
            expr.position);

        prep.push(property_assigment);
        return prep.length > 1 ? new JS_body_statement(prep) : prep[0];
    }
    if (expr instanceof Exit_Expression) {
        const exit_tag = reconstructor.reconstructor_of(
            JS_context.symbols.mangle('exit', expr));
        const err_binding = context.temp_binding('err');
        const catch_stmt = new JS_body_statement([
            new JS_if_statement(
                new JS_binary_operator_expression(
                    new JS_binary_operator_expression(
                        err_binding, 
                        'instanceof', 
                        reconstructor.reconstructor_of(JS_early_exit)),
                    '&&',
                    new JS_binary_operator_expression(
                        new JS_property_access_expression(err_binding, 'tag'),
                        '==',
                        exit_tag,
                    )),
            new JS_property_access_expression(err_binding, 'value'),
            new JS_throw_expression(err_binding)),
        ], expr.position);
        const try_catch = new JS_try_catch_statement(
            JS_compile(expr.expression, context, reconstructor),
            err_binding,
            catch_stmt,
            undefined,
            expr.position);
        return try_catch;
    }
    if (expr instanceof Exit_Call_Expression) {
        const exit_tag = reconstructor.reconstructor_of(
            JS_context.symbols.mangle('exit', expr.exit));
        
        const prep: JS_statement[] = [];
        prep.push(JS_compile(expr.expression, context, reconstructor));
        JS_unroll_statement(prep, context);
        const exit_expr = prep.pop() as JS_expression;

        const eary_exit_obj_expr = new JS_new_expression(
            new JS_call_expression(
                reconstructor.reconstructor_of(JS_early_exit),
                [exit_tag, exit_expr]));
        prep.push(new JS_throw_expression(eary_exit_obj_expr));
        return prep.length > 1 ? new JS_body_statement(prep) : prep[0];
    }
    throw new Error('unknown expression');
}

export class JS_early_exit {
    tag: string;
    value: Datum;

    constructor(tag: string, value: Datum) { 
        this.tag = tag;
        this.value = value; 
    }
}

export function JS_compile_method(method_id: number, reconstructor: JS_object_reconstructor) {
    const $poly = Runtime.instance;
    const expr = $poly.method_expressions[method_id];
    if (!expr) return;

    const datum = $poly.method_datums[method_id];
    if (!Array.isArray(datum.lambda)) datum.lambda = [];
    
    // hacky-flag for reconstructor, important for recursion-related corner cases 
    (datum.lambda[reconstructor.environment] as any) = null; 

    const scope = expr.formal_parameters.scope;
    // if (reconstructor.environment == Method_Environment.Integrated)
    //    optimize(Typer_Context.from_scope(scope), expr, scope);

    const parameters_context = JS_context.from_scope(scope);
    parameters_context.consume_formal_parameters(expr.formal_parameters);
    const parameters: JS_expression[] = [];
    for (let param of expr.formal_parameters.required)
        parameters.push(parameters_context.must_lookup(param.name));
    for (let param of expr.formal_parameters.optional) 
        parameters.push(parameters_context.must_lookup(param.name));
    for (let param of expr.formal_parameters.named) 
        parameters.push(parameters_context.must_lookup(param.name));
    if (expr.formal_parameters.rest) 
        parameters.push(parameters_context.must_lookup(expr.formal_parameters.rest.name));
    const body_reconstructor = new JS_object_reconstructor(parameters_context, reconstructor.mapper, reconstructor);
    const body = JS_compile(expr.body, parameters_context, body_reconstructor);
    const body_prep: JS_statement[] = [];

    const generic_parameter_scope_body: JS_statement[] = [];
    for (let gscope = scope; gscope.parent; gscope = gscope.parent as Scope) 
        if (gscope instanceof Generic_Parameter_Scope) for (let defn of gscope.definitions.values())
            generic_parameter_scope_body.push(JS_compile(defn, parameters_context, body_reconstructor));

    body_prep.push(...body_reconstructor.init_statements);
    body_prep.push(...generic_parameter_scope_body);
    body_prep.push(body);
    JS_unroll_statement(body_prep, parameters_context);
    body_prep.push(new JS_return_statement(body_prep.pop() as JS_expression));

    const closure = JS_optimize(new JS_closure_expression(
        parameters.filter(p => p instanceof JS_binding) as JS_binding[],
        body_prep.length > 1 ? 
            new JS_body_statement(body_prep) : body_prep[0],
        expr.position));
    datum.lambda[reconstructor.environment] = closure;
}

export function JS_generate_class_prototype(bundle: Bundle, module: Module, mapper: JS_object_mapper, reconstructor?: JS_object_reconstructor) {
    const jsclass = mapper.compiled_prototype_key(bundle);
    if (jsclass) return jsclass;

    reconstructor = reconstructor ? 
        reconstructor : isolated_reconstructor(module);
    
    const class_context = JS_context.from_scope(module);
    const class_reconstructor = new JS_object_reconstructor(
        JS_context.from_scope(class_context.module), 
        mapper, reconstructor);

    const name = bundle.name ? 
        class_context.mangled_binding(bundle.name, bundle) : 
        class_context.temp_binding('class');

    const nature = bundle.class as Class_Nature;

    const slot_binding = (slot: Slot_Specifier) => class_context.mangled_binding(slot.name, slot.root_origin);
    const multislot_type_expr = (slot_type: Datum) => {
        return class_reconstructor.reconstruction_of_instance_bundle(slot_type as Bundle);
    }

    const constructor_parameters = nature.slots.map(slot => slot_binding(slot));
    const member_from_arg = (slot: Slot_Specifier) => new JS_assigment_expression(
        new JS_property_access_expression(
            new JS_plain_expression('this', false), slot_binding(slot).compile()), 
            slot.multislot ?
                new JS_call_expression(
                    new JS_new_expression(class_reconstructor.reconstructor_of(Internal_Array)),
                    [multislot_type_expr(slot.type), slot_binding(slot)])
                : slot_binding(slot));
    const constructor_body = new JS_body_statement(
        [...nature.slots.map(member_from_arg)]);

    if (Runtime.instance.instance_bundles.findIndex(b => b == bundle) != -1) {
        const access = class_reconstructor.reconstruction_of_instance_bundle(bundle);
        class_reconstructor.reconstruction_by_property_access(bundle, access);
    }
    const datum_spec = new Host_Datum_Spec(
        bundle,
        constructor_parameters.map(param => [param.name, param.compile()]));
    const datum_spec_expression = class_reconstructor.reconstructor_of(datum_spec);
    constructor_body.body.unshift(new JS_call_expression(
        new JS_plain_expression('super', false), 
        [datum_spec_expression], false));

    const js_class_expression = new JS_class_expression(
        name,
        constructor_body,
        constructor_parameters,
        class_reconstructor.reconstructor_of(Host_Datum));
    const statement = new JS_body_statement([
        ...class_reconstructor.init_statements, js_class_expression]);
    return mapper.compile_prototype(bundle, statement, name.compile());
}

export function JS_compile_call_expression(expr: Call_Expression, context: JS_context, reconstructor: JS_object_reconstructor): JS_statement {
    const compile_parameters = (prep: JS_statement[]) => {
        const parameters = expr.parameters.map(p => JS_compile(p, context, reconstructor));
        let unroll_index = parameters.findIndex(p => !(p instanceof JS_expression));
        const result: JS_expression[] = [];
        if (unroll_index == -1)
            unroll_index = parameters.length;
        for (var i = 0; i < unroll_index; i++)
            result.push(parameters[i] as JS_expression);
        for (var i = unroll_index; i < parameters.length; i++) {
            prep.push(parameters[i]);
            JS_unroll_statement_safe(prep, context, `arg_${i}`);
            result.push(prep.pop() as JS_expression);
        }
        return result;
    }

    const optimized_intrinsic = (head: Runtime_Method_Head) => {
        if (!head.intrinsic || expr.spread) return undefined;
        main: for (let imethod of JS_context.builtin_intrinsics) {
            if (imethod.name != head.name) continue;
            if (head.positional.length != imethod.required.length + imethod.optional.length) continue;
            if ((head.named?.size || 0) != imethod.named.size) continue;
            if (imethod.rest && !is_subtype_or_equal(head.rest, imethod.rest)) continue;
            for (var i = 0; i < imethod.required.length; i++) 
                if (!is_subtype_or_equal(head.positional[i], imethod.required[i])) continue main;
            for (var i = 0; i < imethod.optional.length; i++) 
                if (!is_subtype_or_equal(head.positional[i + head.required_count], imethod.optional[i])) continue main;
            // TODO named
            return imethod.builder(expr.parameters, context, reconstructor);
        }
        return undefined;
    }

    const optimized_direct_lambda_call = (method: Runtime_Method_Datum, head: Runtime_Method_Head) => {
        if (head.named || head.rest) return undefined;
        const lhs_method_expr = reconstructor.reconstructor_of(method);
        const lhs = new JS_property_access_expression(
            lhs_method_expr, 'lambda', expr.position);
        const prep: JS_statement[] = [];
        const stack_temp = context.temp_binding('stackid');
        const parameters = compile_parameters(prep);
        prep.push(new JS_stack_push_statement(lhs_method_expr, stack_temp, expr.position));
        const call = new JS_call_expression(lhs, parameters, true, expr.position);
        prep.push(call);
        prep.push(new JS_stack_pop_statement(stack_temp));
        return prep.length > 1 ? new JS_body_statement(prep) : prep[0];
    }

    const optimized_tail_call = (method: Runtime_Method_Datum, head: Runtime_Method_Head, method_expr: Method_Expression) => {
        if (!method_expr || (head.optional_count > 0 || head.rest || head.named)) return undefined;
        const recursive_call = (call: Expression) => 
            call instanceof Call_Expression &&
            ((call.method instanceof Quotation && 
                call.method.datum instanceof Runtime_Method_Datum &&  
                call.method.datum.id == method.id) || 
                (call.method instanceof Method_Expression &&
                Runtime.instance.method_expressions[method.id] == call.method));
        const recursive_node = (expr: Expression): boolean => {
            if (expr instanceof Call_Expression) 
                if (recursive_call(expr)) return true;
                else if (recursive_node(expr.method)) return true;
                else for (let p of expr.parameters)
                    if (recursive_node(p)) return true;
            if (expr instanceof If_Expression) 
                if (recursive_node(expr.test)) return true;
                else if (recursive_node(expr.consequent)) return true;
                else if (recursive_node(expr.alternate)) return true;
            if (expr instanceof Prog_Expression)
                for (let e of expr.expressions)
                    if (recursive_node(e)) return true;
            if (expr instanceof Block_Scope)
                for (let e of expr.expressions)
                    if (recursive_node(e)) return true;
            if (expr instanceof Exit_Expression)
                return recursive_node(expr.expression);
            if (expr instanceof Exit_Call_Expression)
                return recursive_node(expr.expression);
            if (expr instanceof Constant_Definition)
                return recursive_node(expr.expression);
            if (expr instanceof Variable_Definition)
                return recursive_node(expr.expression);
            if (expr instanceof Assigment_Expression)
                return recursive_node(expr.rhs);
            if (expr instanceof Slot_Write_Expression)
                return recursive_node(expr.rhs);
            if (expr instanceof Instance_Expression)
                for (let e of expr.expressions)
                    if (recursive_node(e)) return true;
            return false;
        }
        const compile_parameters = (body: JS_statement[], expr: Call_Expression, formal: Formal_Parameters, repeat: boolean) => {
            for (var i = 0; i < expr.parameters.length; i++) {
                const param_defn = formal.required[i];
                const param = expr.parameters[i];
                body.push(JS_compile(param, context, reconstructor));
                JS_unroll_statement(body, context);
                const param_expr = body.pop() as JS_expression;
                if (!repeat) {
                    const binding = context.consume_definition(param_defn.name, param_defn);
                    const decl = new JS_var_declartion_statement(
                        'let', binding, param_expr);
                    body.push(decl);
                } else {
                    const binding = context.lookup(param_defn.name);
                    const assigment = new JS_assigment_expression(binding as JS_expression, param_expr);
                    body.push(assigment);
                }
            }
        }
        const is_false = (expr: Expression) => 
            expr instanceof Quotation && expr.datum == false;
        const copied = new Map();
        for (let m of Runtime.instance.method_expressions)
            if (m) copied.set(m, m); // ughm...
        const formal = copy_formalparameters(method_expr.formal_parameters, copied);
        const method_body = copy_expression(method_expr.body, copied);
        const body_tail = tail_expression(method_body);
        if (body_tail instanceof If_Expression) {
            const consequent_tail = tail_expression(body_tail.consequent);
            if (recursive_call(consequent_tail) && is_false(body_tail.alternate) && consequent_tail instanceof Call_Expression) {
                let method_body_prep = cut_tail(method_body) as Expression;
                const while_prep: JS_statement[] = [];
                compile_parameters(while_prep, expr, formal, false);
                if (method_body_prep) 
                    while_prep.push(JS_compile(method_body_prep, context, reconstructor));
                const test_prep = [JS_compile(body_tail.test, context, reconstructor)];
                const test_var_needed = !(test_prep[0] instanceof JS_expression);
                JS_unroll_statement(test_prep, context);
                const test_expr = test_prep.pop() as JS_expression;
                const test_bind = test_var_needed ? context.temp_binding('test') : undefined;

                while_prep.push(...test_prep);
                if (test_bind) while_prep.push(new JS_var_declartion_statement(
                    'let', test_bind, test_expr));

                const test_cycle_expr = test_bind ? test_bind : test_expr;

                const body = new JS_body_statement([]);
                const consequent_prep = cut_tail(body_tail.consequent) as Expression;
                if (consequent_prep)
                    body.body.push(JS_compile(consequent_prep, context, reconstructor));
                    
                compile_parameters(body.body, consequent_tail, formal, true);

                if (test_bind) {
                    JS_unroll_statement_safe(body.body, context, context.temp_binding('cycle'));
                    const body_final = body.body.pop() as JS_expression;
                    body.body.push(...test_prep);
                    body.body.push(new JS_assigment_expression(test_bind, test_expr));
                    body.body.push(body_final);
                }
                
                const while_stmt = new JS_while_statement(test_cycle_expr, body);
                while_prep.push(while_stmt);
                return while_prep.length > 1 ? new JS_body_statement(while_prep) : while_prep[0];
            }
        }
        return undefined;
    }

    let method: Runtime_Method_Datum | undefined = undefined;
    if (expr.method instanceof Quotation && expr.method.datum instanceof Runtime_Method_Datum)
        method = expr.method.datum;
    if (expr.method instanceof Method_Expression)
        method = method_expression_to_datum(expr.method);

    if (method) {
        const method_id = method.id;
        const head = Runtime.instance.method_heads[method_id];
        const method_expr = Runtime.instance.method_expressions[method_id];

        let optimized = undefined;
        
        optimized = optimized_intrinsic(head); 
        if (optimized) return optimized;

        optimized = optimized_tail_call(method, head, method_expr)
        if (optimized) return optimized;

        if (reconstructor.environment == Method_Environment.Integrated) {
            optimized = optimized_direct_lambda_call(method, head)
            if (optimized) return optimized;
        }
    }

    const method_stmt = JS_compile(expr.method, context, reconstructor);

    const prep = [method_stmt];
    JS_unroll_statement_safe(prep, context, `fn`);
    const method_expr = prep.pop() as JS_expression;
    const parameters = compile_parameters(prep);
    
    const _plain = (s: string) => new JS_plain_expression(s, false);
    const source_location = Runtime.instance.call_stack.make_source_location(
        expr.position.name, expr.position.line);
    
    prep.push(new JS_call_expression(
        new JS_plain_expression(expr.spread ? '$poly.spread_call' : '$poly.call', false), 
        [_plain(`${source_location}`), method_expr,...parameters]));
    return prep.length > 1 ? new JS_body_statement(prep) : prep[0];
}

export type JS_intrinsic_builder = 
    (params: Expression[], context: JS_context, reconstructor: JS_object_reconstructor) => JS_statement;

export class JS_intrinsic_method {
    name: Name;
    required: Type[];
    optional: Type[];
    named: Map<Name, Type>;
    rest?: Type;
    result: Datum;
    builder: JS_intrinsic_builder;

    constructor(
        name: Name,
        required: Type[],
        optional: Type[],
        named: Map<Name, Type>,
        rest: Type | undefined,
        result: Datum,
        builder: JS_intrinsic_builder) {
            this.name = name;
            this.required = required;
            this.optional = optional;
            this.named = named;
            this.rest = rest;
            this.result = result;
            this.builder = builder;
        }
}


export function JS_builtin_intrinsic_methods($poly: Runtime): JS_intrinsic_method[] {
    const methods: JS_intrinsic_method[] = []

    const name = (spelling: string) => Name.make(spelling);

    const bundle = (name: Name) => {
        let defn = lookup($poly.modules as Module, name) as any;
        return defn.value as Bundle;   
    }

    type method_head = {
        required: Datum[], 
        optional: Datum[], 
        named: Map<Name, Datum>, 
        result: Datum, 
        rest?: Datum
    };

    const method = (n: Name, head: method_head, builder: JS_intrinsic_builder) => {
        methods.push(new JS_intrinsic_method(
            n, head.required, head.optional, head.named, head.rest, head.result,
            builder));
    }

    const method_head = (result: Datum, required: Datum[], optional?: Datum[], named?: Map<Name, Datum>, rest?: Datum) => {
        const dename = (r: Datum) => r instanceof Name ? bundle(r) : r;
        return {
            result: dename(result),
            required: required.map((r) => dename(r)), 
            optional: optional ? optional.map((r) => dename(r)) : [], 
            named: named ? new Map(Array.from(named.entries()).
                map(e => [e[0], dename(e[1])])) : new Map(), 
            rest: rest ? dename(rest) : undefined,
        };
    }

    const binary_operator: (op: string) => JS_intrinsic_builder = (op) => (params, context, reconstructor) => {
        const prep: JS_statement[] = [];
        prep.push(JS_compile(params[0], context, reconstructor));
        JS_unroll_statement(prep, context);
        const lhs = prep.pop() as JS_expression;

        prep.push(JS_compile(params[1], context, reconstructor));
        JS_unroll_statement(prep, context);
        const rhs = prep.pop() as JS_expression;

        prep.push(new JS_binary_operator_expression(lhs, op, rhs))
        return prep.length > 1 ? new JS_body_statement(prep) : prep[0];
    }

    const unary_operator: (op: string) => JS_intrinsic_builder = (op) => (params, context, reconstructor) => {
        reconstructor.init_statements.push(JS_compile(params[0], context, reconstructor));
        JS_unroll_statement(reconstructor.init_statements, context);
        const rhs = reconstructor.init_statements.pop() as JS_expression;

        return new JS_unary_operator_expression(op, rhs);
    }

    type Baked_Builder = (params: JS_expression[], context: JS_context, reconstructor: JS_object_reconstructor) => JS_statement;
    const baked_expressions: (builder: Baked_Builder, begin?: number, end?: number) => JS_intrinsic_builder = (builder, begin, end) => (params, context, reconstructor) => {
        const prep: JS_statement[] = [];
        const baked: JS_expression[] = [];
        for (var i = 0; i < params.length; i++) {
            if (begin !== undefined && i < begin) continue;
            if (end !== undefined && i >= end) continue;
            prep.push(JS_compile(params[i], context, reconstructor));
            JS_unroll_statement_safe(prep, context);
            baked.push(prep.pop() as JS_expression);
        }
        const stmt = builder(baked, context, reconstructor);
        prep.push(stmt);
        return prep.length > 1 ? new JS_body_statement(prep) : prep[0];
    }

    const _new = (expr: JS_expression) =>
        new JS_new_expression(expr);
    const _call = (method: JS_expression, params: JS_expression[]) =>
        new JS_call_expression(method, params);
    const _prop = (lhs: JS_expression, key: string | number) =>
        new JS_property_access_expression(lhs, key);
    const _plain = (e: string, side_effect = false) =>
        new JS_plain_expression(e, side_effect);
    const _binary = (lhs: JS_expression, op: string, rhs: JS_expression) =>
        new JS_binary_operator_expression(lhs, op, rhs);
    const _unary = (rhs: JS_expression, op: string) =>
        new JS_unary_operator_expression(op, rhs);
    // const _ifexpr = (test: JS_expression, then_expr: JS_expression, else_expr: JS_expression) =>
    //    new JS_if_expression(test, then_expr, else_expr);
    const _index = (lhs: JS_expression, rhs: JS_expression) => 
        new JS_index_expression(lhs, rhs);

    method(name('+'), 
        method_head(name('number'), [name('number'), name('number')]),
        binary_operator('+'));
    method(name('+'), 
        method_head(name('string'), [name('string'), name('string')]),
        binary_operator('+'));
    method(name('+'), 
        method_head(name('number'), [name('number')]),
        baked_expressions(params => params[0]));

    
    method(name('-'), 
        method_head(name('number'), [name('number'), name('number')]),
        binary_operator('-'));
    method(name('-'), 
        method_head(name('number'), [name('number')]),
        unary_operator('-'));

    method(name('*'), 
        method_head(name('number'), [name('number'), name('number')]),
        binary_operator('*'));
    
    method(name('/'), 
        method_head(name('integer'), [name('integer'), name('integer')]),
        baked_expressions((params) => 
            _call(_plain('Math.floor'), [_binary(params[0], '/', params[1])])));
    method(name('/'), 
        method_head(name('number'), [name('float'), name('number')]),
        binary_operator('/'));
    method(name('/'), 
        method_head(name('number'), [name('number'), name('float')]),
        binary_operator('/'));

    method(name('mod'), 
        method_head(name('integer'), [name('number'), name('number')]),
        binary_operator('%'));

    method(name('&'), 
        method_head(name('number'), [name('number'), name('number')]),
        binary_operator('&'));

    method(name('|'), 
        method_head(name('number'), [name('number'), name('number')]),
        binary_operator('|'));

    method(name('~'), 
        method_head(name('number'), [name('number'), name('number')]),
        binary_operator('^'));

    method(name('eq'), 
        method_head(name('boolean'), [name('everything'), name('everything')]),
        binary_operator('==='));

    method(name('>>'), 
        method_head(name('number'), [name('number'), name('number')]),
        binary_operator('>>'));
    method(name('<<'), 
        method_head(name('number'), [name('number'), name('number')]),
        binary_operator('<<'));

    method(name('='), 
        method_head(name('boolean'), [name('number'), name('number')]),
        binary_operator('=='));
    method(name('='), 
        method_head(name('boolean'), [name('string'), name('string')]),
        binary_operator('=='));
    method(name('='), 
        method_head(name('boolean'), [name('character'), name('character')]),
        baked_expressions(params =>
            _binary(_prop(params[0], 'code'), '==', _prop(params[1], 'code'))));

    method(name('<'), 
        method_head(name('boolean'), [name('number'), name('number')]),
        binary_operator('<'));

    method(name('<='), 
        method_head(name('boolean'), [name('number'), name('number')]),
        binary_operator('<='));

    method(name('>'), 
        method_head(name('boolean'), [name('number'), name('number')]),
        binary_operator('>'));

    method(name('>='), 
        method_head(name('boolean'), [name('number'), name('number')]),
        binary_operator('>='));

    method(name('not'), 
        method_head(name('boolean'), [name('everything')]),
        baked_expressions(params =>
            _binary(params[0], '===', _plain('false'))));

    method(name('internal_list'),
        method_head(name('internal_list'), []),
        () => _plain('[]'));
    method(name('append!'),
        method_head(name('everything'), [
            name('internal_list')], 
            [], new Map(), 
            name('everything')),
        baked_expressions((params) => 
            _call(_prop(params[0], 'push'), params.slice(1))));

    method(name('internal_array_length'),
        method_head(name('everything'), [name('everything')]),
        baked_expressions((params) => _prop(params[0], 'length'), 0, 1));
    method(name('internal_array_element_get'),
        method_head(name('everything'), [name('everything'), name('everything')]),
        baked_expressions((params) => _index(_prop(params[0], 'array'), params[1])));
    method(name('internal_array_element_set'),
        method_head(name('everything'), [name('everything'), name('everything'), name('everything')]),
        baked_expressions((params) => _binary(_index(_prop(params[0], 'array'), params[1]), '=', params[2])));

    method(name('internal_string_length'),
        method_head(name('everything'), [name('everything')]),
        baked_expressions((params) => _prop(params[0], 'length'), 0, 1));
    method(name('internal_string_character_get'),
        method_head(name('everything'), [name('everything'), name('everything')]),
        baked_expressions((params) => _new(_call(_plain('$poly.objmap.Char'), 
            [_call(_prop(params[0], 'charCodeAt'), [params[1]])]))));

    
    method(name('.'),
        method_head(name('integer'), [name('internal_list'), new Set([Name.make('length')])]),
        baked_expressions((params) => _prop(params[0], 'length'), 0, 1));
    
    method(name('iterate'),
        method_head(name('integer'), [name('internal_list')]),
        () => _plain('0'));
    method(name('iterate'),
        method_head(name('integer'), [name('internal_list'), name('integer')]),
        baked_expressions((params) => _binary(params[1], '+', _plain('1')), 1));
    method(name('more?'),
        method_head(name('integer'), [name('internal_list'), name('integer')]),
        baked_expressions((params) => _binary(_prop(params[0], 'length'), '>', params[1]), 0));
    method(name('next'),
        method_head(name('everything'), [name('internal_list'), name('integer')]),
        baked_expressions((params) => _index(params[0], params[1])));
        // baked_expressions((params) => _binary(
        //    _binary(params[1], '>=', _plain('0')), '&&', 
        //    _ifexpr(_binary(params[1], '<', _prop(params[0], 'length')), _index(params[0], params[1]), _plain('false'))), 0));
    method(name('['),
        method_head(name('everything'), [name('internal_list'), name('integer')]),
        baked_expressions((params) => _index(params[0], params[1])));
        // baked_expressions((params) => _binary(
        //    _binary(params[1], '>=', _plain('0')), '&&', 
        //    _ifexpr(_binary(params[1], '<', _prop(params[0], 'length')), _index(params[0], params[1]), _plain('false'))), 0));
    method(name('[:='),
        method_head(name('everything'), [name('internal_list'), name('integer'), name('everything')]),
        baked_expressions((params) => _binary(_index(params[0], params[1]), '=', params[2])));
        // baked_expressions((params) => _binary(
        //    _binary(params[1], '>=', _plain('0')), '&&', 
        //    _ifexpr(_binary(params[1], '<', _prop(params[0], 'length')), _binary(_index(params[0], params[1]), '=', params[2]), _plain('false'))), 0));

    method(name('.'),
        method_head(name('integer'), [name('character'), new Set([Name.make('code')])]),
        baked_expressions((params) => _prop(params[0], 'code'), 0, 1));
    return methods;
}

export class Compilation_Error extends Poly_Error {
    constructor(message: string, position?: Source_Position) {
        super(position, 'compilation error', message);
    }
}

export function JS_eval(code: string) {
    return (function (code: any) { return eval.apply(this, [code]); })(code);
}