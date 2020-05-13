import { Name, Datum, Bundle, Function_Nature, Host_Datum, Host_Datum_Spec, Type } from "./datum";
import { lookup, Known_Definition, Method_Expression, Expression, Scope, Method_Modifiers, Generic_Parameter_Scope, Unresolved_Type, Unresolved_Generic_Parameter_Definition, Call_Expression, lookup_known_definition, generic_context_of, add_definition, copy_expression, eliminate_unresolved_types, datum_string } from "./expression";
import { Source_Position, Poly_Error } from "./token";
import { JS_statement, JS_compile_method } from "./js_compile";
import { instantiate_generic_bundle, is_subtype_or_equal, is_subclass_or_equal, classof } from "./class";
import { Runtime, Call_Stack } from "./js_runtime";
import { eval_expression } from "./eval";
import { isolated_reconstructor } from "./js_reconstruct";

enum Runtime_Method_Head_Flags {
    Sealed = 1,
    Intrinsic = 2,
    Dominant = 4,
}

export class Runtime_Method_Head {
    readonly name?: Name;
    readonly id: number;

    readonly positional: Type[];
    readonly required_count: number;
    readonly named?: Map<Name, Type>;
    readonly rest?: Type;
    readonly result: Type;
    readonly flags: number;

    generic_parameters?: Datum[];
    generic_method?: number | Runtime_Generic_Method_Datum;

    get sealed() {
        return (this.flags & Runtime_Method_Head_Flags.Sealed) != 0;
    }
    get dominant() {
        return (this.flags & Runtime_Method_Head_Flags.Dominant) != 0;
    }
    get intrinsic() {
        return (this.flags & Runtime_Method_Head_Flags.Intrinsic) != 0;
    }

    get optional_count() { return this.positional.length - this.required_count }
    get no_parameters() { return this.positional.length == 0 && !this.named && !this.rest; }

    constructor(
        name: Name | undefined,
        method_id: number,
        modifiers: Set<Method_Modifiers>,
        required: Type[], optional: Type[], named: Map<Name, Type>, 
        result: Type, rest?: Type) {
            this.name = name ? Name.make(name) : undefined;
            this.id = method_id;

            this.positional = required.concat(optional);
            this.required_count = required.length;
            if (named.size > 0) this.named = new Map(named);
            if (rest) this.rest = rest;
            this.result = result;

            this.flags = 0;
            if (modifiers.has('sealed')) 
                this.flags |= Runtime_Method_Head_Flags.Sealed;
            if (modifiers.has('dominant')) 
                this.flags |= Runtime_Method_Head_Flags.Dominant;
            if (modifiers.has('intrinsic'))
                this.flags |= Runtime_Method_Head_Flags.Intrinsic;
        }
}   

export enum Method_Environment {
    Isolated = 0,
    Integrated = 1
}

export const Method_datum_spec = new Host_Datum_Spec('method', []);  

export class Runtime_Method_Datum extends Host_Datum {
    readonly id: number;
    lambda?: (Function | JS_statement) | (Function | JS_statement)[];

    constructor(id: number, lambda?: (Function | JS_statement) | (Function | JS_statement)[]) {
        super(Method_datum_spec);
        this.id = id;
        this.lambda = lambda;
    }
}

export class Runtime_Generic_Method_Datum extends Host_Datum {
    readonly id: number;
    general_case?: Runtime_Method_Datum;
    instances: Runtime_Method_Datum[];

    constructor(id: number) {
        super(Method_datum_spec);
        this.id = id;
        this.instances = [];
    }
}

export class generic_instance_descriptor {
    type: Type;
    parameters: generic_descriptor[];

    constructor(type: Type, parameters: generic_descriptor[]) {
        this.type = type;
        this.parameters = parameters;
    }
}

export type generic_descriptor =  Type | number | generic_instance_descriptor;

export class Runtime_Generic_Method_Head {
    readonly name?: Name;
    readonly id: number;

    readonly generic_parameters_count: number;
    readonly positional: generic_descriptor[];
    readonly required_count: number;
    readonly named?: Map<Name, generic_descriptor>;
    readonly rest?: generic_descriptor;
    readonly result: generic_descriptor;
    readonly flags: number;

    constructor(
        name: Name | undefined,
        method_id: number,
        generic_parameters_count: number,
        modifiers: Set<Method_Modifiers>,
        required: generic_descriptor[], optional: generic_descriptor[], named: Map<Name, generic_descriptor>, 
        result: generic_descriptor, rest?: generic_descriptor) {
            this.name = name ? Name.make(name) : undefined;
            this.id = method_id;
            this.generic_parameters_count = generic_parameters_count;

            this.positional = required.concat(optional);
            this.required_count = required.length;
            if (named.size > 0) this.named = new Map(named);
            if (rest !== undefined) this.rest = rest;
            this.result = result;

            this.flags = 0;
            if (modifiers.has('sealed')) 
                this.flags |= Runtime_Method_Head_Flags.Sealed;
            if (modifiers.has('dominant')) 
                this.flags |= Runtime_Method_Head_Flags.Dominant;
            if (modifiers.has('intrinsic'))
                this.flags |= Runtime_Method_Head_Flags.Intrinsic;
        }

    get modifiers(): Set<Method_Modifiers> {
        const _modifiers = new Set<Method_Modifiers>()
        if ((this.flags & Runtime_Method_Head_Flags.Sealed) != 0)
            _modifiers.add('sealed');
        if ((this.flags & Runtime_Method_Head_Flags.Dominant) != 0)
            _modifiers.add('dominant');
        if ((this.flags & Runtime_Method_Head_Flags.Intrinsic) != 0)
            _modifiers.add('intrinsic');
        return _modifiers;
    }
}   


export function select_method(srcloc: number, bundle: Bundle, params: Datum[]): Runtime_Method_Datum {
    const $poly = Runtime.instance;

    if (!bundle.function) throw new Execution_Error(
        $poly.call_stack.make_source_position(srcloc),
        `cannot call non-function bundle ${JSON.stringify(bundle.name?.spelling)}`,
        $poly.call_stack);
    let direct_method: Runtime_Method_Datum | undefined = undefined;
    for (var i = 0; i < bundle.function.methods.length; i++) {
        const method = bundle.function.methods[i];
        if (is_method_applicable(method.id, params)) {
            direct_method = bundle.function.methods[i];
            break;
        }
    }
    if (direct_method) {
        const head = $poly.method_heads[direct_method.id];
        if (head.sealed) return direct_method;
    }
    if (bundle.function.generic_methods) {
        const applicable_heads: Runtime_Method_Head[] = [];
        for (let gm of bundle.function.generic_methods) {
            const m = instantiate_generic_method_head(gm, params);
            if (m) applicable_heads.push(m);
        }
        if (direct_method) applicable_heads.push($poly.method_heads[direct_method.id]);
        applicable_heads.sort((a, b) => compare_method_heads(a, b));
        if (applicable_heads.length > 0) {
            const head = applicable_heads[0];
            if (head.id == direct_method?.id)
                return direct_method;
            if (head.id >= 0) for (let gm of bundle.function.generic_methods) for (let im of gm.instances)
                if (im.id == head.id) return im;
            if (head.generic_method !== undefined && head.generic_parameters !== undefined)
                return instantiate_generic_method(srcloc, head.generic_method as Runtime_Generic_Method_Datum, head.generic_parameters);
        }
    }
    if (direct_method) 
        return direct_method;
    return no_applicable_method_error(bundle, params) as any;
}

/*
export function instantiate_generic_method_general_case(srcloc: number, method: Runtime_Generic_Method_Datum) {
    const $poly = Runtime.instance;
    const method_expr = $poly.generic_method_expressions[method.id];

    const generic_parameters = method_expr.generic_parameters as Name[];

    let scope: Scope | undefined = method_expr.formal_parameters.scope;
    const instance_method_expr = copy_expression(method_expr, copied) as Method_Expression;
    eliminate_unresolved_types(instance_method_expr, generic_scope.parent as Scope);

    instance_method_expr.generic_parameters = undefined;
    const instance_datum = method_expression_to_datum(instance_method_expr);
    const instance_head = $poly.method_heads[instance_datum.id];
    method.instances.push(instance_datum);

    instance_head.generic_method = method.id;
    instance_head.generic_parameters = generic_actuals;

    return instance_datum;
}
*/

export function instantiate_generic_method(srcloc: number, method: Runtime_Generic_Method_Datum, generic_actuals: Datum[]): Runtime_Method_Datum {
    const $poly = Runtime.instance;
    const head = $poly.generic_method_heads[method.id];
    instance_loop: for (let instance of method.instances) {
        const head = $poly.method_heads[instance.id];
        const instance_context = head.generic_parameters as Datum[]; 
        for (var i = 0; i < generic_actuals.length; i++)
            if (generic_actuals[i] != instance_context[i]) continue instance_loop;
        return instance;
    }
    const method_expr = $poly.generic_method_expressions[method.id];
    if (!method_expr && method.general_case) 
        return $poly.call(srcloc, method.general_case, ...generic_actuals);
    if (!method_expr && !method.general_case) 
        return no_generic_method_expression_provided(head, generic_actuals) as any;

    const generic_parameters = method_expr.generic_parameters as Name[];

    let scope: Scope | undefined = method_expr.formal_parameters.scope;
    while (scope?.parent && !(scope instanceof Generic_Parameter_Scope))
        scope = scope.parent;
    
    const generic_scope = new Generic_Parameter_Scope(scope?.parent ? scope.parent : scope);
    for (var i = 0; i < generic_actuals.length; i++) {
        const name = generic_parameters[i];
        const value = generic_actuals[i];
        const known = new Known_Definition(method_expr.position, name, value);
        add_definition(generic_scope, name, known); 
    }

    const copied = new Map();
    copied.set(scope, generic_scope);

    const instance_method_expr = copy_expression(method_expr, copied) as Method_Expression;
    eliminate_unresolved_types(instance_method_expr, generic_scope.parent as Scope);

    instance_method_expr.generic_parameters = undefined;
    const instance_datum = method_expression_to_datum(instance_method_expr);
    const instance_head = $poly.method_heads[instance_datum.id];
    method.instances.push(instance_datum);

    instance_head.generic_method = method.id;
    instance_head.generic_parameters = generic_actuals;

    return instance_datum;
}

export function instantiate_generic_method_head(method: Runtime_Generic_Method_Datum, params: Datum[]): Runtime_Method_Head | undefined {
    const $poly = Runtime.instance;

    const length = params.length;
    const head = $poly.generic_method_heads[method.id];
    if (length < head.required_count) return undefined;
    if (head.rest === undefined && head.required_count == 0 && length > head.positional.length) return undefined;
    const context: Datum[] = new Array(head.generic_parameters_count);
    const conforms = (t0: Datum, t1: Datum) => {
        if (t0 instanceof Bundle) 
            return is_subclass_or_equal(classof(t1), t0);
        return $poly.call(0, $poly.lookup('in'), t1, t0) !== false;
    }
    const find_common_type = (t0: Datum, t1: Datum) => {
        if (is_subtype_or_equal(t0, t1)) return t1;
        if (is_subtype_or_equal(t1, t0)) return t0;
        if (!(t0 instanceof Bundle && t1 instanceof Bundle))
            return undefined;
        if (!t0.class || !t1.class) return $poly.lookup('bundle');
        for (let class0 of t0.class.superclasses)
            for (let class1 of t1.class.superclasses)
                if (class0 == class1) return class0;
        return t0;
    }
    const descriptor_context = (dscr: generic_instance_descriptor, t0: Bundle) => {
        const instance = t0.class?.generic_instance;
        if (instance && instance.generic_class == dscr.type)
            return instance.generic_actuals;
        const superclasses = t0.class?.superclasses as Bundle[];
        if (superclasses) for (let sclass of superclasses)
            if (sclass.class?.generic_instance?.generic_class == dscr.type)
                return sclass.class.generic_instance.generic_actuals;
        return undefined;
    }
    const conforms_descriptor = (d: generic_descriptor, p: Datum, by_type = false) => {
        if (typeof d == 'number') {
            p = by_type ? p : classof(p);
            if (!context[d]) context[d] = p;
            else if (context[d]) {
                const common = find_common_type(p, context[d]);
                if (!common)
                    return false;   
                context[d] = common;
            }
            return true;
        }
        if (d instanceof generic_instance_descriptor) {
            p = by_type ? p : classof(p);
            const actuals = descriptor_context(d, p as Bundle);
            if (!actuals) return false;

            if (actuals.length != d.parameters.length) return false;
            for (var i = 0; i < actuals.length; i++)
                if (!conforms_descriptor(d.parameters[i], actuals[i], true)) return false;
            return true;
        }
        return conforms(d, p);
    }
    for (var i = 0; i < head.positional.length; i++) {
        const descriptor = head.positional[i];
        if (!conforms_descriptor(descriptor, params[i]))
            return undefined;
    }
    if (params.length > head.positional.length) {
        if (head.rest !== undefined) for (var i = head.positional.length; i < params.length; i++)
            if (!conforms_descriptor(head.rest, params[i])) return undefined;
        if (head.named) 
            // TODO
            return undefined;
    }
    instance_loop: for (let instance of method.instances) {
        const head = $poly.method_heads[instance.id];
        const instance_context = head.generic_parameters as Datum[]; 
        for (var i = 0; i < context.length; i++)
            if (context[i] != instance_context[i]) continue instance_loop;
        return head;
    }  
    const resolve_descriptor = (d: generic_descriptor): Datum => {
        if (typeof d == 'number')
            return context[d];
        if (d instanceof generic_instance_descriptor) {
            const parameters = d.parameters.map(p => resolve_descriptor(p));
            return instantiate_generic_bundle(d.type as Bundle, parameters) as Bundle;
        }
        return d;
    }
    const detached_head = new Runtime_Method_Head(
        head.name,
        -2,
        head.modifiers,
        head.positional.slice(0, head.required_count).
            map(p => resolve_descriptor(p)),
        head.positional.slice(head.required_count).
            map(p => resolve_descriptor(p)),
        new Map(),
        resolve_descriptor(head.result),
        head.rest !== undefined ? 
            resolve_descriptor(head.rest) : undefined);
    detached_head.generic_method = method;
    for (var i = 0; i < context.length; i++)
        if (context[i] == undefined) context[i] = $poly.lookup('everything');
    detached_head.generic_parameters = context;
    return detached_head;
}

export function is_method_applicable(method: number, params: Datum[]) {
    const $poly = Runtime.instance;

    const length = params.length;
    const head = $poly.method_heads[method];
    if (length < head.required_count) return false;
    if (!head.rest && head.required_count == 0 && length > head.positional.length) return false;
    const positional = head.positional.length > params.length ?
        params.length : head.positional.length;
    const match = (type: Datum, param: Datum) => {
        if (type instanceof Bundle) 
            return is_subclass_or_equal(classof(param), type);
        else if (type instanceof Set) 
            return type.has(param);
        return $poly.call(0, $poly.lookup('in'), param, type) !== false;
    }
    for (var i = 0; i < positional; i++) 
        if (!match(head.positional[i], params[i])) return false;
    
    if (head.positional.length >= params.length) return true;
    if (head.rest) {
        for (var i = head.positional.length; i < params.length; i++) 
            if (!match(head.rest, params[i])) return false;
        return true;
    }
    // TODO named
    return false;
}

export function add_method(bundle: Bundle, method: Runtime_Generic_Method_Datum | Runtime_Method_Datum) {
    const $poly = Runtime.instance;

    if (!bundle.function) {
        bundle.function = new Function_Nature();
    }
    if (method instanceof Runtime_Method_Datum) {
        bundle.function.methods.push($poly.method_datums[method.id]);
        bundle.function.methods.sort((a, b) => compare_methods(a.id, b.id));
    }
    if (method instanceof Runtime_Generic_Method_Datum) {
        if (!bundle.function.generic_methods)
            bundle.function.generic_methods = [];
        bundle.function.generic_methods.push(method);
    }
}

export function add_method_expression(bundle: Bundle, expr: Method_Expression) {
    add_method(bundle, method_expression_to_datum(expr));
}

export function method_expression_to_datum(expr: Method_Expression): Runtime_Method_Datum | Runtime_Generic_Method_Datum {
    const $poly = Runtime.instance;
    const generic_parameters = expr.generic_parameters;
    if (!generic_parameters) {
        let method_id: number | undefined = undefined;
        for (var i = 0; i < $poly.method_expressions.length; i++)
            if (expr == $poly.method_expressions[i]) {
                method_id = i;
                break;
            }
        if (method_id !== undefined) 
            return $poly.method_datums[method_id];
        method_id = $poly.method_index++;
        $poly.method_expressions[method_id] = expr;
        $poly.method_heads[method_id] = new Runtime_Method_Head(
            expr.name,
            method_id,
            expr.modifiers,
            expr.formal_parameters.required.map(p => p.type),
            expr.formal_parameters.optional.map(p => p.type),
            new Map(expr.formal_parameters.named.map(p => [p.name, p.type])),
            expr.result_type,
            expr.formal_parameters.rest?.type);
        $poly.method_datums[method_id] = new Runtime_Method_Datum(method_id);
        // @isolated_computations
        // NOTE: line below enables isolated computations
        // JS_compile_method(method_id, isolated_reconstructor());
        return $poly.method_datums[method_id];
    }
    let generic_method_id: number | undefined = undefined;
    for (var i = 0; i < $poly.generic_method_expressions.length; i++)
        if (expr == $poly.generic_method_expressions[i]) {
            generic_method_id = i;
            break;
        }
    if (generic_method_id !== undefined)
        return $poly.generic_method_datums[generic_method_id];

    const is_generic_instance_expression = (e: Expression) => 
        e instanceof Call_Expression && 
        e.method instanceof Name && 
        e.method.spelling == '[' &&
        e.parameters.length > 1 &&
        e.parameters[0] instanceof Name &&
        (lookup_known_definition(
            expr.formal_parameters.scope, 
            e.parameters[0]) instanceof Bundle);

    const descriptor_of = (type: Datum | Unresolved_Type) => {
        if (!(type instanceof Unresolved_Type))
            return type;
        const type_expr = type.expression;
        if (type_expr instanceof Name) {
            const defn = lookup(expr.formal_parameters.scope, type_expr);
            if (defn instanceof Unresolved_Generic_Parameter_Definition)
                return generic_parameters.indexOf(defn.name);
            return eval_expression(type_expr, expr.formal_parameters.scope);
        }
        if (!is_generic_instance_expression(type_expr)) 
            throw new Error('invalid usage of generic parameters...');
        const call = type_expr as Call_Expression;
        const bundle = lookup_known_definition(
            expr.formal_parameters.scope, call.parameters[0] as Name) as Bundle;
        const descriptors: generic_descriptor[] = [];
        for (let p of call.parameters.slice(1)) {
            const context = generic_context_of(p, expr.formal_parameters.scope);
            if (context.size == 0) {
                descriptors.push(eval_expression(p, expr.formal_parameters.scope));
                continue;
            }
            const unresolved_type = new Unresolved_Type(p, context);
            descriptors.push(descriptor_of(unresolved_type));
        }
        return new generic_instance_descriptor(bundle, descriptors);            
    }
    generic_method_id = $poly.generic_method_index++;
    $poly.generic_method_expressions[generic_method_id] = expr;
    $poly.generic_method_heads[generic_method_id] = new Runtime_Generic_Method_Head(
        expr.name,
        generic_method_id,
        generic_parameters.length,
        expr.modifiers,
        expr.formal_parameters.required.map(p => descriptor_of(p.type)),
        expr.formal_parameters.optional.map(p => descriptor_of(p.type)),
        new Map(expr.formal_parameters.named.map(p => [p.name, descriptor_of(p.type)])),
        descriptor_of(expr.result_type),
        expr.formal_parameters.rest?.type ?
            descriptor_of(expr.formal_parameters.rest.type) :
            undefined,
    );
    $poly.generic_method_datums[generic_method_id] = new Runtime_Generic_Method_Datum(generic_method_id);
    return $poly.generic_method_datums[generic_method_id];
}

export function compare_methods(method1: number, method2: number) {
    const $poly = Runtime.instance;
    return compare_method_heads($poly.method_heads[method1], $poly.method_heads[method2]);
}

export function compare_method_heads(head1: Runtime_Method_Head, head2: Runtime_Method_Head): number {
    let equal = true;
    const positional = head1.positional.length > head2.positional.length ?
        head1.positional.length : head2.positional.length;

    for (var i = 0; i < positional; i++) {
        const type1 = head1.positional[i];
        const type2 = head2.positional[i];
        if (type1 === undefined) {
            equal = false;
            continue;
        } 
        if (!is_subtype_or_equal(type1, type2)) return 1;
        if (!is_subtype_or_equal(type2, type1)) equal = false;
    }

    const head1_named = head1.named ? head1.named.keys() : [];
    for (let name of head1_named) {
        const type1 = head1.named?.get(name);
        const type2 = head2.named?.get(name);
        if (type1 === undefined) {
            equal = false;
            continue;
        }
        if (!is_subtype_or_equal(type1, type2)) return 1;
        if (!is_subtype_or_equal(type2, type1)) equal = false;
    }

    const head2_named = head1.named ? head1.named.keys() : [];
    for (let name of head2_named) {
        const type1 = head1.named?.get(name);
        const type2 = head2.named?.get(name);
        if (type1 === undefined) {
            equal = false;
            continue;
        }
        if (!is_subtype_or_equal(type1, type2)) return 1;
        if (!is_subtype_or_equal(type2, type1)) equal = false;
    }

    return equal ? 0 : -1;
}  


export class Execution_Error extends Poly_Error {
    constructor(position: Source_Position, message: string, stack: Call_Stack) {
        super(position, 'execution error', message, stack);   
    }
}

export function no_generic_method_expression_provided(head: Runtime_Generic_Method_Head, generic_actuals: Datum[]) {
    const $poly = Runtime.instance;
    const descriptor_string = (p: generic_descriptor): string => {
        if (typeof p == 'number') return '$' + datum_string(p);
        if (p instanceof generic_instance_descriptor)
            return `${datum_string(p.type)}[${p.parameters.map(p => descriptor_string(p)).join(', ')}]`;
        return datum_string(p);
    }
    const actuals = generic_actuals.map(p => datum_string(p));
    const positional = head.positional.map(p => descriptor_string(p));
    const method_desc = `${head.name?.spelling}[${actuals.join(', ')}](${positional.join(', ')})`;
    const message = `cannot instantiate generic method ${method_desc} if expression is not provided`;
    throw new Execution_Error(
        $poly.call_stack.tail_source_position(),
       message, $poly.call_stack);
}

export function no_applicable_method_error(method: Bundle | Runtime_Generic_Method_Datum | string, params: Datum[]) {
    const $poly = Runtime.instance;
    method = method instanceof Runtime_Method_Datum ?
        $poly.method_heads[method.id].name?.spelling as string :
        method;
    let position = $poly.call_stack.tail_source_position();
    let method_string = datum_string(method);
    let params_string = params.map(p => datum_string(p)).join(', ');
    let message = `no method matching ${method_string}(${params_string})`;
    throw new Execution_Error(position, message, $poly.call_stack);
}