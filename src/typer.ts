import { Expression, Quotation, Scope, Prog_Expression, Block_Scope, If_Expression, Call_Expression, Assigment_Expression, Known_Definition, Constant_Definition, Variable_Definition, Method_Expression, Instance_Expression, Slot_Read_Expression, Slot_Write_Expression, Definition, Module, Formal_Parameters, Formal_Parameter_Definition, Generic_Parameter_Scope, Exit_Expression, Exit_Call_Expression, Method_Head } from "./expression";
import { Runtime } from "./js_runtime";
import { generic_descriptor, generic_instance_descriptor, Runtime_Generic_Method_Datum, instantiate_generic_method, compare_methods, Runtime_Method_Datum, method_expression_to_datum } from './method';
import { Char, Name, Datum, Bundle, Type, Macro_Context } from "./datum";
import { Poly_Error, Source_Position } from "./token";
import { instantiate_generic_bundle, is_subtype_or_equal, classof } from "./class";

export type Predicted_Outcome = Outcome_Oneof | Outcome_Type | Outcome_Datum;

export class Outcome_Oneof {
    outcomes: Set<Outcome_Datum | Outcome_Type>;

    constructor(...outcomes: Predicted_Outcome[]) {
        this.outcomes = new Set();
        for (let outcome of outcomes) this.add(outcome);
    }

    has(out0: Predicted_Outcome) {
        if (out0 instanceof Outcome_Oneof) {
            for (let out1 of out0.outcomes) 
                if (!this.has(out1)) return false;
            return true;
        }
        return this.outcomes.has(out0);
    }
    
    add(outcome: Predicted_Outcome) {
        if (this.has(outcome)) {
            return;
        }
        if (outcome instanceof Outcome_Oneof) {
            for (let sub_outcome of outcome.outcomes) {
                this.add(sub_outcome);
            } 
            return;       
        }
        this.outcomes.add(outcome);
    }   

    delete(out0: Predicted_Outcome) {
        if (out0 instanceof Outcome_Oneof) for (let out1 of out0.outcomes)
            this.delete(out1);
        else this.outcomes.delete(out0);
    }
}

export class Outcome_Datum {
    datum: Datum;

    constructor(datum: Datum) {
        this.datum = datum;
    }

    static make(typer: Typer, datum: Datum) {
        const existing = typer._datum_outcomes.get(datum);
        if (existing)
            return existing;
        const outcome = new Outcome_Datum(datum);
        typer._datum_outcomes.set(datum, outcome);
        return outcome;
    }
}

export class Outcome_Type {
    type: Datum;

    constructor(type: Datum) {
        this.type = type;
    }

    static make(typer: Typer, type: Datum) {
        const existing = typer._typed_outcomes.get(type);
        if (existing)
            return existing;
        const outcome = new Outcome_Type(type);
        typer._typed_outcomes.set(type, outcome);
        return outcome;
    }
}

export function combine_outcomes(...outcomes: Predicted_Outcome[]): Predicted_Outcome {
    const outcome = new Outcome_Oneof(...outcomes);
    if (outcome.outcomes.size == 1) for (let out of outcome.outcomes)
        return out;
    return outcome;
}

export class Typer {
    constructor() {
        this._typed_outcomes = new Map();
        this._datum_outcomes = new Map();
    }

    _typed_outcomes: Map<Datum, Outcome_Type>;
    _datum_outcomes: Map<Datum, Outcome_Datum>;

    typed_outcome(type: Datum) {
        return Outcome_Type.make(this, type);
    }
    
    datum_outcome(datum: Datum) {
        return Outcome_Datum.make(this, datum);
    }
}

export class Typer_object {
    name: Name;
    outcome: Predicted_Outcome;
    definition?: Definition;

    constructor(name: Name, outcome: Predicted_Outcome, definition?: Definition) {
        this.name = name;
        this.outcome = outcome;
        this.definition = definition;
    }

    has_outcome(outcome: Predicted_Outcome) {
        if (outcome == this.outcome) return true;
        if (this.outcome instanceof Outcome_Oneof)
            return this.outcome.has(outcome);
        return false;
    }

    add_outcome(outcome: Predicted_Outcome) {
        if (outcome == this.outcome) return;
        if (this.outcome instanceof Outcome_Oneof) {
            this.outcome.add(outcome);
            this.outcome = combine_outcomes(this.outcome);
            return;
        }
        this.outcome = combine_outcomes(this.outcome, outcome);
    }

    delete_outcome(outcome: Predicted_Outcome) {
        if (outcome == this.outcome)  this.outcome = combine_outcomes();
        if (this.outcome instanceof Outcome_Oneof) {
            this.outcome.delete(outcome);
            this.outcome = combine_outcomes(this.outcome);
            return;
        }
    }
}

export class Typer_Context {
    typer: Typer;
    parent: Typer_Context | Module;
    objects: Map<Name | Exit_Expression, Typer_object>;

    static dispatch_cache: Method_Dispatch_Cache;
    static enable_aggressive_inlining = false;

    constructor(parent: Typer_Context | Module, typer?: Typer) {
        this.typer = typer ? typer : (parent as any).typer;
        this.parent = parent;
        this.objects = new Map();
        if (!Typer_Context.dispatch_cache)
            Typer_Context.dispatch_cache = new Method_Dispatch_Cache();
    }

    from_definition(name: Name, defn: Definition, outcome_cache = new Map()): Typer_object {
        let outcome: Predicted_Outcome | undefined = undefined;
        if (defn instanceof Known_Definition)
            outcome = infer_outcome(defn, this, outcome_cache);
        else if (defn instanceof Variable_Definition)
            outcome = infer_outcome(defn, this, outcome_cache);
        else if (defn instanceof Constant_Definition)
            outcome = infer_outcome(defn, this, outcome_cache);
        else if (defn instanceof Formal_Parameter_Definition)
            outcome = this.typer.typed_outcome(defn.type);
        const object = new Typer_object(name, outcome as Predicted_Outcome, defn);
        return object;
    }

    consume_definition(name: Name, defn: Definition, outcome_cache = new Map()) {
        this.objects.set(name, this.from_definition(name, defn, outcome_cache));
    }

    consume_scope(scope: Scope, outcome_cache = new Map()) {
        for (let [name, defn] of scope.definitions)
            this.consume_definition(name, defn, outcome_cache);
        if (scope instanceof Block_Scope) for (var i = 0; i < scope.expressions.length; i++) {
            const body_expression = scope.expressions[i];
            if (body_expression instanceof Exit_Expression) {
                const object = new Typer_object(body_expression.name, combine_outcomes());
                this.objects.set(body_expression, object);
            }
        }
    }

    consume_formal_parameters(formal_parameters: Formal_Parameters, outcome_cache = new Map()) {
        for (let param of formal_parameters.required)
            this.consume_definition(param.name, param, outcome_cache);
        for (let param of formal_parameters.optional)
            this.consume_definition(param.name, param, outcome_cache);
        for (let param of formal_parameters.named)
            this.consume_definition(param.name, param, outcome_cache);
        if (formal_parameters.rest)
            this.consume_definition(formal_parameters.rest.name, formal_parameters.rest, outcome_cache);
    }

    lookup(name: Name | Exit_Expression): Typer_object | undefined {
        const existing = this.objects.get(name);
        if (existing)
            return existing;
        if (this.parent instanceof Typer_Context)
            return this.parent.lookup(name);
        if (name instanceof Exit_Expression)
            return undefined;
        const defn = this.parent.lookup(name);
        if (!defn)
            return name.context instanceof Macro_Context ?
                Typer_Context.
                    from_scope(name.context.parent_scope).
                    lookup(Name.make(name)) : 
                undefined;
        return this.from_definition(name, defn);
    }

    has_outcome(name: Name, outcome: Predicted_Outcome) {
        const object = this.lookup(name);
        if (!object)
            return false;
        return object.has_outcome(outcome);
    }

    _local(name: Name) {
        const existing = this.objects.get(name);
        if (existing)
            return existing;
        const from_parents = this.lookup(name);
        if (from_parents) {
            const object = new Typer_object(
                name, 
                from_parents.outcome,
                from_parents.definition);
            this.objects.set(name, object);
            return object;       
        }
        const object = new Typer_object(name, combine_outcomes());
        this.objects.set(name, object);
        return object;
    }

    add_outcome(name: Name, outcome: Predicted_Outcome) {
        const object = this._local(name);
        object.add_outcome(outcome);
    }

    delete_outcome(name: Name, outcome: Predicted_Outcome) {
        const object = this._local(name);
        object.delete_outcome(outcome);
    }

    static from_scope(scope: Scope, typer: Typer = new Typer(), outcome_cache = new Map()): Typer_Context {
        const path: Scope[] = [];
        let next: Scope | undefined = scope;
        while (next) {
            path.push(next);
            next = next.parent;
        }
        let context = new Typer_Context(path.pop() as Module, typer);
        while (path.length > 0) {
            const next = path.pop() as Scope;
            context = new Typer_Context(context);
            context.consume_scope(next, outcome_cache);
        }
        return context;
    }
}

export function predict_most_general_outcome_type(outcome: Predicted_Outcome): Datum {
    const $poly = Runtime.instance;
    let most_general_type: Datum | undefined = undefined;
    const proccess_type = (type: Datum) => {
        if (!most_general_type) {
            most_general_type = type;
            return;
        }
        if (is_subtype_or_equal(most_general_type, type) && !is_subtype_or_equal(type, most_general_type))
            most_general_type = type;
    }
    const proccess_outcome = (outcome: Predicted_Outcome) => {
        if (outcome instanceof Outcome_Datum)
            return proccess_type(classof(outcome.datum));
        if (outcome instanceof Outcome_Type)
            return proccess_type(outcome.type);
        for (let out of outcome.outcomes)
            proccess_outcome(out);
    }
    proccess_outcome(outcome);
    if (!most_general_type)
        return $poly.lookup('everything');
    return most_general_type;
}

export function predict_spread_parameter_member_type(context: Typer_Context, outcome: Predicted_Outcome) {
    const $poly = Runtime.instance;
    const _everything = $poly.lookup('everything');
    const _sequence = $poly.lookup('sequence');
    const proccess_type = (datum: Datum) => {
        const is_class = datum instanceof Bundle && datum.class;
        if (!is_class) 
            return context.typer.typed_outcome(_everything);
        const bundle = datum as Bundle;
        for (let sup of bundle.class?.superclasses as Bundle[])
            if (sup.class?.generic_instance?.generic_class == _sequence)
                return context.typer.typed_outcome(
                    sup.class?.generic_instance?.generic_actuals[0] as Datum);
        return context.typer.typed_outcome(_everything);
    }
    const proccess_datum = (datum: Datum) => 
        proccess_type(classof(datum));
    if (outcome instanceof Outcome_Datum) 
        return proccess_datum(outcome.datum);
    if (outcome instanceof Outcome_Type) 
        return proccess_type(outcome.type);
    let result = combine_outcomes();
    for (let out of outcome.outcomes) 
        result = combine_outcomes(predict_spread_parameter_member_type(context, out));
    if (result instanceof Outcome_Oneof && result.outcomes.size == 0)
        return context.typer.typed_outcome(_everything);
    return result;
}

export function predict_generic_method_call_applicable(context: Typer_Context, method: Runtime_Generic_Method_Datum, params: Predicted_Outcome[], spread: boolean, generic_parameter_scope?: Datum[]) {
    const $poly = Runtime.instance;
    const head = $poly.generic_method_heads[method.id];

    if (params.length < head.required_count && !spread) return false;
    if (head.rest === undefined && !head.named && params.length > head.positional.length) return false;

    const possible_context_parameters: Set<Datum>[] = [];
    const descriptor_context = (dscr: generic_instance_descriptor, t0: Bundle) => {
        const instance = t0.class?.generic_instance;
        if (instance && instance.generic_class == dscr.type)
            return instance.generic_actuals;
        const superclasses = t0.class?.superclasses as Bundle[];
        if(superclasses) for (let sclass of superclasses)
            if (sclass.class?.generic_instance?.generic_class == dscr.type)
                return sclass.class.generic_instance.generic_actuals;
        return undefined;
    }
    const find_common_type = (t0: Datum, t1: Datum) => {
        if (is_subtype_or_equal(t0, t1)) return t1;
        if (is_subtype_or_equal(t1, t0)) return t0;
        if (!(t0 instanceof Bundle && t1 instanceof Bundle))
            return undefined;
        if (!t0.class || !t1.class) return this.lookup('bundle');
        for (let class0 of t0.class.superclasses)
            for (let class1 of t1.class.superclasses)
                if (class0 == class1) return class0;
        return t0;
    }
    const conform_context_parameter = (position: number, actual: Datum): boolean => {
        if (generic_parameter_scope) { 
            const common = find_common_type(actual, generic_parameter_scope[position]);
            if (!common) return false;
            generic_parameter_scope[position] = common;
            return true;
        }
        if (!possible_context_parameters[position])
            possible_context_parameters[position] = new Set();
        possible_context_parameters[position].add(actual);
        return true;
    }

    const applicable_membership = (class0: Type, class1: Type) => {
        if (is_subtype_or_equal(class0, class1))
            return true;
        return is_subtype_or_equal(class1, class0);
    }
    const applicable_datum = (dscr: generic_descriptor, datum: Datum) => {
        if (typeof dscr == 'number')
            return conform_context_parameter(dscr, classof(datum));
        if (dscr instanceof generic_instance_descriptor) {
            const actuals = descriptor_context(dscr, classof(datum));
            if (!actuals) return false;
            for (var i = 0; i < actuals.length; i++)
                if (!applicable_type(dscr.parameters[i], actuals[i])) return false;
            return false;
        }
        if (dscr instanceof Bundle && applicable_membership(classof(datum), dscr))
            return true;
        if (dscr instanceof Set)
            return dscr.has(datum);
        if ($poly.call(0, $poly.lookup('in'), datum, dscr) !== false) 
            return true;
        return false;
    }
    const applicable_type = (dscr: generic_descriptor, type: Datum) => {
        if (typeof dscr == 'number')
            return conform_context_parameter(dscr, type);
        if (dscr instanceof generic_instance_descriptor) {
            const actuals = descriptor_context(dscr, type as Bundle);
            if (!actuals) return false;
            for (var i = 0; i < actuals.length; i++)
                if (!applicable_type(dscr.parameters[i], actuals[i])) return false;
            return true;
        }
        return applicable_membership(type, dscr);
    }
    const applicable_outcome = (dscr: generic_descriptor, param: Predicted_Outcome) => {
        if (param instanceof Outcome_Datum)
            return applicable_datum(dscr, param.datum);
        if (param instanceof Outcome_Type)
            return applicable_type(dscr, param.type);
        for (let out of param.outcomes)
            if (!applicable_outcome(dscr, out)) return false;
        return param.outcomes.size > 0;
    }

    const non_spread_length = spread ? params.length - 1 : params.length;
    const positional = head.positional.length > non_spread_length ?
        non_spread_length : head.positional.length;
    for (var i = 0; i < positional; i++) {
        const param_type = head.positional[i];
        if (!applicable_outcome(param_type, params[i])) return false;
    }
    if (non_spread_length > head.positional.length) {
        if (head.rest !== undefined) for (var i = head.positional.length; i < non_spread_length; i++)
            if (!applicable_outcome(head.rest, params[i])) return false;
        if (head.named) 
            // TODO named
            return false;
    }
    if (spread) {
        const spread_member = predict_spread_parameter_member_type(context, params[params.length - 1]);
        if (non_spread_length < head.positional.length)
            for (var i = non_spread_length; i < head.positional.length; i++)
                if (!applicable_outcome(head.positional[i], spread_member)) return false;
        if (head.rest !== undefined && !applicable_outcome(head.rest, spread_member)) 
            return false;
    }

    if (generic_parameter_scope) return true;

    while (possible_context_parameters.length < head.generic_parameters_count)
        possible_context_parameters.push(new Set());
    
    for (let p of possible_context_parameters)
        if (p.size == 0) p.add($poly.lookup('everything'));

    const possibilities_tail = (i: number) => {
        if (i >= possible_context_parameters.length)
            return [[]] as Datum[][];
        const invariants = possible_context_parameters[i];
        const next_tails = possibilities_tail(i + 1);
        const tails: Datum[][] = [];
        for (let param of invariants)
            tails.push(...next_tails.map(tail => [param, ...tail]));
        return tails;
    }

    let possible_contexts = possibilities_tail(0);
    if (possible_contexts.length == 1 && possible_contexts[0].length == 0)
        possible_contexts = [];

    const always_applicable_contexts: Datum[][] = possible_contexts.filter(c => 
        predict_generic_method_call_applicable(context, method, params, spread, c));

    for (let c of possible_contexts)
        instantiate_generic_method(0, method, c);

    if (always_applicable_contexts.length == 0)
        return false;

    return always_applicable_contexts.map(c => 
        instantiate_generic_method(0, method, c)).
        sort((a, b) => compare_methods(a.id, b.id));
}

export function predict_method_call_applicable(context: Typer_Context, m1: number, params: Predicted_Outcome[], spread: boolean, strict: boolean = false) {
    const $poly = Runtime.instance;
    const head = $poly.method_heads[m1];
    
    if (params.length < head.required_count && (!spread || strict)) return false;
    if (!head.rest && !head.named && params.length > head.positional.length) return false;
    if (!head.rest && spread && strict) return false;

    const applicable_membership = (class0: Type, class1: Type) => {
        if (is_subtype_or_equal(class0, class1))
            return true;
        if (!strict) 
            return is_subtype_or_equal(class1, class0);
        return false;
    }
    const applicable_datum = (param_type: Datum, datum: Datum) => {
        if (param_type instanceof Bundle && applicable_membership(classof(datum), param_type))
            return true;
        if (param_type instanceof Set)
            return param_type.has(datum);
        if ($poly.call(0, $poly.lookup('in'), datum, param_type) !== false) 
            return true;
        return false;
    }
    const applicable_type = (param_type: Datum, type: Datum) => {
        if (applicable_membership(type, param_type)) 
            return true;
        return false;
    }
    const applicable_outcome = (param_type: Datum, param: Predicted_Outcome) => {
        if (param instanceof Outcome_Datum)
            return applicable_datum(param_type, param.datum);
        if (param instanceof Outcome_Type)
            return applicable_type(param_type, param.type);
        for (let out of param.outcomes)
            if (!applicable_outcome(param_type, out)) return false;
        return param.outcomes.size > 0;
    }
    const non_spread_length = spread ? params.length - 1 : params.length;
    const positional = head.positional.length > non_spread_length ?
        non_spread_length : head.positional.length;
    for (var i = 0; i < positional; i++) {
        const param_type = head.positional[i];
        if (!applicable_outcome(param_type, params[i])) return false;
    }
    if (spread) {
        const spread_member = predict_spread_parameter_member_type(context, params[params.length - 1]);
        if (non_spread_length < head.positional.length)
            for (var i = non_spread_length; i < head.positional.length; i++)
                if (!applicable_outcome(head.positional[i], spread_member)) return false;
        if (head.rest !== undefined && !applicable_outcome(head.rest, spread_member)) 
            return false;
    }
    if (head.positional.length >= non_spread_length) return true;
    if (head.rest) {
        for (var i = head.positional.length; i < non_spread_length; i++)
            if (!applicable_outcome(head.rest, params[i])) 
                return false;
        return true;
    }
    // TODO named
    if (head.named) throw new Error(`TODO`);
    return false;
}

export function equal_outcomes(out0: Predicted_Outcome, out1: Predicted_Outcome) {
    if (out0 == out1) return true;
    if (out0 instanceof Outcome_Oneof) {
        if (!(out1 instanceof Outcome_Oneof))
            return out0.outcomes.size == 1 && out0.has(out1);
        if (!out1.has(out1)) return false;
        if (!out0.has(out0)) return false;
        return true;
    }
    if (out1 instanceof Outcome_Oneof) 
        return out1.outcomes.size == 1 && out1.has(out0);
    if (out0 instanceof Outcome_Datum && out1 instanceof Outcome_Datum)
        return out0.datum == out1.datum;
    if (out0 instanceof Outcome_Type && out1 instanceof Outcome_Type)
        return out0.type == out1.type;
    return false;
}

export function specify_prediction(outcome: Predicted_Outcome, type0: Type, context: Typer_Context) {
    const proccess_datum_outcome = (datum: Datum) =>
    is_subtype_or_equal(type0, classof(datum)) && !is_subtype_or_equal(classof(datum), type0) ?
        context.typer.typed_outcome(type0) : 
        context.typer.datum_outcome(datum);
    const proccess_type_outcome = (type: Datum) => 
        is_subtype_or_equal(type0, type) && !is_subtype_or_equal(type, type0) ?
            context.typer.typed_outcome(type0) : 
            context.typer.typed_outcome(type);
    const proccess_outcome = (outcome: Predicted_Outcome) => {
        if (outcome instanceof Outcome_Datum)
            return proccess_datum_outcome(outcome.datum);
        if (outcome instanceof Outcome_Type)
            return proccess_type_outcome(outcome.type);
        let result = combine_outcomes();
        for (let out of outcome.outcomes)
            result = combine_outcomes(result, proccess_outcome(out));
        return result;
    }
    return proccess_outcome(outcome);
}

export function infer_outcome(expr: Expression, context: Typer_Context, outcome_cache = new Map()): Predicted_Outcome {
    if (typeof expr != 'object' ||
        expr instanceof Name ||
        expr instanceof Quotation ||
        expr instanceof Char ||
        expr instanceof Method_Expression) return _infer_outcome(expr, context, outcome_cache);
    const existing = outcome_cache.get(expr);
    if (existing !== undefined)
        return existing;
    const outcome = _infer_outcome(expr, context, outcome_cache);
    outcome_cache.set(expr, outcome);
    return outcome;
}

export function _infer_outcome(expr: Expression, context: Typer_Context, outcome_cache = new Map()): Predicted_Outcome {
    switch (typeof expr) {
    case 'undefined':
        return context.typer.datum_outcome(false);
    case 'boolean':
        return context.typer.datum_outcome(expr);
    case 'number':
        return context.typer.datum_outcome(expr);
    case 'string':
        return context.typer.datum_outcome(expr);
    }
    if (expr instanceof Char) {
        return context.typer.datum_outcome(expr);
    }
    if (expr instanceof Quotation) {
        return context.typer.datum_outcome(expr.datum);
    }
    if (expr instanceof Name) {
        const object = context.lookup(expr);
        if (!object) 
            throw new Typer_Error(`unknown reference ${JSON.stringify(expr.spelling)}`);
        return object.outcome;
    }
    if (expr instanceof Block_Scope) {
        const body_context = new Typer_Context(context);
        body_context.consume_scope(expr, outcome_cache);

        let outcome: Predicted_Outcome | undefined;
        for (let body_expr of expr.expressions) {
            outcome = infer_outcome(body_expr, body_context, outcome_cache);
        }
        return outcome || context.typer.datum_outcome(false);
    }
    if (expr instanceof Prog_Expression) {
        let outcome: Predicted_Outcome | undefined;
        for (let body_expr of expr.expressions) {
            outcome = infer_outcome(body_expr, context, outcome_cache);
        }
        return outcome || context.typer.datum_outcome(false);
    }
    if (expr instanceof If_Expression) {
        const if_context = new Typer_Context(context);
        if (expr.test instanceof Name) {
            if_context.delete_outcome(expr.test, if_context.typer.datum_outcome(false));
        }
        const consequent = infer_outcome(expr.consequent, if_context, outcome_cache);
        const alternate = infer_outcome(expr.alternate, if_context, outcome_cache);
        return combine_outcomes(consequent, alternate);
    }
    if (expr instanceof Call_Expression) {
        const outcome = infer_method_call_outcome(context, expr, outcome_cache);
        return outcome;
    }
    if (expr instanceof Assigment_Expression) {
        const rhs = infer_outcome(expr.rhs, context, outcome_cache);
        const object = context.lookup(expr.lhs) as Typer_object;
        if (object === undefined)
            throw new Typer_Error(`assigment to unresolved definition ${JSON.stringify(expr.lhs.spelling)}`);
        if (!object.definition?.assignable())
            throw new Typer_Error(`definition ${JSON.stringify(object.name.spelling)} is not assignable`);
        object.add_outcome(rhs);
        return object.outcome;
    }
    if (expr instanceof Known_Definition) {
        return context.typer.datum_outcome(expr.value);
    }
    if (expr instanceof Constant_Definition) {
        const expression_outcome = infer_outcome(expr.expression, context, outcome_cache);
        const outcome = specify_prediction(expression_outcome, expr.type, context);
        return outcome;
    }
    if (expr instanceof Variable_Definition) {
        const expression_outcome = infer_outcome(expr.expression, context, outcome_cache);
        return specify_prediction(expression_outcome, expr.type, context);
    }
    if (expr instanceof Method_Expression) {
        return context.typer.datum_outcome(expr);
    }
    if (expr instanceof Instance_Expression) {
        return context.typer.typed_outcome(expr.bundle);
    }
    if (expr instanceof Slot_Read_Expression) {
        infer_outcome(expr.lhs, context, outcome_cache);
        const slot = expr.bundle.class?.slots.find(s => s.name == expr.slot);
        return context.typer.typed_outcome(slot?.type as any || Runtime.instance.lookup('everything'));
    }
    if (expr instanceof Slot_Write_Expression) {
        return infer_outcome(expr.rhs, context, outcome_cache);
    }
    if (expr instanceof Exit_Expression) {
        let object = context.lookup(expr);
        if (!object) {
            object = new Typer_object(expr.name, combine_outcomes());
            context.objects.set(expr, object);
        }
        const outcome = infer_outcome(expr.expression, context, outcome_cache);
        object.add_outcome(outcome);
        return object.outcome;
    }
    if (expr instanceof Exit_Call_Expression) {
        const object = context.lookup(expr.exit);
        if (object === undefined) {
            const message = `early exit ${JSON.stringify(expr.exit.name.spelling)} called outside exit's definition scope`;
            throw new Typer_Error(message, expr.position);
        }
        const outcome = infer_outcome(expr.expression, context, outcome_cache);
        object.add_outcome(outcome);
        return outcome;
    }
    throw new Error('unknown expression');
}

class Method_Dispatch_Cache_Entry {
    method: Predicted_Outcome;
    dispatch: Method_Call_Dispatcher[];

    constructor(method: Predicted_Outcome) {
        this.method = method;
        this.dispatch = [];
    }

    lookup(parameters: Predicted_Outcome[], spread: boolean) {
        search: for (var k = 0; k < this.dispatch.length; k++) {
            const dispatch = this.dispatch[k];
            if (dispatch.spread != spread)
                continue search;
            if (dispatch.parameters.length != parameters.length)
                continue search;
            for (var p = 0; p < parameters.length; p++)
                if (!equal_outcomes(parameters[p], dispatch.parameters[p]))
                    continue search;
            return dispatch;
        }
        return undefined;
    }
}

class Method_Dispatch_Cache {
    cache: Method_Dispatch_Cache_Entry[];
    constructor() { this.cache = []; }

    lookup_entry(method: Predicted_Outcome) {
        for (var i = 0; i < this.cache.length; i++) {
            const entry = this.cache[i];
            if (!equal_outcomes(entry.method, method))
                continue;
            return entry;
        }
        return undefined;
    }

    lookup(method: Predicted_Outcome, parameters: Predicted_Outcome[], spread: boolean) {
        const entry = this.lookup_entry(method);
        if (!entry) return undefined;
        return entry.lookup(parameters, spread);
    }

    save(d: Method_Call_Dispatcher) {
        let entry = this.lookup_entry(d.method);
        if (!entry) {
            entry = new Method_Dispatch_Cache_Entry(d.method);
            this.cache.push(entry);
        }
        let dispatcher = entry.lookup(d.parameters, d.spread);
        if (!dispatcher) 
            entry.dispatch.push(d);
        else dispatcher.queue = d.queue;
    }
}

export function infer_method_expression_outcome(context: Typer_Context, m: Method_Expression, params: Predicted_Outcome[], spread: boolean, outcome_cache = new Map()): Predicted_Outcome {
    if (outcome_cache.has(m))
        return outcome_cache.get(m) as Predicted_Outcome;
    outcome_cache.set(m, context.typer.typed_outcome(m.result_type));
    const method_context = new Typer_Context(context);
    const formal = m.formal_parameters;
    const numeric = formal.required.length + formal.optional.length;
    for (let scope = m.formal_parameters.scope; scope; scope = scope.parent as Scope)
        if (scope instanceof Generic_Parameter_Scope) for (let [name, defn] of scope.definitions)
            if (defn instanceof Known_Definition) method_context.add_outcome(name, context.typer.datum_outcome(defn.value));
    for (var i = 0; i < numeric; i++) {
        const param = i < formal.required.length ? 
            formal.required[i] : formal.optional[i - formal.required.length];
            method_context.add_outcome(param.name, params[i]);
    }
    const $poly = Runtime.instance;
    const internal_array = $poly.lookup('internal_array');
    if (formal.rest) {
        const type = instantiate_generic_bundle(internal_array, [formal.rest.type]) as Bundle;
        const outcome = method_context.typer.typed_outcome(type);
        method_context.add_outcome(formal.rest.name, outcome);
    }
    if (formal.named.length > 0) throw new Error(`TODO`);
    const body_context = new Typer_Context(method_context);
    const body_outcome = infer_outcome(m.body, body_context, outcome_cache);
    
    let final_outcome = specify_prediction(body_outcome, m.result_type, method_context);
    outcome_cache.set(m, final_outcome);
    return final_outcome;
}

export function infer_method_call_outcome(context: Typer_Context, expr: Call_Expression, outcome_cache = new Map()) {
    if (outcome_cache.has(expr))
        return outcome_cache.get(expr) as Predicted_Outcome;
    const $poly = Runtime.instance;
    const dispatcher = method_call_dispatcher(context, expr, outcome_cache);
    if (!dispatcher || dispatcher.queue.length == 0)
        return context.typer.typed_outcome($poly.lookup('everything'));
    let outcome = combine_outcomes();
    for (let m of dispatcher.queue) {
        const head = $poly.method_heads[m.id];
        const method_expr = $poly.method_expressions[m.id];
        if (!method_expr) {
            outcome = combine_outcomes(
                outcome, context.typer.typed_outcome(head.result));
            continue;
        }
        outcome = combine_outcomes(outcome, infer_method_expression_outcome(
            context, method_expr, dispatcher.parameters, expr.spread, outcome_cache));
    }
    if (outcome instanceof Outcome_Oneof && outcome.outcomes.size == 0)
        return context.typer.typed_outcome($poly.lookup('everything'));
    return outcome;
}

export class Method_Call_Dispatcher {
    method: Predicted_Outcome;
    parameters: Predicted_Outcome[];
    spread: boolean;

    proved: Set<Runtime_Method_Datum>;
    queue: Runtime_Method_Datum[];

    constructor(method: Predicted_Outcome, parameters: Predicted_Outcome[], spread: boolean, proved: Set<Runtime_Method_Datum>, queue: Runtime_Method_Datum[]) {
        this.method = method;
        this.parameters = parameters;
        this.spread = spread;
        this.proved = proved;
        this.queue = queue;
    }
}

export function enforce_requirement(bundle: Bundle, req: Method_Head) {
    // TODO
}

export function method_call_dispatcher(context: Typer_Context, expr: Call_Expression, outcome_cache = new Map()): Method_Call_Dispatcher | undefined {
    const method = infer_outcome(expr.method, context, outcome_cache);
    const parameters = expr.parameters.map(p => infer_outcome(p, context, outcome_cache));

    const existing = Typer_Context.dispatch_cache.lookup(method, parameters, expr.spread);
    if (existing) return existing;

    if (method instanceof Outcome_Type)
        return undefined;

    let possibly_applicable_methods: Set<Runtime_Method_Datum> = new Set();
    let applicable_methods: Set<Runtime_Method_Datum> = new Set();
    const add_method_outcome = (m: Runtime_Method_Datum) => {
        if (predict_method_call_applicable(context, m.id, parameters, expr.spread)) 
            possibly_applicable_methods.add(m);
        if (predict_method_call_applicable(context, m.id, parameters, expr.spread, true)) 
            applicable_methods.add(m);
    }

    const proccess_datum_outcome = (method: Datum) => {
        if (method instanceof Bundle) {
            if (!method.function) 
                return non_method_expression_error(expr) as any;
            for (let m of method.function.methods)
                add_method_outcome(m);
            if (!method.function.generic_methods) return;
            for (let gm of method.function.generic_methods) {
                const applicable = predict_generic_method_call_applicable(context, gm, parameters, expr.spread);
                if (Array.isArray(applicable)) for (let m of applicable) 
                    add_method_outcome(m);
            }
            return;
        }
        if (method instanceof Runtime_Method_Datum) {
            add_method_outcome(method);
            return;
        }
        if (method instanceof Method_Expression) {
            proccess_datum_outcome(method_expression_to_datum(method));
            return;
        }
        return non_method_expression_error(expr) as any;
    }

    if (method instanceof Outcome_Datum) {
        proccess_datum_outcome(method.datum);
    } else for (let outcome of method.outcomes) {
        if (outcome instanceof Outcome_Type)
            return undefined;
        proccess_datum_outcome(outcome.datum);
    }

    const general_dispatch_queue = Array.from(possibly_applicable_methods).
        sort((a, b) => compare_methods(a.id, b.id));
    const optimized_dispatch_queue: Runtime_Method_Datum[] = []; 

    let last_applicable_method_index = general_dispatch_queue.length;
    for (var i = 0; i < general_dispatch_queue.length; i++) 
        if (applicable_methods.has(general_dispatch_queue[i])) 
            last_applicable_method_index = i + 1;

    for (var i = 0; i < last_applicable_method_index; i++) {
        const m = general_dispatch_queue[i];
        optimized_dispatch_queue.push(m);
        if (applicable_methods.has(m)) {
            const head = Runtime.instance.method_heads[m.id];
            if (head.no_parameters) break;
            if (head.sealed) break;
            if (i == 0 && Typer_Context.enable_aggressive_inlining) break;
        }
    }

    const dispatcher =  new Method_Call_Dispatcher(
        method,
        parameters,
        expr.spread,
        applicable_methods, 
        optimized_dispatch_queue);
    Typer_Context.dispatch_cache.save(dispatcher);
    return dispatcher;
}

export function non_method_expression_error(expr: Expression) {
    let message = `trying to call non-method expression!`;
    if (expr instanceof Call_Expression && expr.method instanceof Name)
        message = `trying to call non-method expression ${JSON.stringify(expr.method.spelling)}!`;
    throw new Typer_Error(message);
}

export class Typer_Error extends Poly_Error {
    constructor(message: string, position?: Source_Position) {
        super(position, 'type error', message);   
    }
}