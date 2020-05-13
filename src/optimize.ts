import { Expression, Quotation, Block_Scope, Prog_Expression, If_Expression, Call_Expression, Assigment_Expression, Known_Definition, Constant_Definition, Variable_Definition, Method_Expression, Instance_Expression, Slot_Read_Expression, Slot_Write_Expression, Scope, lookup, expand_definition, Formal_Parameter_Definition, Definition, copy_expression, lookup_known_definition, Generic_Parameter_Scope, Compound_Expression, Exit_Expression, Exit_Call_Expression } from "./expression";
import { Typer_Context, Outcome_Type, Predicted_Outcome, infer_outcome, Outcome_Datum, specify_prediction, equal_outcomes, combine_outcomes, predict_most_general_outcome_type, method_call_dispatcher } from "./typer";
import { Char, Name, Datum, Bundle, Macro_Context } from "./datum";
import { Runtime } from "./js_runtime";
import { instantiate_generic_bundle, classof, is_subtype_or_equal } from "./class";
import { Poly_Error } from "./token";
import { Runtime_Method_Datum, method_expression_to_datum } from "./method";
import { eval_expression } from "./eval";

export function optimize(context: Typer_Context, expr: Expression, scope: Scope, visited: Set<Expression> = new Set(), outcome_cache = new Map()): Expression {
    try {
        return _optimize(context, expr, scope, visited, outcome_cache);
    } catch(e) {
        if (e instanceof Poly_Error && !e.position && expr instanceof Compound_Expression)
            e.position = expr.position;
        throw e;
    }
}

export function _optimize(context: Typer_Context, expr: Expression, scope: Scope, visited: Set<Expression> = new Set(), outcome_cache = new Map()): Expression {
    switch (typeof expr) {
    case 'undefined':
        return new Quotation(false);
    case 'boolean':
        return new Quotation(expr);
    case 'number':
        return expr;
    case 'string':
        return expr;
    }
    if (expr instanceof Char) {
        return expr;
    }
    if (expr instanceof Quotation) {
        return expr;
    }
    if (expr instanceof Name) {
        const defn = lookup(scope, expr);
        if (defn instanceof Variable_Definition) 
            return expr;
        const outcome = infer_outcome(expr, context, outcome_cache);
        if (outcome instanceof Outcome_Datum) {
            switch (typeof outcome.datum) {
            case 'undefined':
                return new Quotation(false);
            case 'number':
                return outcome.datum;
            case 'string':
                return outcome.datum;
            case 'boolean':
                return new Quotation(outcome.datum);
            }
            if (outcome.datum instanceof Method_Expression)
                return outcome.datum;
            return new Quotation(outcome.datum);
        }
        return expr;
    }
    if (visited.has(expr)) 
        return expr;
    infer_outcome(expr, context, outcome_cache);
    visited.add(expr);
    const is_useful_expression = (body_expr: Expression, scope: Scope) => {
        if (body_expr instanceof Definition) {
            const mentions = infer_mentions_count(expr, scope);
            if (!mentions.has(body_expr))
                return false;
        }
        return true;
    }
    if (expr instanceof Block_Scope) {
        const body_context = new Typer_Context(context);
        body_context.consume_scope(expr); 

        expr.expressions = expr.expressions.map(
            body_expr => optimize(body_context, body_expr, expr, visited, outcome_cache));
        expr.expressions = expr.expressions.filter(
            body_expr => is_useful_expression(body_expr, expr));
        return expr;
    }
    if (expr instanceof Prog_Expression) {
        expr.expressions = expr.expressions.map(
            body_expr => optimize(context, body_expr, scope, visited, outcome_cache));
        return expr;
    }
    if (expr instanceof If_Expression) {
        const if_context = new Typer_Context(context);
        if (expr.test instanceof Name)
            if_context.delete_outcome(expr.test, if_context.typer.datum_outcome(false));
    
        infer_outcome(expr.test, if_context, outcome_cache);
        infer_outcome(expr.consequent, if_context, outcome_cache);
        infer_outcome(expr.alternate, if_context, outcome_cache);

        expr.test = optimize(if_context, expr.test, scope, visited, outcome_cache);
        expr.consequent = optimize(if_context, expr.consequent, scope, visited, outcome_cache);
        expr.alternate = optimize(if_context, expr.alternate, scope, visited, outcome_cache);

        const $poly = Runtime.instance;
        const test_outcome = infer_outcome(expr.test, if_context, outcome_cache);

        const resolve_condition = (outcome: Predicted_Outcome): number => {
            if (outcome instanceof Outcome_Datum)
                return outcome.datum !== false ? 1 : -1;
            if (outcome instanceof Outcome_Type)
                return $poly.call(0, $poly.lookup('in'), false, outcome.type) === false ?
                    1 : (outcome.type == classof(false) ? -1 : 0);
            let resolution: number = 0;
            for (let out of outcome.outcomes) {
                const out_resolution = resolve_condition(out);
                if (resolution === undefined) resolution = out_resolution;
                if (resolution !== out_resolution) return 0;
            }
            return resolution as number;
        }
        const resolution = resolve_condition(test_outcome);
        const enabled = false;
        // not stable yet...
        if (enabled)
            return resolution === 0 ? expr : (resolution > 0 ? expr.consequent : expr.alternate);
        return expr;
    }
    if (expr instanceof Call_Expression) {
        expr.method = optimize(context, expr.method, scope, visited, outcome_cache);
        expr.parameters = expr.parameters.map(p => optimize(context, p, scope, visited, outcome_cache));

        const dispatcher = method_call_dispatcher(context, expr);
        if (!dispatcher) return expr;

        if (dispatcher.queue.length > 0 && dispatcher.proved.has(dispatcher.queue[0]) && dispatcher.proved.size == 1) {
            const method = dispatcher.queue[0];
            expr.method = new Quotation(method);
            if (method.lambda == instantiate_generic_bundle)
                return eval_known_call_expression(expr, scope);
            
            const inlined = inline_call_expression(expr, scope, outcome_cache);
            if (expr != inlined) return optimize(context, inlined, scope, visited, outcome_cache);
        } 

        return expr;
    }
    if (expr instanceof Assigment_Expression) {         
        expr.rhs = optimize(context, expr.rhs, scope, visited, outcome_cache);
        const rhs = infer_outcome(expr.rhs, context, outcome_cache);
        const object = context.lookup(expr.lhs);
        object?.add_outcome(rhs);
        return expr;
    }
    if (expr instanceof Known_Definition) {
        return expr;
    }
    if (expr instanceof Constant_Definition) {
        expr.expression = optimize(context, expr.expression, scope, visited, outcome_cache);
        // const outcome_type = predict_most_general_outcome_type(infer_outcome(expr.expression, context));
        // if (subtype_lte(outcome_type, expr.type) && !subtype_lte(expr.type, outcome_type))  
        //    expr.type = outcome_type;
        return expr;
    }
    if (expr instanceof Variable_Definition) {
        expr.expression = optimize(context, expr.expression, scope, visited, outcome_cache);
        return expr;
    }
    if (expr instanceof Method_Expression) {
        const head_context = new Typer_Context(context);
        head_context.consume_formal_parameters(expr.formal_parameters);
        const body_context = new Typer_Context(head_context);
        expr.body = optimize(body_context, expr.body, expr.formal_parameters.scope, visited, outcome_cache);
        return expr;
    }
    if (expr instanceof Instance_Expression) {
        expr.expressions = expr.expressions.map(e => optimize(context, e, scope, visited, outcome_cache));
        return expr;
    }
    if (expr instanceof Slot_Read_Expression) {
        expr.lhs = optimize(context, expr.lhs, scope, visited, outcome_cache);
        return expr;
    }
    if (expr instanceof Slot_Write_Expression) {
        expr.lhs = optimize(context, expr.lhs, scope, visited, outcome_cache);
        expr.rhs = optimize(context, expr.rhs, scope, visited, outcome_cache);
        return expr;
    }
    if (expr instanceof Exit_Expression) {
        expr.expression = optimize(context, expr.expression, scope, visited, outcome_cache);
        return expr;
    }   
    if (expr instanceof Exit_Call_Expression) {
        expr.expression = optimize(context, expr.expression, scope, visited, outcome_cache);
        return expr;
    }
    throw new Error('unknown expression');
}

export function infer_call_expression_method_id(call_expr: Call_Expression): number | undefined {
    if (call_expr.method instanceof Method_Expression && !call_expr.method.generic_parameters)
        return method_expression_to_datum(call_expr.method).id;
    if (call_expr.method instanceof Quotation && call_expr.method.datum instanceof Runtime_Method_Datum)
        return call_expr.method.datum.id;
    return undefined;
}

export function inline_call_expression(call_expr: Call_Expression, scope: Scope, outcome_cache = new Map()): Expression {
    const method_id = infer_call_expression_method_id(call_expr);
    if (method_id === undefined) return call_expr;
    const method_expr = Runtime.instance.method_expressions[method_id];
    if (!method_expr) return call_expr;

    if (call_expr.spread) return call_expr;
    if (method_expr.formal_parameters.rest !== undefined) return call_expr;
    
    const formal = method_expr.formal_parameters;
    if (formal.named.length > 0)
        return call_expr;
        
    const recursive_calls: Map<Method_Expression, Call_Expression_In_Scope[]> = new Map();
    infer_recursive_calls(method_expr, scope, recursive_calls);
    const method_recursive_calls = recursive_calls.get(method_expr) || [];

    if (method_recursive_calls.length > 0) {
        if (!formal.have_parameters) // nothing to do here...
            return call_expr;
        if (formal.optional.length > 0 || formal.named.length > 0 || !!formal.rest) 
            // may be implemented later...
            return call_expr;
        // if parameter type is too general (e.g. "everything", which is common case for "for" loops),
        // we can provide more specific method formal parameters based on call expression outcomes
        const outcomes: Predicted_Outcome[] = [];
        for (let call_in_scope of method_recursive_calls) {
            const call = call_in_scope.call;
            if (method_id !== infer_call_expression_method_id(call))
                return call_expr;
            if (call_expr == call)
                continue;
            const context = Typer_Context.from_scope(call_in_scope.scope);
            const parameters = call.parameters.map(p => infer_outcome(p, context, outcome_cache));
            const length = call.spread ? call.parameters.length - 1 : call.parameters.length;
            for (var i = 0; i < length; i++) 
                outcomes[i] = outcomes[i] ?
                    combine_outcomes(outcomes[i], parameters[i]) :
                    parameters[i];
        }
        const more_specific_formals: Map<Formal_Parameter_Definition, Datum> = new Map();
        for (var i = 0; i < formal.required.length; i++) {
            const outcome = outcomes[i];
            if (!outcome) continue;
            const param = formal.required[i];
            const type = predict_most_general_outcome_type(outcome);   
            if (is_subtype_or_equal(type, param.type) && !is_subtype_or_equal(param.type, type))
                more_specific_formals.set(param, type);
        }

        if (more_specific_formals.size == 0) 
            return call_expr;
            
        const method_copy = copy_expression(method_expr) as Method_Expression;
        const copy_formal = method_copy.formal_parameters;
        for (var i = 0; i < formal.required.length; i++) {
            const param = formal.required[i];
            const copy_param = copy_formal.required[i];
            if (!more_specific_formals.has(param))
                continue;
            const new_type = more_specific_formals.get(param) as Datum;
            copy_param.type = new_type;
        }
        return new Call_Expression(
            call_expr.position,
            method_copy,
            call_expr.parameters,
            call_expr.spread);
    }

    const expression_weight = infer_expressions_count(method_expr, scope);
    if (expression_weight.logical_count > 15)
        return call_expr;

    const head = new Block_Scope(scope, [], 'head');
    let tail = head;
    var index = 0;

    const mentions_in_body = (defn: Definition) =>  
        infer_mentions_count(method_expr.body, formal.scope).get(defn) || 0;
    const add_definition = (name: Name, defn: Definition) => {
        const prog = expand_definition(tail, name, defn) as Prog_Expression;
        tail.expressions.push(...prog.expressions);
        tail = tail.expressions[tail.expressions.length - 1] as Block_Scope;
    }
    const add_parameter = (p: Formal_Parameter_Definition, i: number) => {
        if (mentions_in_body(p) <= 0) return;
        const defn = new Constant_Definition(p.position, p.name, p.type, call_expr.parameters[i]);
        add_definition(p.name, defn);
    }
    const add_known = (name: Name, p: Known_Definition) => {
        if (mentions_in_body(p) <= 0) return;
        const defn = new Known_Definition(p.position, p.name, p.value);
        add_definition(name, defn);
    }

    const copied = new Map<any, any>();
    for (let scope = formal.scope; scope; scope = scope.parent as Scope) {
        if (scope instanceof Generic_Parameter_Scope) for (let [name, defn] of scope.definitions) {
            if (defn instanceof Known_Definition) add_known(name, defn);
        } else if (scope instanceof Block_Scope) for (let expr of scope.expressions) {
            if (expr instanceof Exit_Expression) copied.set(expr, expr);
        }
    }

    for (let p of formal.required) add_parameter(p, index++);
    for (let p of formal.optional) add_parameter(p, index++);
    if (formal.rest && mentions_in_body(formal.rest) > 0) {
        const p = formal.rest;
        const internal_array = lookup_known_definition(scope, Name.make('internal_array'));
        const type = instantiate_generic_bundle(internal_array as Bundle, [p.type]);
        const defn = new Constant_Definition(p.position, p.name, type as Bundle, 
            new Instance_Expression(p.position, type as Bundle, call_expr.parameters.slice(index)));
        add_definition(p.name, defn);
    }
    copied.set(method_expr.formal_parameters.scope, tail);
    const body = copy_expression(method_expr.body, copied);
    
    const body_context = Typer_Context.from_scope(tail);
    const body_outcome = infer_outcome(body, body_context, outcome_cache);
    const specified_outcome = specify_prediction(body_outcome, method_expr.result_type, body_context);

    if (!equal_outcomes(specified_outcome, body_outcome)) {
        const context = new Macro_Context(tail);
        const defn_name = Name.make('temp', context);
        const defn = new Constant_Definition(method_expr.position, defn_name, method_expr.result_type, body);
        add_definition(defn_name, defn);
        tail.expressions.push(defn_name);
    } else tail.expressions.push(body);
    return head;
}

export function eval_known_call_expression(call: Call_Expression, scope: Scope) {
    const parameters: Expression[] = [];
    for (let p of call.parameters) {
        if (typeof p == 'number' || typeof p == 'string' || p instanceof Char) {
            parameters.push(p);
            continue;
        }
        if (p instanceof Quotation) {
            parameters.push(p);
            continue;
        }
        if (p instanceof Name) {
            const defn = lookup(scope, p);
            if (defn instanceof Known_Definition) 
                parameters.push(new Quotation(defn.value));
            else return call;
        }
        return call;
    }
    const quoted = new Call_Expression(
        call.position, 
        call.method, 
        parameters, 
        call.spread);
    return new Quotation(eval_expression(quoted, scope));
}

class Call_Expression_In_Scope {
    scope: Scope;
    call: Call_Expression;

    constructor(scope: Scope, call: Call_Expression) {
        this.scope = scope;
        this.call = call;
    }
}

export function infer_recursive_calls(expr: Expression, scope: Scope, calls: Map<Method_Expression, Call_Expression_In_Scope[]> = new Map(), visited: Set<any> = new Set()) {
    if (visited.has(expr)) return calls;
    visited.add(expr);

    if (expr instanceof If_Expression) {
        infer_recursive_calls(expr.test, scope, calls, visited);
        infer_recursive_calls(expr.consequent, scope, calls, visited);
        infer_recursive_calls(expr.alternate, scope, calls, visited);
    }
    else if (expr instanceof Method_Expression) {
        infer_recursive_calls(expr.body, expr.formal_parameters.scope, calls, visited);
    }
    else if (expr instanceof Call_Expression) {
        infer_recursive_calls(expr.method, scope, calls, visited);
        for (let param of expr.parameters) 
            infer_recursive_calls(param, scope, calls, visited);

        const add_call = (method_expr: Method_Expression) =>  {
            if (!calls.has(method_expr)) calls.set(method_expr, []);
            const expr_calls = calls.get(method_expr) as Call_Expression_In_Scope[];
            for (let call of expr_calls) if (call.call == expr)
                return;
            expr_calls.push(new Call_Expression_In_Scope(scope, expr));
        }
        const dispatcher = method_call_dispatcher(Typer_Context.from_scope(scope), expr);
        if (!dispatcher) return;
        for (let m of dispatcher.queue) {
            const method_expression = Runtime.instance.method_expressions[m.id];
            if (!method_expression) continue;
            add_call(method_expression);
            infer_recursive_calls(method_expression, scope, calls, visited);
        }
    }
    else if (expr instanceof Prog_Expression) {
        for (let body_expr of expr.expressions) 
            infer_recursive_calls(body_expr, scope, calls, visited);
    }
    else if (expr instanceof Block_Scope) {
        for (let body_expr of expr.expressions) 
            infer_recursive_calls(body_expr, expr, calls, visited);
    }
    else if (expr instanceof Assigment_Expression) {
        infer_recursive_calls(expr.rhs, scope, calls, visited);
    }
    else if (expr instanceof Instance_Expression) {
        for (let body_expr of expr.expressions) 
            infer_recursive_calls(body_expr, scope, calls, visited);
    }
    else if (expr instanceof Slot_Read_Expression) {
        infer_recursive_calls(expr.lhs, scope, calls, visited);
    } else if (expr instanceof Exit_Expression) {
        infer_recursive_calls(expr.expression, scope, calls, visited);
    } else if (expr instanceof Exit_Call_Expression) {
        infer_recursive_calls(expr.expression, scope, calls, visited);
    } else if (expr instanceof Slot_Write_Expression) {
        infer_recursive_calls(expr.lhs, scope, calls, visited);
        infer_recursive_calls(expr.rhs, scope, calls, visited);
    } else if (expr instanceof Variable_Definition) {
        infer_recursive_calls(expr.expression, scope, calls, visited);
    } else if (expr instanceof Constant_Definition) {
        infer_recursive_calls(expr.expression, scope, calls, visited);
    } else if (expr instanceof Quotation && expr.datum instanceof Runtime_Method_Datum) {
        const method_expr = Runtime.instance.method_expressions[expr.datum.id];
        if (method_expr) {
            infer_recursive_calls(method_expr, scope, calls, visited);
        }
    }
    return calls;
}

export function infer_mentions_count(expr: Expression, scope: Scope, visited: Set<Expression> = new Set(), mentions = new Map<Definition, number>()) {
    if (expr instanceof Name) { 
        const expr_defn = lookup(scope, expr)
        if (expr_defn) mentions.set(expr_defn, (mentions.get(expr_defn) || 0) + 1);
    }
    if (visited.has(expr)) return mentions;
    visited.add(expr);
    if (expr instanceof If_Expression) {
        infer_mentions_count(expr.test, scope, visited, mentions);
        infer_mentions_count(expr.consequent, scope, visited, mentions);
        infer_mentions_count(expr.alternate, scope, visited, mentions);
    }
    else if (expr instanceof Method_Expression) {
        infer_mentions_count(expr.body, expr.formal_parameters.scope, visited, mentions);
    }
    else if (expr instanceof Call_Expression) {
        infer_mentions_count(expr.method, scope, visited, mentions);
        for (let param of expr.parameters) 
            infer_mentions_count(param, scope, visited, mentions);
    }
    else if (expr instanceof Prog_Expression) {
        for (let body_expr of expr.expressions) 
            infer_mentions_count(body_expr, scope, visited, mentions);
    }
    else if (expr instanceof Block_Scope) {
        for (let body_expr of expr.expressions) 
            infer_mentions_count(body_expr, expr, visited, mentions);
    }
    else if (expr instanceof Assigment_Expression) {
        infer_mentions_count(expr.lhs, scope, visited, mentions);
        infer_mentions_count(expr.rhs, scope, visited, mentions);
    }
    else if (expr instanceof Instance_Expression) {
        for (let body_expr of expr.expressions) 
            infer_mentions_count(body_expr, scope, visited, mentions);
    }
    else if (expr instanceof Slot_Read_Expression) {
        infer_mentions_count(expr.lhs, scope, visited, mentions);
    }
    else if (expr instanceof Slot_Write_Expression) {
        infer_mentions_count(expr.lhs, scope, visited, mentions);
        infer_mentions_count(expr.rhs, scope, visited, mentions);
    } else if (expr instanceof Variable_Definition) {
        infer_mentions_count(expr.expression, scope, visited, mentions);
    } else if (expr instanceof Constant_Definition) {
        infer_mentions_count(expr.expression, scope, visited, mentions);
    } else if (expr instanceof Exit_Expression) {
        infer_mentions_count(expr.expression, scope, visited, mentions);
    } else if (expr instanceof Exit_Call_Expression) {
        infer_mentions_count(expr.expression, scope, visited, mentions);
    } else if (expr instanceof Quotation && expr.datum instanceof Runtime_Method_Datum) {
        const method_expr = Runtime.instance.method_expressions[expr.datum.id];
        if (method_expr) infer_mentions_count(method_expr, scope, visited, mentions);
    } else if (expr instanceof Quotation && expr.datum instanceof Bundle) {
        if (expr.datum.function) {
            for (let m of expr.datum.function.methods) {
                const method_expr = Runtime.instance.method_expressions[m.id];
                if (method_expr) infer_mentions_count(method_expr, scope, visited, mentions);
            }
            if (expr.datum.function.generic_methods) for (let gm of expr.datum.function.methods) {
                const method_expr = Runtime.instance.generic_method_expressions[gm.id];
                if (method_expr) infer_mentions_count(method_expr, scope, visited, mentions);
            }
        }
    } else if (expr instanceof Known_Definition && expr.value instanceof Bundle) {
        if (expr.value.function) for (let m of expr.value.function.methods) {
            const method_expr = Runtime.instance.method_expressions[m.id];
            if (method_expr) infer_mentions_count(method_expr, scope, visited, mentions);
        }
        if (expr.value.function && expr.value.function.generic_methods) for (let gm of expr.value.function.methods) {
            const method_expr = Runtime.instance.generic_method_expressions[gm.id];
            if (method_expr) infer_mentions_count(method_expr, scope, visited, mentions);
        }
    }
    return mentions;
}


class Expression_Counter {
    logical_count: number;

    constructor() {
        this.logical_count = 0;
    }

    add(expr: Expression) {
        const logical = [
            If_Expression,
            Call_Expression,
            Definition,
            Assigment_Expression,
            Instance_Expression,
            Slot_Write_Expression,
            Slot_Read_Expression,
        ]
        for (let l of logical) if (expr instanceof l) {
            this.logical_count++;
            break;
        }
    }
}

export function infer_expressions_count(expr: Expression, scope: Scope, visited: Set<Expression> = new Set(), counter = new Expression_Counter()) {
    if (expr instanceof Name) {
        counter.add(expr);
        return counter;
    }
    if (visited.has(expr)) return counter;
    visited.add(expr);
    if (expr instanceof If_Expression) {
        counter.add(expr);
        infer_expressions_count(expr.test, scope, visited, counter);
        infer_expressions_count(expr.consequent, scope, visited, counter);
        infer_expressions_count(expr.alternate, scope, visited, counter);
    }
    else if (expr instanceof Method_Expression) {
        counter.add(expr);
        infer_expressions_count(expr.body, expr.formal_parameters.scope, visited, counter);
    }
    else if (expr instanceof Call_Expression) {
        counter.add(expr);
        infer_expressions_count(expr.method, scope, visited, counter);
        for (let param of expr.parameters) 
            infer_expressions_count(param, scope, visited, counter);
    }
    else if (expr instanceof Prog_Expression) {
        counter.add(expr);
        for (let body_expr of expr.expressions) 
            infer_expressions_count(body_expr, scope, visited, counter);
    }
    else if (expr instanceof Block_Scope) {
        for (let body_expr of expr.expressions) 
            infer_expressions_count(body_expr, expr, visited, counter);
    }
    else if (expr instanceof Assigment_Expression) {
        counter.add(expr);
        infer_expressions_count(expr.lhs, scope, visited, counter);
        infer_expressions_count(expr.rhs, scope, visited, counter);
    }
    else if (expr instanceof Instance_Expression) {
        counter.add(expr);
        for (let body_expr of expr.expressions) 
            infer_expressions_count(body_expr, scope, visited, counter);
    }
    else if (expr instanceof Slot_Read_Expression) {
        counter.add(expr);
        infer_expressions_count(expr.lhs, scope, visited, counter);
    }
    else if (expr instanceof Slot_Write_Expression) {
        counter.add(expr);
        infer_expressions_count(expr.lhs, scope, visited, counter);
        infer_expressions_count(expr.rhs, scope, visited, counter);
    } else if (expr instanceof Variable_Definition) {
        counter.add(expr);
        infer_expressions_count(expr.expression, scope, visited, counter);
    } else if (expr instanceof Constant_Definition) {
        counter.add(expr);
        infer_expressions_count(expr.expression, scope, visited, counter);
    } else if (expr instanceof Exit_Expression) {
        counter.add(expr);
        infer_expressions_count(expr.expression, scope, visited, counter);
    } else if (expr instanceof Exit_Call_Expression) {
        counter.add(expr);
        infer_expressions_count(expr.expression, scope, visited, counter);
    } else if (expr instanceof Known_Definition && expr.value instanceof Bundle) {
        if (expr.value.function) for (let m of expr.value.function.methods) {
            const expr = Runtime.instance.method_expressions[m.id];
            if (expr) infer_expressions_count(expr, expr.formal_parameters.scope, visited, counter);
        }
    } else if (expr instanceof Quotation && expr.datum instanceof Runtime_Method_Datum) {
        const method_expr = Runtime.instance.method_expressions[expr.datum.id];
        if (method_expr) infer_expressions_count(method_expr, method_expr.formal_parameters.scope, visited, counter);
    }
    return counter;
}