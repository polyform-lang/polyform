import { Scope, Expression, lookup, Known_Definition, Quotation, If_Expression, Block_Scope, Prog_Expression, Call_Expression, Assigment_Expression, Variable_Definition, Constant_Definition, Method_Expression, Instance_Expression, Slot_Write_Expression, Slot_Read_Expression, Module, lookup_known_definition, Formal_Parameters, Definition } from "./expression";
import { Name, Datum, Char, Bundle, Internal_Array } from "./datum";
import { Runtime, Call_Stack } from "./js_runtime";
import { JS_generate_class_prototype } from "./js_compile";
import { Source_Position } from "./token";
import { Execution_Error, select_method, Runtime_Method_Datum, method_expression_to_datum } from "./method";
import { instantiate_internal_array } from "./class";

export class Interpreter_Stack_Entry {
    scope: Scope;
    datums?: Map<Name, Datum>;
    definitions?: Map<Name, Definition>;

    constructor(scope: Scope) {
        this.scope = scope;
        this.datums = undefined;
    }
}

// NOTE: TODO: Interpreter is in placeholder state and
// does not support many language features right now, for example closures.
// It can be used only for very simple cases.

// Simple and very slow interpreter for arbitrary polyform expressions.
// Primary used for compile-time evaluations, because as it turns out,
// even such slow interpreter 4-5 faster than compiling expressions to js at compile-time. 
// However, if you want to enable js-compilation for compile-time expressions 
// search "@isolated_computations" in codebase for instructions.
export class Interpreter {
    readonly stack: Interpreter_Stack_Entry[];
    readonly call_stack: Call_Stack;
    readonly module: Module;
    readonly scope: Scope;

    constructor(scope: Scope, call_stack?: Call_Stack) {
        this.stack = [];
        this.scope = scope;
        this.module = scope.root() as Module;
        this.call_stack = call_stack ? 
            call_stack : Runtime.instance.call_stack;
    }

    push(scope: Scope) { 
        const entry = new Interpreter_Stack_Entry(scope);
        this.stack.push(entry); 
        return this.stack.length - 2;
    }

    pop(index?: number) { 
        if (index === undefined) this.stack.pop(); 
        else this.stack.length = index;
    }

    fetch(name: Name): Datum {
        for (var i = this.stack.length - 1; i >= 0; i--) {
            const entry = this.stack[i];
            const local = entry.datums ?
                entry.datums.get(name) : undefined;
            if (local !== undefined) return local as Datum;
        }
        // if (name.context instanceof Macro_Context)
        const defn = lookup(this.stack[this.stack.length - 1].scope, name);
        if (defn instanceof Known_Definition)
            return defn.value;
        throw new Execution_Error(
            this.call_stack.tail_source_position(), 
            `unresolved name ${JSON.stringify(name.spelling)}`,
            this.call_stack);
    }
    
    assign(name: Name, value: Datum, position: Source_Position) {
        for (var i = this.stack.length - 1; i >= 0; i--) {
            const entry = this.stack[i];
            if (entry.datums && entry.datums.has(name)) { // TODO check assignable
                entry.datums.set(name, value);
                const defn = entry.definitions?.get(name) as Definition;
                if (!defn.assignable()) throw new Execution_Error(
                    position,
                    `definition ${JSON.stringify(name.spelling)} is not assignable`,
                    this.call_stack);
                return value;
            }
        }
        // TODO
        throw new Error(`unresolved name ${JSON.stringify(name.spelling)}`);
    }

    declare(name: Name, value: Datum, defn: Definition) {
        const entry = this.stack[this.stack.length - 1];
        if (!entry.datums) entry.datums = new Map();
        if (!entry.definitions) entry.definitions = new Map();
        entry.datums.set(name, value);
        entry.definitions.set(name, defn);
        return value;
    }

    push_formals(parameters: Datum[], formal: Formal_Parameters) {
        this.push(formal.scope)

        let index = 0;
        for (let p of formal.required)
            this.declare(p.name, parameters[index++], p);
        for (let p of formal.optional)
            this.declare(p.name, parameters[index++], p);  
        // TODO named
        if (formal.rest) {
            const array = instantiate_internal_array(
                formal.rest.type, 
                parameters.slice(index));
            parameters.length = index;
            parameters.push(array);
            this.declare(formal.rest.name, array, formal.rest);
        }    
    }

    eval(expr: Expression): Datum {
        switch (typeof expr) {
            case 'number': return expr;
            case 'string': return expr;
            case 'boolean': return expr;
            case 'undefined': return false;
        }
        if (expr instanceof Char)
            return expr;
        if (expr instanceof Name) 
            return this.fetch(expr);
        if (expr instanceof Quotation) 
            return expr.datum;
        if (expr instanceof If_Expression) {
            if (this.eval(expr.test) !== false)
                return this.eval(expr.consequent);
            return this.eval(expr.alternate);
        }
        if (expr instanceof Slot_Read_Expression)  {
            const lhs = this.eval(expr.lhs);
            return lhs.getslot(expr.slot);
        }   
        if (expr instanceof Slot_Write_Expression) {
            const lhs = this.eval(expr.lhs);
            const rhs = this.eval(expr.rhs);
            lhs.setslot(expr.slot, rhs);
            return rhs;
        }
        if (expr instanceof Block_Scope) {
            this.push(expr);
            let result: Datum = false;
            for (var i = 0; i < expr.expressions.length; i++)
                result = this.eval(expr.expressions[i]);
            this.pop();
            return result;
        }
        if (expr instanceof Prog_Expression) {
            let result: Datum = false;
            for (var i = 0; i < expr.expressions.length; i++)
                result = this.eval(expr.expressions[i]);
            return result;
        }
        if (expr instanceof Call_Expression) {
            const $poly = Runtime.instance;
            let method = this.eval(expr.method);
            let method_expr: Method_Expression | undefined = undefined;
            const parameters = expr.parameters.map(e => this.eval(e));
            const location = Runtime.instance.call_stack.make_source_location(
                expr.position.name, expr.position.line);
            if (expr.spread) {
                const sequence = parameters.pop() as Datum;
                if (sequence instanceof Internal_Array)
                    parameters.push(...sequence.array);
                else if (Array.isArray(sequence))
                    parameters.push(...sequence);
                else {
                    const iterate = lookup_known_definition(this.module, 'iterate') as Bundle;
                    const more = lookup_known_definition(this.module, 'more?') as Bundle;
                    const next = lookup_known_definition(this.module, 'next') as Bundle;

                    let i = $poly.call(location, iterate, sequence);
                    while ($poly.call(location, more, sequence, i)) {
                        parameters.push($poly.call(location, next, sequence, i));
                        i = $poly.call(location, iterate, sequence, i);
                    }
                }
            }
            if (method instanceof Bundle) 
                method = select_method(location, method, parameters);
            if (method instanceof Runtime_Method_Datum)
                method_expr = $poly.method_expressions[method.id];
            
            if (!method_expr)
                return Runtime.instance.call(location, method, ...parameters);

            const stack_index = this.call_stack?.push(method, location);
            this.push_formals(parameters, method_expr.formal_parameters)
            const result = this.eval(method_expr.body);
            this.pop();
            this.call_stack?.pop(stack_index as number);

            return result;
        }
        if (expr instanceof Assigment_Expression) {
            const rhs = this.eval(expr.rhs);
            return this.assign(expr.lhs, rhs, expr.position);
        } 
        if (expr instanceof Known_Definition) 
            return this.declare(expr.name, expr.value, expr);
        if (expr instanceof Variable_Definition) 
            return this.declare(expr.name, this.eval(expr.expression), expr);
        if (expr instanceof Constant_Definition) 
            return this.declare(expr.name, this.eval(expr.expression), expr);

        if (expr instanceof Instance_Expression) {
            const jsclass = JS_generate_class_prototype(
                expr.bundle, this.module, Runtime.instance.mapper);
            const parameters = expr.expressions.map(e => this.eval(e));
            return new (jsclass.prototype as any)(...parameters);
        } 

        if (expr instanceof Method_Expression) 
            return method_expression_to_datum(expr);

        return false;
    }
}

export function eval_expression(expr: Expression, scope: Scope) {
    const interpreter = new Interpreter(scope);
    interpreter.push(scope);
    return interpreter.eval(expr);
}