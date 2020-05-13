import { Macro_Context, Name, Datum, Bundle, Char, Generic_Class_Instance_Maker, Internal_Array } from "./datum";
import { JS_object_mapper, JS_builtin_objects } from "./js_reconstruct";
import { Module, lookup, Method_Expression, Scope, Class_Expression, Method_Head, datum_string } from "./expression";
import { Source_Position } from "./token";
import { JS_statement, JS_eval } from "./js_compile";
import { instantiate_internal_array } from "./class";
import { Interpreter } from "./eval";
import { Runtime_Method_Head, Runtime_Method_Datum, Runtime_Generic_Method_Head, Runtime_Generic_Method_Datum, select_method, is_method_applicable, no_applicable_method_error, Method_Environment, Execution_Error } from "./method";

export class Runtime {
    mapper: JS_object_mapper;
    modules?: Module;

    method_expressions: Method_Expression[] = [];
    method_heads: Runtime_Method_Head[] = [];
    method_datums: Runtime_Method_Datum[] = [];
    method_index = 0;

    generic_method_expressions: Method_Expression[] = [];
    generic_method_heads: Runtime_Generic_Method_Head[] = [];
    generic_method_datums: Runtime_Generic_Method_Datum[] = [];
    generic_method_index = 0;

    instance_bundles: Bundle[] = [];
    
    generic_class_instances: Map<Bundle, Bundle[]> = new Map();
    generic_class_instance_constructors: Map<Bundle, Bundle> = new Map();
    generic_class_instance_makers: Map<Bundle, Generic_Class_Instance_Maker> = new Map();
    class_expressions: Class_Expression[] = [];
    class_index = 0;

    call_stack: Call_Stack;

    requirements: Map<Bundle, Method_Head[]> = new Map();

    static instance: Runtime;

    constructor(modules?: Module, mapper?: JS_object_mapper) {
        this.modules = modules;
        this.mapper = mapper ? mapper : new JS_object_mapper(JS_builtin_objects());
        this.call_stack = new Call_Stack();
    }

    get objmap(): any { return this.mapper.objects; }
    name(spelling: string | Name, context?: Macro_Context | Module) { return Name.make(spelling, context); }
    char(code: number | string) { return new Char(code); }
    source(file: string, line: number) { return new Source_Position(file, line); }
    newobj(proto: any, obj: any) { return Object.create(proto.prototype, Object.getOwnPropertyDescriptors(obj)); }

    module(name: string): Module {
        const defn = this.lookup(name);
        if (defn instanceof Module) return defn;
        else throw new Error(`unknown module "${name}"`);
    }

    lookup_cache = new Map();
    lookup(name: string) {
        const cached = this.lookup_cache.get(name);
        if (cached !== undefined) return cached;
        if (!this.modules) throw new Error(`runtime not initialized yet!`);
        const def = lookup(this.modules, this.name(name));
        this.lookup_cache.set(name, (def as any)?.value);
        if (def) return (def as any).value;
        else throw new Error(`invalid definition lookup "${name}"`);
    }

    spread_call(srcloc: number, fun: Datum, ...params: Datum[]) {
        const sequence = params.pop() as Datum;
        if (sequence instanceof Internal_Array) {
            params.push(...sequence.array);
            return this.call(srcloc, fun, ...params);
        }
        if (Array.isArray(sequence)) {
            params.push(...sequence);
            return this.call(srcloc, fun, ...params);
        }
        
        const iterate = this.lookup('iterate');
        const more = this.lookup('more?');
        const next = this.lookup('next');

        let i = this.call(srcloc, iterate, sequence);
        while (this.call(srcloc, more, sequence, i)) {
            const e = this.call(srcloc, next, sequence, i);
            params.push(e)
            i = this.call(srcloc, iterate, sequence, i);
        }
        return this.call(srcloc, fun, ...params);
    }
    
    call(srcloc: number, datum: Datum, ...params: Datum[]) {
        let method_datum: Runtime_Method_Datum | undefined = undefined;
        if (typeof datum == 'number')
            method_datum = this.method_datums[datum];
        else if (datum instanceof Bundle) 
            method_datum = select_method(srcloc, datum, params);
        else if (datum instanceof Runtime_Method_Datum)
            if (!is_method_applicable(datum.id, params))
                return no_applicable_method_error(datum, params);
            else method_datum = datum;
        if (!method_datum) 
            throw new Execution_Error(
                this.call_stack.make_source_position(srcloc), 
                `${datum_string(datum)} is not callable`,
                this.call_stack);
        const method_id = method_datum.id;

        if (method_datum.lambda === undefined || 
                (typeof method_datum.lambda == 'object' && (method_datum.lambda as any)[Method_Environment.Isolated] === undefined)) {
            const expression = this.method_expressions[method_datum.id];
            if (!expression)
                throw new Error('method not compiled!');
            const stackid = this.call_stack.push(method_datum, srcloc);

            const interpreter = new Interpreter(this.modules as Scope);
            interpreter.push_formals(params, expression.formal_parameters);
            const result = interpreter.eval(expression.body);
            interpreter.pop();
            this.call_stack.pop(stackid);
            return result;
        }
        
        const head = this.method_heads[method_id];
        if (params.length > head.positional.length && head.rest) {
            const rest = params.slice(head.positional.length);
            params.length = head.positional.length;
            params.push(instantiate_internal_array(head.rest, rest));
        } else if (head.rest) params.push(instantiate_internal_array(head.rest, []));

        let lambda = typeof method_datum.lambda == 'object' ?
            (method_datum.lambda as (Function | JS_statement)[])[Method_Environment.Isolated] :
            method_datum.lambda;
        if (typeof lambda != 'function') {
            lambda = JS_eval(lambda?.compile_statement() as string);
            if (typeof method_datum.lambda == 'object')
                (method_datum.lambda as Function[])[Method_Environment.Isolated] = lambda as Function;
            else method_datum.lambda = lambda;
        }
        const stackid = this.call_stack.push(method_datum, srcloc);
        const result = (lambda as Function).apply(null, params);
        this.call_stack.pop(stackid);
        return result;
    }
}

export class Call_Stack_Entry {
    method: Datum;
    location: number;

    constructor(method: Datum, location: number) {
        this.method = method;
        this.location = location;
    }
}

export enum source_location_mask {
    index  = 0xFFF00000,
    line   = 0x000FFFFF,
}

export class Call_Stack {
    stack: Call_Stack_Entry[];
    source_names: string[];

    constructor() {
        this.stack = [];
        this.source_names = ['unknown'];
    }

    make_source_location(name: string, line: number) {
        const source_index = this.source_index_of(name);
        return (source_index << 20) + line;
    }

    tail_source_position() {
        if (this.stack.length == 0)
            return new Source_Position('unknown', -1);
        const tail = this.stack[this.stack.length - 1];
        return this.make_source_position(tail.location);
    }

    make_source_position(location: number) {
        const index = (location & source_location_mask.index) >> 20;
        const line = location & source_location_mask.line;
        return new Source_Position(this.source_names[index], line);
    }

    source_index_of(name: string) {
        let index = this.source_names.indexOf(name);
        if (index != -1) return index;
        this.source_names.push(name);
        return this.source_names.length - 1;
    }

    push(method: Datum, source_location: number) {
        const entry = new Call_Stack_Entry(method, source_location);
        this.stack.push(entry);
        return this.stack.length - 1;
    }

    pop(position: number) {
        this.stack.length = position;
    }
}   
