import { JS_statement, JS_plain_expression, JS_unroll_statement_safe, JS_context, JS_expression, JS_object_expression, JS_binding, JS_var_declartion_statement, JS_array_expression, JS_call_expression, JS_assigment_expression, JS_undefined, JS_false, JS_true, JS_property_access_expression, JS_unroll_statement, JS_closure_expression, JS_body_statement, JS_return_statement, JS_dynamic_expression, JS_compile, JS_early_exit } from "./js_compile";
import { Macro_Context, Name, Bundle, Function_Nature, Class_Nature, Operator_Nature, Char, Slot_Specifier, Bundle_datum_spec, Char_datum_spec, Name_datum_spec, Host_Datum, Host_Datum_Spec, Host_Datum_Slot_Spec, Macro_Context_datum_spec, Generic_Class_Instance, Generic_Class_Instance_Maker, Internal_Array, Type_Intersection_datum_spec, Type_Union_datum_spec, Type_Union, Type_Intersection } from "./datum";
import { Module_Import,  Module, Block_Scope, Quotation, Call_Expression, Prog_Expression, Assigment_Expression, If_Expression, Known_Definition, Constant_Definition, Variable_Definition, Formal_Parameter_Definition, Formal_Parameter_Scope, Method_Head, Method_Expression, Formal_Parameters, lookup, parse_body, parse_expression, parse_name, parse_anyname, parse_denatured_name, parse_actualparameters, parse_methodhead, parse_methodhead_after_name, parse_methodhead_assigment, parse_formalparameters, parse_modified_expression, parse_operator, parse_methodmodifiers, Scope_datum_spec, Block_Scope_datum_spec, Quotation_datum_spec, Call_Expression_datum_spec, Prog_Expression_datum_spec, Assigment_Expression_datum_spec, If_Expression_datum_spec, Definition_datum_spec, Known_Definition_datum_spec, Constant_Definition_datum_spec, Variable_Definition_datum_spec, Formal_Parameter_Definition_datum_spec, Method_Expression_datum_spec, Instance_Expression_datum_spec, Formal_Parameter_Scope_datum_spec, Method_Head_datum_spec, Formal_Parameters_datum_spec, Module_datum_spec, Instance_Expression, Slot_Read_Expression_datum_spec, Slot_Write_Expression_datum_spec, Slot_Read_Expression, Slot_Write_Expression, Definition, Class_Expression, Superclass_Expression, Generic_Parameter_Scope, Generic_Parameter_Scope_datum_spec, Unresolved_Generic_Parameter_Definition, Unresolved_Generic_Parameter_Definition_datum_spec, Unresolved_Type, Class_Expression_datum_spec, datum_string, datum_print, in_type_intersection, in_type_union, lte_type_intersection, lte_type_union, Scope, Exit_Expression, Exit_Expression_datum_spec, Exit_Call_Expression, Exit_Call_Expression_datum_spec } from "./expression";
import { Newline, Keyword, Lexer, Newline_datum_spec, Keyword_datum_spec, Source_Position } from "./token";
import { macro_prefix_def, macro_prefix_defmacro, macro_infix_paren, macro_prefix_if, macro_prefix_fun, macro_prefix_paren, macro_infix_assigment, macro_infix_and, macro_infix_or, macro_prefix_template, macro_prefix_literal, macro_prefix_defclass, macro_infix_dot, macro_infix_bracket, macro_prefix_for, internal_list_append_token_sequence, macro_prefix_block, macro_prefix_require } from "./builtin_macros";
import { instantiate_generic_bundle, instantiate_internal_generic_bundle, classof, is_subtype_or_equal, is_subclass_or_equal, is_member_of } from './class';
import { Runtime } from "./js_runtime";
import { Method_Environment, Runtime_Method_Head, Runtime_Method_Datum, Method_datum_spec, Runtime_Generic_Method_Head, Runtime_Generic_Method_Datum, generic_instance_descriptor } from './method'

export class JS_recursion_conflict {
    depend_on_object: Object;

    constructor(object: Object) {
        this.depend_on_object = object;
    }
}

export class JS_property_recursion_conflict extends JS_recursion_conflict {
    lhs: JS_expression;
    property: string | number;
    
    constructor(lhs: JS_expression, property: string | number, object: Object) {
        super(object);
        this.lhs = lhs;
        this.property = property;
    }
}

export class JS_object_reconstructor {
    parent?: JS_object_reconstructor;
    context: JS_context;
    mapper: JS_object_mapper;
    
    init_statements: JS_statement[];
    reconstructors: Map<Object, JS_expression>;

    pending: Set<Object>;
    recursion_conflicts: JS_recursion_conflict[];

    required_method_ids: Set<number>;
    environment: Method_Environment = Method_Environment.Isolated;

    static enable_definition_expressions_export = false;

    constructor(context: JS_context, mapper: JS_object_mapper, parent?: JS_object_reconstructor) {
        this.parent = parent;
        this.context = context;
        this.mapper = mapper;
        
        this.init_statements = [];
        this.reconstructors = new Map();

        this.pending = new Set();
        this.recursion_conflicts = [];
        this.required_method_ids = parent ? parent.required_method_ids : new Set();

        if (parent) this.environment = parent.environment;
    }

    get root(): JS_object_reconstructor {
        if (this.parent) {
            return this.parent.root;
        }
        return this;
    }

    lookup<T>(obj0: T): JS_expression | undefined {
        const local = this.reconstructors.get(obj0);
        if (local) {
            return local;
        }
        if (this.parent) {
            return this.parent.lookup(obj0);
        }
        return undefined;
    }

    add_reconstructor(obj: Object, stmt: JS_statement, binding?: JS_binding): JS_expression {
        const existing = this.lookup(obj);
        if (existing) {
            throw new Error('object reconstruction already exists');
        }
        this.init_statements.push(stmt);
        JS_unroll_statement_safe(this.init_statements, this.context, binding ? binding : 'obj');
        let expression = this.init_statements.pop() as JS_expression;
        if (binding && expression != binding) {
            const decl = new JS_var_declartion_statement(
                'const', binding, expression);
            this.init_statements.push(decl);
            expression = binding;
        }
        this.reconstructors.set(obj, expression);
        this.remove_pending(obj);
        this.resolve_recursion_conflicts();
        return expression;
    }

    add_simple_reconstructor(obj: Object, expr: JS_expression): JS_expression {
        const existing = this.lookup(obj);
        if (existing) {
            throw new Error('object reconstruction already exists');
        }
        this.reconstructors.set(obj, expr);
        this.remove_pending(obj);
        this.resolve_recursion_conflicts();
        return expr;
    }

    add_pending(obj: Object) {
        this.pending.add(obj);
    }

    is_pending(obj: Object): boolean {
        if (this.pending.has(obj)) {
            return true;
        }
        if (this.parent) {
            return this.parent.is_pending(obj);
        }
        return false;
    }

    remove_pending(obj: Object) {
        if (this.pending.has(obj)) {
            this.pending.delete(obj);
            return;
        }
        if (this.parent) {
            this.parent.remove_pending(obj);
        }
    }

    reconstructor_of<T>(obj: T): JS_expression {
        switch (typeof obj) {
            case 'undefined':
                return JS_undefined;
            case 'boolean':
                return obj ? JS_true : JS_false;
            case 'number':
                return new JS_plain_expression(`${obj}`, false);
        }
        if (obj instanceof Char) {
            const args = [this.reconstructor_of(obj.code) as JS_expression];
            const expression = new JS_call_expression(
                new JS_plain_expression(`$poly.char`, false),
                args, false);
            return expression;
        }
        if (obj instanceof Name && !obj.context) {
            const args = [this.reconstructor_of(obj.spelling) as JS_expression];
            const expression = new JS_call_expression(
                new JS_plain_expression(`$poly.name`, false),
                args, false);
            return expression;
        }
        if (obj instanceof Source_Position) {
            const args = [
                this.reconstructor_of(obj.name) as JS_expression,
                this.reconstructor_of(obj.line)];
            const expression = new JS_call_expression(
                new JS_plain_expression(`$poly.source`, false),
                args, false);
            return expression;
        }
        const existing = this.lookup(obj);
        if (existing) {
            return existing;
        }
        if (typeof obj == 'string') {
            return new JS_plain_expression(`${JSON.stringify(obj)}`, false);
        }
        if (typeof obj == 'function') {
            this.add_pending(obj);
            const key = this.mapper.prototype_key(obj);
            if (key) {
                const function_expression = this.mapper.object_expression(key);
                return function_expression;
            }
            const function_expression = new JS_plain_expression(obj.toString(), false);
            return this.add_reconstructor(obj, function_expression);
        }
        if (typeof obj != 'object') {
            throw new Error(`object '${typeof obj}' cannot be reconstructed`);
        }
        const mapper_key = this.mapper.object_key(obj);
        if (mapper_key) {
            return this.mapper.object_expression(mapper_key);
        }
        if (this.is_pending(obj)) {
            throw new JS_recursion_conflict(obj);
        } else {
            this.add_pending(obj);
        }
        let obj_binding: JS_binding | undefined;
        if (Array.isArray(obj)) {
            obj_binding = this.context.temp_binding('arr');
            const elements = obj.map((elem, i) => 
                this.reconstruction_of_object_property(obj_binding as JS_binding, obj, i));
            const expression = new JS_array_expression(elements);
            return this.add_reconstructor(obj, expression, obj_binding);
        }
        if (obj instanceof Host_Datum && typeof obj.$datumspec.class == 'string') {
            const module = this.context.module as Module;
            const def = lookup(module, Name.make(obj.$datumspec.class));
            if (!def) {
                throw new Error(`Host_Datum bundle "${obj.$datumspec.class}" not visible in module ${module.name.spelling}`);
            }
            obj.$datumspec.class = (def as Known_Definition).value as Bundle;
        }
        if (obj instanceof Set) {
            obj_binding = this.context.temp_binding('set');
            const elements = Array.from(obj.values()).map((elem, i) => {
                this.init_statements.push(this.reconstructor_of(elem));
                JS_unroll_statement_safe(
                    this.init_statements, this.context, `elem_${i}`);
                return this.init_statements.pop() as JS_expression;
            });
            const expression = new JS_call_expression(
                new JS_plain_expression('new Set', false),
                [new JS_array_expression(elements)]);
            return this.add_reconstructor(obj, expression, obj_binding);
        }
        if (obj instanceof Map) {
            obj_binding = this.context.temp_binding('map');
            const elements = Array.from(obj.entries()).map((elem, i) => {
                this.init_statements.push(this.reconstructor_of(elem));
                JS_unroll_statement_safe(
                    this.init_statements, this.context, `elem_${i}`);
                return this.init_statements.pop() as JS_expression;
            });
            const expression = new JS_call_expression(
                new JS_plain_expression('new Map', false),
                [new JS_array_expression(elements)]);
            return this.add_reconstructor(obj, expression, obj_binding);
        }
        if (obj instanceof Runtime_Method_Datum) {
            const head = Runtime.instance.method_heads[obj.id];
            const spelling = head.name ? head.name.spelling : 'fn'; 
            const prefix = `${spelling}_${obj.id}`;
            obj_binding = new JS_binding(Name.make(prefix), JS_context.symbols.mangle(prefix, obj));
            const lambda = Array.isArray(obj.lambda) ? obj.lambda[this.environment] : obj.lambda;
            if (lambda === null) {
                this.pending.delete(obj);
                return obj_binding;
            }
        }
        const class_key = this.mapper.prototype_key(obj);
        if (!class_key) {
            const name = (obj as any)?.constructor?.name || 'unknown';
            throw new Error(`object class '${name}' is not known by mapper`);
        }
        let temp_binding_name = class_key.toLowerCase() || 'obj';
        if (obj instanceof Host_Datum && obj.$datumspec.class instanceof Bundle)
            temp_binding_name = obj.$datumspec.class.name?.spelling || temp_binding_name;
        if (obj instanceof Bundle || obj instanceof Definition)
            temp_binding_name = (obj as any).name?.spelling || temp_binding_name;
        obj_binding = obj_binding ? obj_binding : this.context.temp_binding(temp_binding_name);
        const properties: {[key: string]: JS_expression} = {}; 
        for (let key in obj) {
            if (!(obj as any).hasOwnProperty(key)) {
                continue;
            }
            properties[key] = this.reconstruction_of_object_property(
                obj_binding, obj, key);
        }
        const expression = this.mapper.prototype_instance_expression(
            this.reconstructor_of(this.mapper.objects[class_key]), 
            new JS_object_expression(properties));
        return this.add_reconstructor(obj, expression, obj_binding);
    }

    reconstruction_of_object_property(binding: JS_binding, obj: any, key: string | number): JS_expression {
        if (obj instanceof Runtime_Method_Datum && key == 'lambda') {
            const compile = () => {
                let lambda = Array.isArray(obj.lambda) ? 
                    obj.lambda[this.environment] : obj.lambda;
                if (!lambda && Array.isArray(obj.lambda) && this.environment == Method_Environment.Integrated)
                    lambda = obj.lambda[Method_Environment.Isolated];
                if (lambda instanceof JS_expression)
                    return lambda.compile();
                if (lambda instanceof JS_statement)
                    return lambda.compile_statement();
                return this.reconstructor_of(lambda).compile();
            };
            this.required_method_ids.add(obj.id);
            return new JS_dynamic_expression(compile);
        }
        if (!JS_object_reconstructor.enable_definition_expressions_export &&
            obj instanceof Definition && obj.have_expression() &&
            key == 'expression') 
                return JS_undefined;
        let construction: JS_statement = JS_undefined;
        try {
            construction = this.reconstructor_of(obj[key]);
        } catch(e) {
            if (!(e instanceof JS_recursion_conflict)) {
                throw e;
            }
            const conflict = new JS_property_recursion_conflict(
                binding, key, e.depend_on_object);
            this.recursion_conflicts.push(conflict);
        }
        this.init_statements.push(construction);
        JS_unroll_statement_safe(
            this.init_statements, this.context, 
            typeof key == 'number' ? `elem_${key}` : key);
        return this.init_statements.pop() as JS_expression;
    }

    resolve_recursion_conflicts() {
        const resolved_conflicts: Set<JS_recursion_conflict> = new Set();
        for (let conflict of this.recursion_conflicts) {
            const resolved = this.lookup(conflict.depend_on_object);
            if (!resolved) {
                continue;
            }
            if (conflict instanceof JS_property_recursion_conflict) {
                const assigment = new JS_assigment_expression(
                    new JS_property_access_expression(conflict.lhs, conflict.property), resolved);
                    this.init_statements.push(assigment);
                }
                resolved_conflicts.add(conflict);
            }
        if (resolved_conflicts.size > 0) {
            this.recursion_conflicts = this.recursion_conflicts.filter(
                conflict => !resolved_conflicts.has(conflict));
        }
    }

    reconstruction_by_property_access_with_queue(queue: _JS_property_reconstruction_queue) {
        const task = queue.pop() as _JS_property_reconstruction_task;
        
        const key = task.key;
        const object = task.object;
        const parent = task.parent;

        if (typeof object != 'object') {
            return this.reconstructor_of(object);
        }
        const parent_reconstruction = parent ? this.lookup(parent) : undefined;
        if (!parent_reconstruction && parent) {
            throw new Error(`parent object is not reconstructed yet`);
        }
        const existing = this.lookup(object);
        if (existing) {
            return existing;
        }
        let expression: JS_expression = JS_undefined;
        if (key instanceof JS_expression) {
            expression = key;
        } else if (parent && parent_reconstruction) {
            if (parent instanceof Map) {
                const mapget = new JS_property_access_expression(parent_reconstruction, 'get');
                expression = new JS_call_expression(mapget, [this.reconstructor_of(key)], false);
            } else {
                expression = new JS_property_access_expression(parent_reconstruction, key);
            }
        }
        if (object instanceof Module && !(key instanceof JS_expression)) {
            expression = new JS_plain_expression(`$poly.module(${JSON.stringify(object.name.spelling)})`, false);
        }
        const construction = this.add_simple_reconstructor(object, expression);
        if (object instanceof JS_statement) {
            return construction;
        }
        if (!JS_object_reconstructor.enable_definition_expressions_export &&
            parent instanceof Definition &&
            parent.have_expression() && key == 'expression')
                return JS_undefined;
        if (object instanceof Map) {
            for (let entry of object) {
                queue.add(new _JS_property_reconstruction_task(entry[1], entry[0], object));
            }
            return construction;
        }
        for (let key in object) {
            if (!object.hasOwnProperty(key)) {
                continue;
            }
            queue.add(new _JS_property_reconstruction_task(object[key], key, object));
        }
        return construction;
    }

    reconstruction_by_property_access(object: any, key: string | number | JS_expression, parent?: any): JS_statement {
        const queue = new _JS_property_reconstruction_queue();
        queue.add(new _JS_property_reconstruction_task(object, key, parent));
        const root = this.reconstruction_by_property_access_with_queue(queue);
        while(queue.length > 0) {
            this.reconstruction_by_property_access_with_queue(queue);
        }
        return root;
    }

    reconstruction_of_instance_bundle(bundle: Bundle) {
        if (this.reconstructors.has(bundle))
            return this.reconstructors.get(bundle) as JS_expression;
        const index = Runtime.instance.instance_bundles.indexOf(bundle);
        const compile = () => {
            if (this.reconstructors.has(bundle) && !(this.reconstructors.get(bundle) instanceof JS_dynamic_expression))
                return (this.reconstructors.get(bundle) as JS_expression).compile();
            const bundle_access = new JS_property_access_expression(
                new JS_plain_expression('$poly.instance_bundles', false), index);
            return bundle_access.compile();
        }
        return new JS_dynamic_expression(compile);
    }
}

class _JS_property_reconstruction_queue {
    _buffer: (_JS_property_reconstruction_task | undefined)[];
    _first: number;
    _last: number; 

    constructor() {
        this._buffer = new Array(3072);
        this._first = 0;
        this._last = 0;
    }

    add(task: _JS_property_reconstruction_task) {
        if (this._last + 1 > this._buffer.length) {
            this._buffer.length = this._last + 256;
        }
        this._buffer[this._last] = task;
        this._last++;
    }

    pop(): _JS_property_reconstruction_task | undefined {
        const task = this._buffer[this._first];
        this._first++;
        return task;
    }

    get length() {
        return this._last - this._first;
    }
}

class _JS_property_reconstruction_task {
    object: any;
    key: string | number | JS_expression;
    parent: any;

    constructor(object: any, key: string | number | JS_expression, parent: any) {
        this.object = object;
        this.key = key;
        this.parent = parent;
    }
}

export class JS_compiled_prototype {
    bundle: Bundle;
    statement: JS_statement;
    prototype: Function;
    key: string;
    
    constructor(bundle: Bundle, statement: JS_statement, key: string) {
        this.bundle = bundle;
        this.statement = statement;
        this.key = key;
        const $poly = Runtime.instance;
        const compile = ($poly: Runtime) => {
            const context = new JS_context($poly.modules as Module);
            const body = [statement];
            JS_unroll_statement(body, context);
            body.push(new JS_return_statement(body.pop() as JS_expression));
            const closure_expression = new JS_closure_expression(
                [], new JS_body_statement(body));
            const compiled = closure_expression.compile_statement();
            return eval(compiled)();
        };
        this.prototype = compile($poly);
    }
}

export class JS_object_mapper {
    objects: {[key: string]: Object};
    compiled_prototypes: JS_compiled_prototype[];

    constructor(objects: {[key: string]: Object}) {
        this.objects = objects;
        this.compiled_prototypes = [];
    }

    compile_prototype(bundle: Bundle, statement: JS_statement, key: string) {
        const compiled = new JS_compiled_prototype(bundle, statement, key);
        this.compiled_prototypes.push(compiled);
        this.objects[compiled.key] = compiled.prototype;
        return compiled;
    }

    compiled_prototype_key(bundle: Bundle): JS_compiled_prototype | undefined {
        for (let entry of this.compiled_prototypes) {
            if (entry.bundle == bundle) {
                return entry;
            }
        }
        return undefined;
    }

    prototype_key(obj: Object | Function): string | undefined {
        if (typeof obj == 'function') {
            for (let key in this.objects) {
                if (obj === this.objects[key]) {
                    return key;
                }
            }
            return undefined;
        }
        const proto = Object.getPrototypeOf(obj);
        for (let key in this.objects) {
            if (proto === (this.objects[key] as any).prototype) {
                return key;
            }
        }
        return undefined;
    }

    object_key(obj: Object): string | undefined {
        for (let key in this.objects) {
            if (this.objects[key] == obj) {
                return key;
            }
        }
        return undefined;
    }

    object_expression(key: string): JS_expression {
        return new JS_plain_expression(`$poly.objmap.${key}`, false);
    }

    prototype_instance_expression(proto: JS_expression, expr: JS_expression): JS_expression {
        const classbinder = new JS_call_expression(
            new JS_plain_expression('$poly.newobj', false),
            [proto, expr]);
        return classbinder;
    }
}

export function JS_builtin_objects(): {[key: string]: any} {
    const objects: {[key: string]: any} = {
        Object,
        Host_Datum,
        Host_Datum_Spec,
        Host_Datum_Slot_Spec,

        Char,

        Bundle,
            Function_Nature,
            Class_Nature,
                Class_Expression,
                Superclass_Expression,
            Operator_Nature,
        
        Unresolved_Type,
        Generic_Parameter_Scope,
        Unresolved_Generic_Parameter_Definition,
        Generic_Class_Instance,
        Generic_Class_Instance_Maker,

        Module,
            Module_Import,
        Macro_Context,
        Block_Scope,

        Quotation,
        Call_Expression,
        Prog_Expression,
        Assigment_Expression,
        If_Expression,

        Exit_Expression,
        Exit_Expression_datum_spec,
        Exit_Call_Expression,
        Exit_Call_Expression_datum_spec,

        Known_Definition,
        Constant_Definition,
        Variable_Definition,
        Formal_Parameter_Definition,
        Formal_Parameter_Scope,
        Formal_Parameters,

        Method_Head,
        Method_Expression,
        Runtime_Method_Head,
        Runtime_Method_Datum,
        Runtime_Generic_Method_Datum,
        Runtime_Generic_Method_Head,
        Instance_Expression,
        Slot_Read_Expression,
        Slot_Write_Expression,

        Type_Union,
        Type_Intersection,
        
        Slot_Specifier,

        Name,
        Newline,
        Keyword,

        Lexer,
        Source_Position,

        Internal_Array,
        internal_list_append_token_sequence,

        macro_prefix_def,
        macro_prefix_defmacro,
        macro_prefix_if,
        macro_prefix_fun,
        macro_prefix_paren,
        macro_infix_paren,
        macro_infix_assigment,
        macro_infix_and,
        macro_infix_or,
        macro_infix_dot,
        macro_infix_bracket,
        macro_prefix_template,
        macro_prefix_literal,
        macro_prefix_defclass,
        macro_prefix_for,
        macro_prefix_block,
        macro_prefix_require,
        
        parse_expression,
        parse_name,
        parse_anyname,
        parse_denatured_name,
        parse_actualparameters,
        parse_methodhead,
        parse_methodhead_after_name,
        parse_methodhead_assigment,
        parse_formalparameters,
        parse_modified_expression,
        parse_operator,
        parse_methodmodifiers,
        parse_body,

        instantiate_generic_bundle,
        instantiate_internal_generic_bundle,
        classof,
        is_subtype_or_equal,
        is_subclass_or_equal,
        is_member_of,

        datum_string,
        datum_print,

        in_type_intersection,
        in_type_union,
        lte_type_intersection,
        lte_type_union,

        Bundle_datum_spec,
        Char_datum_spec,

        Name_datum_spec,
        Newline_datum_spec,
        Keyword_datum_spec,
        
        Scope_datum_spec,
        Block_Scope_datum_spec,
        Module_datum_spec,
        
        Quotation_datum_spec,
        Call_Expression_datum_spec,
        Prog_Expression_datum_spec,
        Assigment_Expression_datum_spec,
        If_Expression_datum_spec,
        Slot_Read_Expression_datum_spec,
        Slot_Write_Expression_datum_spec,

        Definition_datum_spec,
        Known_Definition_datum_spec,
        Constant_Definition_datum_spec,
        Variable_Definition_datum_spec,

        Macro_Context_datum_spec,
        Method_Expression_datum_spec,
        Method_Head_datum_spec,
        Method_datum_spec,
        
        Instance_Expression_datum_spec,

        Formal_Parameters_datum_spec,
        Formal_Parameter_Scope_datum_spec,
        Formal_Parameter_Definition_datum_spec,
        Unresolved_Generic_Parameter_Definition_datum_spec,

        Generic_Parameter_Scope_datum_spec,
        generic_instance_descriptor,
        Class_Expression_datum_spec,

        Type_Intersection_datum_spec,
        Type_Union_datum_spec,

        JS_early_exit,
    }
    return objects;
}

export function isolated_reconstructor(scope?: Scope): JS_object_reconstructor {
    const $poly = Runtime.instance;

    const context = JS_context.from_scope(scope ? scope : $poly.modules as Scope);
    const reconstructor = new JS_object_reconstructor(context, $poly.mapper);
    
    const module_expr = new JS_plain_expression("$poly.modules", false);
    reconstructor.reconstruction_by_property_access($poly.modules, module_expr);
    
    const bundle_expr = new JS_plain_expression("$poly.instance_bundles", false);
    reconstructor.reconstruction_by_property_access($poly.instance_bundles, bundle_expr);
    
    for (let gscope = scope; gscope; gscope = gscope.parent as Scope) 
        if (gscope instanceof Generic_Parameter_Scope) for (let defn of gscope.definitions.values())
            reconstructor.init_statements.push(JS_compile(defn, context, reconstructor));
            
    return reconstructor;
}