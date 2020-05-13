import { Source_Position } from "./token";
import { Macro_Context, Bundle, Datum, Slot_Specifier, Class_Nature, Class_Modifier, Name, Generic_Class_Instance, Generic_Class_Instance_Maker, Function_Nature, Internal_Array, Host_Datum, Type } from "./datum";
import { Module, Quotation, Known_Definition, evaluate_type, Variable_Definition, Method_Head, Block_Scope, Prog_Expression, Scope, Method_Expression, Expression, Call_Expression, Formal_Parameters, Formal_Parameter_Definition, Formal_Parameter_Scope, expand_definition, lookup_known_definition, add_definition, Assigment_Expression, Instance_Expression, Slot_Read_Expression, copy_expression, Superclass_Expression, Class_Expression, Generic_Parameter_Scope, generic_context_of, Unresolved_Type, copy_formalparameters, Definition, lookup, Method_Modifiers, Slot_Write_Expression } from "./expression";
import { Runtime } from "./js_runtime";
import { add_method_expression, Runtime_Method_Head, Runtime_Method_Datum, compare_methods } from "./method";
import { eval_expression } from "./eval";

export function classof(datum: Datum): Bundle {
    const $poly = Runtime.instance;
    if (!$poly.modules) throw new Error(`runtime not initialized yet!`);
    const _class = datum === undefined ? 
        false.datumclass() : datum.datumclass();
    if (typeof _class != 'string') return _class;
    if (datum instanceof Host_Datum) {
        datum.$datumspec.class = $poly.lookup(_class);
        return datum.$datumspec.class as Bundle;   
    }
    return $poly.lookup(_class);
}

export function evaluate_superclass_bundle(expr: Superclass_Expression, scope: Scope): Bundle {
    const bundle = lookup_known_definition(scope, expr.name) as Bundle | undefined;
    if (!(bundle instanceof Bundle)) 
        throw new Error(`lhs of superclass expression must be bundle!`);
    if (!expr.generic_parameters)
        return bundle;
    if (generic_context_of(expr, scope).size > 0)
        return bundle;
    for (let p of expr.generic_parameters) if (generic_context_of(p, scope).size > 0)
        return bundle;
    const parameters = expr.generic_parameters.map(p => eval_expression(p, scope));
    const generic_instance = instantiate_generic_bundle(bundle, parameters) as Bundle;
    if (!(generic_instance instanceof Bundle)) 
        throw new Error(`lhs of superclass expression must be bundle!`);
    return generic_instance;
}

export function generate_class_constructor_method(class_bundle: Bundle, class_expression: Class_Expression, scope: Scope) {
    const class_nature = class_bundle.class as Class_Nature;
    const $poly = Runtime.instance;

    const direct_superclasses: Bundle[] = class_expression.superclasses.map(e => 
        evaluate_superclass_bundle(e, class_expression.formal_parameters.scope));

    const inherited_slots: Slot_Specifier[] = class_nature.slots.filter(s => s.origin != class_bundle);
    const accept_constructor_parameters_from: Map<Bundle, Bundle> = new Map()
    for (let superclass of class_nature.superclasses) {
        const nature = superclass.class as Class_Nature;
        const superclass_expression = $poly.class_expressions[nature.id];
        if (!superclass_expression)
            continue;
        
        const superclasses = superclass_expression.superclasses.map(e => 
            evaluate_superclass_bundle(e, superclass_expression.formal_parameters.scope));
        for (let bundle of superclasses)
            accept_constructor_parameters_from.set(bundle, superclass);
    }
    for (let direct_superclass of direct_superclasses)
        accept_constructor_parameters_from.set(direct_superclass, class_bundle);
    const body_head = new Block_Scope(class_expression.formal_parameters.scope, [], 'tail');
    let body_tail = body_head;
    
    const temp_context = new Macro_Context(body_tail);
    const inherited_slots_temp: Map<Name, Name> = new Map();
    for (let slot of inherited_slots) {
        const name = Name.make(slot.name, temp_context);
        const defn = new Variable_Definition(class_expression.position, 
            name, Runtime.instance.lookup('everything') as Bundle, 
            new Quotation(false))
        const expanded = expand_definition(body_tail, name, defn) as Prog_Expression;
        body_tail.expressions.push(...expanded.expressions);
        body_tail = body_tail.expressions[body_tail.expressions.length - 1] as Block_Scope;
        inherited_slots_temp.set(slot.name, name);
    }
    
    const superclass_constructors: Map<Bundle, Method_Expression> = new Map();
    const find_superclass_expression = (subclass: Bundle, superclass: Bundle, scope: Scope) => {
        if (accept_constructor_parameters_from.get(superclass) != subclass)
            return undefined;
        const initial_expression = $poly.class_expressions[subclass.class?.id as number].superclasses.find(
            call_expression => call_expression.name == superclass.name);
        if (!initial_expression)
            return undefined;
        const constructor_stub = superclass_constructors.get(superclass) as Method_Expression;
        if (!constructor_stub)
            return undefined;
        const copied = new Map();
        copied.set(constructor_stub.formal_parameters.scope.root(), scope)
        const constructor_final = copy_expression(constructor_stub, copied) as Method_Expression;  
        const expression = new Call_Expression(
            initial_expression.position,
            constructor_final,
            initial_expression.constructor_parameters,
            initial_expression.spread);
        return expression;
    }

    for (let superclass of class_nature.superclasses) {
        const class_constructor = $poly.class_expressions[superclass.class?.id as number];
        if (!class_constructor) 
            continue;
        const head = new Method_Head(
            superclass.name as Name, new Set(['sealed']), 
            class_constructor.formal_parameters,
            lookup_known_definition(scope, 'everything') as Bundle);
        const body = new Block_Scope(head.formal_parameters.scope, [], 'head');
        for (let assigment of class_constructor.slot_assigments) {
            const new_assigment = new Assigment_Expression(assigment.position,
                inherited_slots_temp.get(assigment.lhs) as Name, assigment.rhs);
            body.expressions.push(new_assigment);
        }
        for (let supersuperclass of class_nature.superclasses) {
            if (supersuperclass == superclass)
                continue;
            const expression = find_superclass_expression(superclass, supersuperclass, body);
            if (expression) body.expressions.push(expression);
        }
        const method_expression = new Method_Expression(
            class_expression.position,
            Name.make(superclass.name?.spelling + '@super'),
            undefined,
            class_constructor.formal_parameters,
            lookup_known_definition(scope, 'everything') as Bundle,
            new Set(['sealed']),
            body);
        superclass_constructors.set(superclass, method_expression);

        const expression = find_superclass_expression(class_bundle, superclass, body_tail);
        if (expression) body_tail.expressions.push(expression);
    }
    const instance = new Instance_Expression(
        class_expression.position,
        class_bundle,
        class_nature.slots.map(slot => (slot.origin == class_bundle ?
            class_expression.slot_assigments.find(assigment => assigment.lhs == slot.name)?.rhs :
            inherited_slots_temp.get(slot.name)) as Expression),
    );
    body_tail.expressions.push(instance);
    const constructor = new Method_Expression(
        class_expression.position,
        class_expression.constructor_name,
        undefined,
        class_expression.formal_parameters,
        class_bundle,
        new Set(),
        body_head);

    return constructor;
}

export function class_expression_outer_scope(class_expression: Class_Expression): Scope {
    let outer_scope: Scope = class_expression.formal_parameters.scope;
    while (outer_scope.parent) {
        if (outer_scope instanceof Module)
            break;
        if (outer_scope instanceof Block_Scope)
            break;
        outer_scope = outer_scope.parent as Scope;
    }
    outer_scope = outer_scope.parent ? outer_scope.parent : outer_scope;
    return outer_scope;
}


export function instantiate_generic_class_constructor(class_bundle: Bundle, generic_actuals: Datum[], bundle?: Bundle) {
    const $poly = Runtime.instance;

    if (class_bundle.class?.abstract)
        return bundle;
        
    const instance = instantiate_generic_class(class_bundle, generic_actuals);
    if (instance.class?.superclasses === undefined)
        return bundle;
    const instance_expression = $poly.class_expressions[(instance.class as Class_Nature).id];

    const existing_constructor = $poly.generic_class_instance_constructors.get(instance);
    if (existing_constructor) return existing_constructor;

    const constructor_bundle = bundle ?
        bundle : new Bundle(instance.class?.constructor_name); 
    $poly.generic_class_instance_constructors.set(instance, constructor_bundle);

    const outer_scope = class_expression_outer_scope(instance_expression);
    const method = generate_class_constructor_method(instance, instance_expression, outer_scope);
    add_method_expression(constructor_bundle, method);   

    return constructor_bundle;
}

export function instantiate_generic_class(class_bundle: Bundle, generic_actuals: Datum[]) {
    const class_nature = class_bundle.class as Class_Nature;
    const existing_instance = lookup_generic_instance(class_bundle, generic_actuals);
    if (existing_instance)
        return existing_instance;

    const class_expression = Runtime.instance.class_expressions[class_nature.id];
    if (!class_expression)
        throw new Error(`runtime instantation of generic classes seems to be disabled...`)
    const generic_parameters = class_expression.generic_parameters as Formal_Parameters;
    
    let scope: Scope | undefined = class_expression.formal_parameters.scope;
    while (scope?.parent && !(scope instanceof Generic_Parameter_Scope))
        scope = scope.parent;

    const generic_scope = new Generic_Parameter_Scope(scope?.parent ? scope.parent : scope);
    let generic_actuals_index = 0;
    const defknown = (p: Formal_Parameter_Definition) => {
        const param = generic_actuals[generic_actuals_index];
        generic_actuals_index++;
        const known = new Known_Definition(p.position, p.name, param);
        add_definition(generic_scope, p.name, known); 
    }
    for (let p of generic_parameters.required) defknown(p);
    for (let p of generic_parameters.optional) defknown(p);

    const copied = new Map();
    copied.set(scope, generic_scope);

    const formal = copy_formalparameters(class_expression.formal_parameters, copied);
    const new_class_expression = new Class_Expression(
        class_expression.position,
        Runtime.instance.class_index++,
        class_expression.constructor_name,
        formal,
        undefined,
        class_expression.slot_assigments.map(
            e => copy_expression(e, copied) as Assigment_Expression),
        class_expression.superclasses,
        class_expression.length_expression !== undefined ? 
            copy_expression(class_expression.length_expression, copied) : undefined);
    Runtime.instance.class_expressions[new_class_expression.id] = new_class_expression;
    
    const resolve_parameter = (p: Formal_Parameter_Definition) => {
        if (p.type instanceof Unresolved_Type)
            p.type = evaluate_type(p.type.expression, formal.scope);
    }
    for (let p of formal.required) resolve_parameter(p);
    for (let p of formal.optional) resolve_parameter(p);
    for (let p of formal.named) resolve_parameter(p);
    if (formal.rest) resolve_parameter(formal.rest); 

    const new_class_bundle = new Bundle(class_bundle.name);
    const new_class_modifiers = new Set<Class_Modifier>();
    if (class_nature.abstract) 
        new_class_modifiers.add('abstract');
    if (class_nature.autothrow)
        new_class_modifiers.add('autothrow');
    if (class_nature.noreturn)
        new_class_modifiers.add('noreturn');
    if (class_nature.noreturn)
        new_class_modifiers.add('sealed');
    const new_class_nature = new Class_Nature(
        new_class_expression.id,
        class_nature.constructor_name,
        undefined as any,
        undefined as any,
        new_class_modifiers);
    new_class_nature.generic_instance = 
        new Generic_Class_Instance(class_bundle, generic_actuals);
    new_class_bundle.class = new_class_nature;
    add_generic_instance(class_bundle, new_class_bundle);

    const superclasses = evaluate_class_superclasses(new_class_expression);
    superclasses.push(class_bundle);
    new_class_nature.superclasses = superclasses;
    new_class_nature.slots = combine_slots(superclasses),
    rebind_generic_slots(new_class_bundle, new_class_expression);

    const outer_scope: Scope = class_expression_outer_scope(new_class_expression);

    const bdef = new _Batch_Definer(class_expression.position);
    define_class_slot_operations(bdef, new_class_bundle, new_class_expression, outer_scope);

    return new_class_bundle;
}

export function instantiate_generic_bundle(bundle: Bundle, generic_actuals: Datum[] | Internal_Array) {
    if (generic_actuals instanceof Internal_Array) generic_actuals = generic_actuals.array;
    const $poly = Runtime.instance;
    const maker = $poly.generic_class_instance_makers.get(bundle) as Generic_Class_Instance_Maker;
    let instance_bundle: Bundle | undefined = undefined;
    if (maker.class_maker) instance_bundle = 
        instantiate_generic_class(maker.class_maker, generic_actuals);
    if (maker.constructor_maker) instance_bundle = 
        instantiate_generic_class_constructor(
            maker.constructor_maker, generic_actuals, instance_bundle);
    return instance_bundle;
}

export function instantiate_internal_generic_bundle(generic: Bundle, context: Datum[], superclasses: Bundle[], callback?: (instance: Bundle) => void) {
    const $poly = Runtime.instance;
    const existing = lookup_generic_instance(generic, context);
    if (existing) return existing;

    const class_nature = generic.class as Class_Nature;

    const instance_superclasses: Set<Bundle> = new Set();
    for (let bundle of superclasses) {
        const instance = bundle.class?.generic ? 
            instantiate_generic_bundle(bundle, context) as Bundle : bundle;
        instance_superclasses.add(instance);
        for (let super_bundle of instance.class?.superclasses as Bundle[])
            instance_superclasses.add(super_bundle);
    }

    for (let bundle of superclasses)
        instantiate_generic_bundle(bundle, context);

    const modifers = new Set<Class_Modifier>();
    if (class_nature.intrinsic) modifers.add('intrinsic');
    if (class_nature.sealed) modifers.add('sealed');
    if (class_nature.abstract) modifers.add('abstract');

    const baked_instance_superclasses = Array.from(instance_superclasses);
    baked_instance_superclasses.sort((a, b) => is_subclass_or_equal(a, b) ? -1 : 0);

    const instance = new Bundle(generic.name);
    const class_id = $poly.class_index++;
    instance.class = new Class_Nature(
        class_id,
        generic.name,
        baked_instance_superclasses, 
        class_nature.slots.slice(),
        modifers);
    add_generic_instance(generic, instance);

    if (callback) callback(instance);

    return instance;
}

export function rebind_generic_slots(class_bundle: Bundle, class_expression: Class_Expression) {
    const class_nature = class_bundle.class as Class_Nature;
    const slots = class_nature.slots.slice();
    for (var i = 0; i < slots.length; i++) {
        const slot = slots[i];
        if (slot.origin != class_nature.generic_instance?.generic_class) continue;
        const type = slot.type instanceof Unresolved_Type ?
            evaluate_type(slot.type.expression, class_expression.formal_parameters.scope) :
            slot.type;
        const new_slot = new Slot_Specifier(
            slot.name,
            type,
            class_bundle,
            slot.reader_name,
            slot.writer_name,
            slot.multislot);
        slots[i] = new_slot;
    }
    class_nature.slots = slots;
}

export function generate_class_generic_instance_maker_method(bundle: Bundle, position: Source_Position, generic_parameters: Formal_Parameters, scope: Scope) {
    const $poly = Runtime.instance;

    const actual_generic_parameters: Expression[] = [];
    for (let p of generic_parameters.required)
        actual_generic_parameters.push(p.name);
    for (let p of generic_parameters.optional)
        actual_generic_parameters.push(p.name);
    for (let p of generic_parameters.named)
        actual_generic_parameters.push(p.name);
    if (generic_parameters.rest) 
        actual_generic_parameters.push(generic_parameters.rest.name);

    const body = new Call_Expression(
        position,
        Name.make('instantiate_generic_bundle', $poly.modules),
        [new Quotation(bundle), ...actual_generic_parameters], 
        false);
        
    const method_formal = copy_formalparameters(generic_parameters); {
        const bundle_context = new Macro_Context(scope);
        const bundle_name = Name.make(bundle.name || 'bundle', bundle_context);
        const bundle_parameter = new Formal_Parameter_Definition(
            position, bundle_name, new Set([bundle]));

        add_definition(method_formal.scope, bundle_name, bundle_parameter);
        method_formal.required.unshift(bundle_parameter);
    }

    const method = new Method_Expression(
        position,
        Name.make('['),
        undefined,
        method_formal,
        lookup_known_definition(scope, 'bundle') as Datum,
        new Set([]),
        body);
    return method;
}

export function generate_class_slot_reader(class_bundle: Bundle, class_expression: Class_Expression, slot_name: Name, scope: Scope) {
    const class_nature = class_bundle.class as Class_Nature;

    const slot = class_nature.slots.
        find(s => s.name == slot_name) as Slot_Specifier;
    const assigment = class_expression.slot_assigments.
        find(a => a.lhs == slot_name);
    const position = assigment?.position || class_expression.position;

    const reader_formal = new Formal_Parameters(scope);
    const arg0 = new Formal_Parameter_Definition(
        position,
        Name.make('datum'),
        class_bundle);
    const arg1 = new Formal_Parameter_Definition(
        position,
        Name.make('slot_name'),
        new Set([slot.name]));
    reader_formal.required.push(arg0, arg1);

    reader_formal.scope = new Formal_Parameter_Scope(reader_formal.scope);
    add_definition(reader_formal.scope, arg0.name, arg0);

    reader_formal.scope = new Formal_Parameter_Scope(reader_formal.scope);
    add_definition(reader_formal.scope, arg1.name, arg1);
        
    const reader_method_body = new Slot_Read_Expression(
        position,
        class_bundle,
        Name.make('datum'),
        slot.name);
    const reader_method = new Method_Expression(
        position,
        slot.name,
        undefined,
        reader_formal,
        slot.type,
        new Set(['sealed']),
        reader_method_body);
    return reader_method;
}

export function generate_class_slot_writer(class_bundle: Bundle, class_expression: Class_Expression, slot_name: Name, scope: Scope) {
    const class_nature = class_bundle.class as Class_Nature;

    const slot = class_nature.slots.
        find(s => s.name == slot_name) as Slot_Specifier;
    const assigment = class_expression.slot_assigments.
        find(a => a.lhs == slot_name);
    const position = assigment?.position || class_expression.position;

    const reader_formal = new Formal_Parameters(scope);
    const arg0 = new Formal_Parameter_Definition(
        position,
        Name.make('datum'),
        class_bundle);
    const arg1 = new Formal_Parameter_Definition(
        position,
        Name.make('slot_name'),
        new Set([slot.name]));
    const arg2 = new Formal_Parameter_Definition(
        position,
        Name.make('new_value'),
        slot.type);
    reader_formal.required.push(arg0, arg1, arg2);
        
    const parameters = [arg0, arg1, arg2];
    for (let p of parameters) {
        reader_formal.scope = new Formal_Parameter_Scope(reader_formal.scope);
        add_definition(reader_formal.scope, p.name, p);
    }
        
    const writer_method_body = new Slot_Write_Expression(
        position,
        class_bundle,
        Name.make('datum'),
        slot.name,
        Name.make('new_value'));
    const writer_method = new Method_Expression(
        position,
        slot.name,
        undefined,
        reader_formal,
        slot.type,
        new Set(['sealed']),
        writer_method_body);
    return writer_method;
}

export function define_class_slot_operations(bdef: _Batch_Definer, class_bundle: Bundle, class_expression: Class_Expression, scope: Scope) {
    const class_nature = class_bundle.class as Class_Nature;
    for (let slot of class_nature.slots) {
        if (slot.type instanceof Unresolved_Type)
            continue;
        if (slot.origin != class_bundle)
            continue;
        const generic_class = class_nature.generic_instance?.generic_class.class;
        if (generic_class && generic_class.slots.find(s => s.name == slot.name && s.type == slot.type))
            continue;

        let reader = bdef.lookup_nothing_or_assert_bundle(slot.reader_name, scope);
        if (slot.reader_name != Name.make('.') && !reader) 
            reader = reader ? reader : bdef.define_bundle(
                class_expression.position, scope, slot.reader_name);
        const reader_method = generate_class_slot_reader(
            class_bundle, class_expression, slot.name, scope);
        add_method_expression(reader as Bundle, reader_method);

        if (slot.writer_name) {
            let writer = bdef.lookup_nothing_or_assert_bundle(slot.writer_name, scope);
            if (slot.writer_name != Name.make('.:='))
                writer = writer ? writer : bdef.define_bundle(
                    class_expression.position, scope, slot.reader_name);
            const writer_method = generate_class_slot_writer(class_bundle, class_expression, slot.name, scope);
            add_method_expression(writer as Bundle, writer_method);
        }       
    }
}


export function lookup_generic_instance(generic_class: Bundle, generic_actuals: Datum[]) {
    const $poly = Runtime.instance;
    const generated = $poly.generic_class_instances.get(generic_class);
    if (generated) loop_start: for (let generated_bundle of generated) {
        const generated_class = generated_bundle.class as Class_Nature;
        const generic_instance = generated_class.generic_instance as Generic_Class_Instance;
        if (generic_instance.generic_class != generic_class)
            break loop_start;
        const generated_actuals = generic_instance.generic_actuals as Datum[];
        if (generated_actuals.length != generic_actuals.length)
            continue;
        for (var i = 0; i < generated_actuals.length; i++)
            if (generated_actuals[i] != generic_actuals[i]) continue loop_start;
        return generated_bundle;
    }
    return undefined;
}

export function add_generic_instance(generic_class: Bundle, generated_bundle: Bundle) {
    const $poly = Runtime.instance;
    $poly.instance_bundles.push(generated_bundle);
    if (!$poly.generic_class_instances.has(generic_class))
        $poly.generic_class_instances.set(generic_class, []);
    ($poly.generic_class_instances.get(generic_class) as Bundle[]).
        push(generated_bundle);
}


export function evaluate_class_superclasses(class_expression: Class_Expression) {
    const $poly = Runtime.instance;
    const direct_superclasses: Bundle[] = class_expression.superclasses.map(
        e => evaluate_superclass_bundle(e, class_expression.formal_parameters.scope));
    let superclasses: Bundle[] = [
        $poly.lookup('everything') as Bundle,
    ];
    for (let direct_superclass of direct_superclasses) {
        superclasses.push(direct_superclass);
        if (!direct_superclass.class) {
            throw new Error(`superclass must be class bundle!`);
        }
        superclasses.push(...direct_superclass.class.superclasses);
    }
    superclasses = Array.from(new Set(superclasses));
    superclasses.sort((a, b) => is_subclass_or_equal(a, b) ? -1 : 0);
    return superclasses;
}

export function combine_slots(classes: Bundle[]) {
    let slots: Slot_Specifier[] = [];
    for (let bundle of classes) {
        const nature = bundle.class as Class_Nature;
        const direct_slots = nature.slots.filter(s => s.origin == bundle);
        slots.push(...direct_slots);
    }
    slots = slots.filter(slot0 => slot0.origin.class?.generic ?
        !slots.find(slot1 => slot1.name == slot0.name && !slot1.origin.class?.generic) :
        true);

    const slot_names: Set<Name> = new Set();
    let seen_multislot = false;
    for (let slot of slots) {
        if (seen_multislot) {
            throw new Error(`trying to declare slots after multislot!`);
        }
        if (slot_names.has(slot.name)) {
            throw new Error(`duplicate slot name!`);
        }
        slot_names.add(slot.name);
        if (slot.multislot) {
            seen_multislot = true;
        }
    }

    return slots;
}

export function instantiate_internal_array(slot: Type, elements: Datum[], length?: number) {
    const $poly = Runtime.instance;
    const internal_array = $poly.lookup('internal_array');
    let type = internal_array;
    if (internal_array.class?.generic)
        type = instantiate_generic_bundle(internal_array, [slot]) as Bundle;
    return new Internal_Array(type, elements, length);
}

type internal_method_head = {
    required: Datum[], 
    optional: Datum[], 
    named: Map<Name, Datum>, 
    result: Datum, 
    rest?: Datum
};

function register_internal_method(name: Name, head: internal_method_head, modifiers: Method_Modifiers[], method: Function) {
    const $poly = Runtime.instance;
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

export const internal_source_position = new Source_Position('compiler', -1)

export function internal_method_in_module(module: Module, name: Name, head: internal_method_head, modifiers: Method_Modifiers[], method: Function) {
    let defn = lookup(module, name);
    if (!defn) {
        const bundle = new Bundle(name);
        defn = new Known_Definition(internal_source_position, name, bundle);
        add_definition(module, name, defn);
    }
    const bundle = (defn as Known_Definition).value as Bundle;
    internal_method(bundle, head, modifiers, method);
}

export function internal_method(bundle: Bundle, head: internal_method_head, modifiers: Method_Modifiers[], method: Function) {
    bundle.function = bundle.function ? bundle.function : new Function_Nature();
    bundle.function.methods.push(register_internal_method(name, head, modifiers, method));
    bundle.function.methods.sort((a, b) => compare_methods(a.id, b.id));
}

export function internal_method_head(result: Datum, required: Datum[], optional?: Datum[], named?: Map<Name, Datum>, rest?: Datum): internal_method_head {
    return {
        result: result,
        required: required,
        optional: optional || [],
        named: named || new Map(), 
        rest: rest,
    };
}

export class _Batch_Definer {
    definitions: Prog_Expression;

    constructor(position: Source_Position) {
        this.definitions = new Prog_Expression(position, []);
    }

    define(scope: Scope, name: Name, defn: Definition) {
        const expanded = expand_definition(scope, name, defn);
        if (expanded instanceof Prog_Expression) {
            this.definitions.expressions.push(...expanded.expressions);
        }
        return defn;
    }
    
    define_bundle(position: Source_Position, scope: Scope, name: Name) {
        const bundle = new Bundle(name);
        this.define(scope, name, new Known_Definition(position, name, bundle));
        return bundle;
    }
    
    lookup_nothing_or_assert_bundle(name: Name, scope: Scope) {
        const defn = lookup(scope, name);
        if (!defn) return undefined;
        if (defn instanceof Known_Definition && defn.value instanceof Bundle)
            return defn.value;
        throw new Error('incompatible definitions');
    }
}

export function is_member_of(b1: Datum, b2: Bundle): boolean {
    return is_subtype_or_equal(classof(b1), b2);
}

export function is_subclass_or_equal(b1: Bundle, b2: Bundle): boolean {
    if (b1 == b2) return true;

    const superclasses0 = b1.class?.superclasses;
    if (!superclasses0) {
        throw new Error(`invalid bundle comparsion ${b1.name?.spelling} <= ${b2.name?.spelling}`)
    }
    
    for (var i = 0; i < superclasses0.length; i++)
        if (superclasses0[i] == b2) return true;
    return false;
}

export function is_subtype_or_equal(t1: Datum | undefined, t2: Datum | undefined): boolean {
    const $poly = Runtime.instance;
    if (t2 === undefined) 
        return false;
    if (t1 === t2) 
        return true;
    if (t1 instanceof Bundle) {
        if (t2 instanceof Bundle)
            return is_subclass_or_equal(t1, t2);
        if (t2 instanceof Set) {
            for (let e of t2) if (is_subclass_or_equal(classof(e), t1)) 
                return false;
            return true;
        }
    } else if (t1 instanceof Set) {
        if (t2 instanceof Bundle) {
            for (let e of t1) if (!is_subclass_or_equal(classof(e), t2)) 
                return false;
            return true;
        }
        if (t2 instanceof Set) {
            for (let e of t1)  if (!t2.has(e)) 
                return false;
            return true;
        }
    }
    const result = $poly.call(0, $poly.lookup('<='), t1 || false, t2);
    return result;
}