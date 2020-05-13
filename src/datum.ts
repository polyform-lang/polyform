import { Lexer, Token } from "./token";
import { Expression, Scope, Module, Method_Head } from "./expression";
import { Runtime_Method_Datum, Runtime_Generic_Method_Datum } from "./method";

export interface Datum {
    datumclass(): Bundle | string;
    
    getslot(name: Name): Datum;
    setslot(name: Name, datum: Datum): void;
}

export type Type = Datum;

export class Host_Datum_Slot_Spec {
    reader: (obj: any) => Datum;
    writer: (obj: any, datum: Datum) => void;

    constructor(reader: (obj: any) => Datum, writer: (obj: any, datum: Datum) => void) {
        this.reader = reader;
        this.writer = writer;
    }
}

export class Host_Datum_Spec {
    class: Bundle | string;
    slots: Map<Name, string | Host_Datum_Slot_Spec>;

    constructor(bundle: Bundle | string, slots: [Name, string | Host_Datum_Slot_Spec][]) {
        this.class = bundle;
        this.slots = new Map(slots);
    }
}

export class Host_Datum implements Datum {
    readonly $datumspec: Host_Datum_Spec;

    constructor(datum_spec: Host_Datum_Spec) {
        this.$datumspec = datum_spec;
    }

    getslot(name: Name): Datum {
        const slot_spec = this.$datumspec.slots.get(name);
        if (!slot_spec) {
            throw new Error('expected slot missing');
        }
        if (typeof slot_spec == 'string') {
            return (this as any)[slot_spec];
        }
        return slot_spec.reader(this as any);
    }

    setslot(name: Name, datum: Datum): void {
        const slot_spec = this.$datumspec.slots.get(name);
        if (!slot_spec) {
            throw new Error('expected slot missing');
        }
        if (typeof slot_spec == 'string') {
            (this as any)[slot_spec] = datum;
            return;
        }
        if (!slot_spec.writer) {
            throw new Error('slot is not writable');
        }
        slot_spec.writer(this as any, datum);
    }

    datumclass(): Bundle | string {
        return this.$datumspec.class;
    }
}

export class Macro_Context extends Host_Datum {
    parent_scope: Scope;
    names: Map<string, Name> = new Map();

    constructor(parent_scope: Scope) {
        super(Macro_Context_datum_spec);
        this.parent_scope = parent_scope;
    }
}

export type Name_Context = Module | Macro_Context;

export class Name extends Host_Datum {
    readonly spelling: string;
    readonly context: Name_Context | undefined;

    constructor(name: Name | string, context?: Name_Context) {
        super(Name_datum_spec);
        this.spelling = (name instanceof Name ? name.spelling : name).toLowerCase();
        if (context) {
            this.context = context;
        }
    }

    equal(other: Name | string): boolean {
        if (typeof other == 'string') {
            return !this.context && other == this.spelling;
        }
        return this.spelling == other.spelling &&
            this.context == other.context;
    }

    static same_spelling(n0: Name | string | any, n1: Name | string | any): boolean {
        const spelling0 = n0 instanceof Name ?
            n0.spelling : (typeof n0 == 'string' ? n0 : undefined);
        const spelling1 = n1 instanceof Name ?
            n1.spelling : (typeof n1 == 'string' ? n1 : undefined);
        if (!spelling0 || !spelling1) {
            return false;
        }
        return spelling0 == spelling1;
    }

    static make(name: Name | string, context?: Name_Context) {
        const spelling = (name instanceof Name ? name.spelling : name).toLowerCase();
        const interner = context instanceof Macro_Context ?
            context.names : Name._names;
        const existing = interner.get(spelling);
        if (existing) {
            return existing;
        }
        const new_name = new Name(name, context);
        interner.set(spelling, new_name);
        return new_name;
    }

    static _names = new Map<string, Name>();
}

export const Name_datum_spec = new Host_Datum_Spec(
    'name', [
        [Name.make('spelling'), 'spelling'],
    ]);

export const Macro_Context_datum_spec = new Host_Datum_Spec(
    'macro_context', []);

export class Function_Nature {
    readonly methods: Runtime_Method_Datum[];
    generic_methods?: Runtime_Generic_Method_Datum[];
    // requirements   

    constructor() {
        this.methods = [];
    }
}

export type Class_Modifier = 
    'abstract' | 'intrinsic' | 'sealed' |
    'autothrow' | 'noreturn' | 'generic';

export class Slot_Specifier {
    readonly name: Name;
    readonly type: Datum;
    readonly origin: Bundle;
    readonly reader_name: Name;
    readonly writer_name?: Name;
    readonly multislot?: boolean;
    
    constructor(
        name: Name, 
        type: Datum, 
        origin: Bundle, 
        reader_name: Name, 
        writer_name?: Name,
        mutislot?: boolean) {
            this.name = name;
            this.type = type;
            this.reader_name = reader_name;
            this.origin = origin;
            if (writer_name) this.writer_name = writer_name;
            if (mutislot) this.multislot = true;
        }

    get root_origin() {
        if (this.origin?.class?.generic_instance)
            return this.origin.class.generic_instance.generic_class;
        return this.origin;
    }
} 

export class Generic_Class_Instance_Maker {
    class_maker?: Bundle;
    constructor_maker?: Bundle;

    constructor(class_maker?: Bundle, constructor_maker?: Bundle) {
        if (class_maker) this.class_maker = class_maker;
        if (constructor_maker) this.constructor_maker = constructor_maker;
    }
}

export class Generic_Class_Instance {
    generic_class: Bundle;
    generic_actuals: Datum[];

    constructor(generic_class: Bundle, generic_actuals: Datum[]) {
        this.generic_class = generic_class;
        this.generic_actuals = generic_actuals;
    }
}

export class Class_Nature {
    id: number;
    constructor_name?: Name;
    superclasses: Bundle[];
    slots: Slot_Specifier[];
    generic_instance?: Generic_Class_Instance;

    abstract?: boolean;
    intrinsic?: boolean;
    sealed?: boolean;
    autothrow?: boolean;
    noreturn?: boolean;
    generic?: boolean;

    constructor(class_id: number, constructor_name: Name | undefined, superclasses: Bundle[], slots: Slot_Specifier[], modifiers: Set<Class_Modifier>) {
        this.id = class_id;
        if (constructor_name) this.constructor_name = constructor_name;
        this.superclasses = superclasses;
        this.slots = slots;

        if (modifiers.has('abstract')) 
            this.abstract = true;
        if (modifiers.has('intrinsic'))
            this.intrinsic = true;
        if (modifiers.has('sealed')) 
            this.sealed = true;
        if (modifiers.has('autothrow')) 
            this.autothrow = true;
        if (modifiers.has('noreturn')) 
            this.noreturn = true;
        if (modifiers.has('generic')) 
            this.generic = true;
    }
}

export type Operator_Arity = 'unary' | 'binary' | 'ternary' | 'prefix' | 'infix' | 'suffx';

export type Prefix_Expander = (
    lexer: Lexer, 
    indentation: number, 
    scope: Scope, 
    modifiers: Set<string>, 
    previous_context?: Macro_Context | Module) => Expression | Token[];

export type Infix_Expander = (
    lhs: Expression,
    lexer: Lexer, 
    indentation: number, 
    scope: Scope, 
    previous_context?: Macro_Context | Module,
    method_head_flag?: boolean) => Expression | Token[] | Method_Head;

export class Operator_Nature {
    arity: Set<Operator_Arity>;
    left_precedence: number;
    right_precedence: number;

    prefix_expander?: Runtime_Method_Datum;
    infix_expander?: Runtime_Method_Datum;
    
    constructor() {
        this.arity = new Set();
        this.left_precedence = 0;
        this.right_precedence = 0;
    }
}

export const Bundle_datum_spec = new Host_Datum_Spec(
    'bundle', []); 

export class Bundle extends Host_Datum {
    readonly name?: Name;

    class?: Class_Nature;
    function?: Function_Nature;
    operator?: Operator_Nature;

    constructor(name?: Name) {
        super(Bundle_datum_spec);
        this.name = name;
    }

    datumclass(): string | Bundle {
        const c = !!this.class;
        const f = !!this.function;
        const o = !!this.operator;
        if (c && f && o) {
            return 'class_function_operator_bundle';
        }
        if (c && f) {
            return 'class_function_bundle';
        }
        if (c && o) {
            return 'class_operator_bundle';
        }
        if (f && o) {
            return 'function_operator_bundle';
        }
        if (c) {
            return 'class_bundle'
        }
        if (f) {
            return 'function_bundle'
        }
        if (o) {
            return 'operator_bundle';
        }
        return 'bundle';
    }
}

export const Char_datum_spec = new Host_Datum_Spec(
    'character', [
        [Name.make('code'), 'code'],   
    ]);

export class Char extends Host_Datum {
    readonly code: number;

    constructor(char: string | number) {
        super(Char_datum_spec);
        if (typeof char == 'string' && char.length != 1)
            throw new Error('trying to construct character from string with length != 1 ...');
        this.code = typeof char == 'number' ? char : char.charCodeAt(0);
    }
}

export class Internal_Array implements Datum {
    readonly $datumclass: Bundle;
    readonly array: any[];
    readonly length: number;

    constructor($datumclass: Bundle, elements: any[] | Internal_Array, length?: number) {
        this.$datumclass = $datumclass;
        if (length === undefined) {
            this.array = elements instanceof Internal_Array ?
                elements.array : elements;
            this.length = elements.length;
            return;
        }
        this.length = length;
        this.array = [];
        if (elements instanceof Internal_Array) for (var i = 0; i < length; i++)
            this.array.push(elements.array[i]);
        else for (var i = 0; i < length; i++)
            this.array.push(elements[i]);
    }

    datumclass() { return this.$datumclass; }
    getslot(name: Name): Datum { throw new Error('expected slot missing'); };
    setslot(name: Name, datum: Datum) {  throw new Error('expected slot missing'); };
}

export const Type_Union_datum_spec = new Host_Datum_Spec(
    'type_union', []);

export class Type_Union extends Host_Datum {
    types: Set<Datum>;

    constructor(...parameters: Datum[]) {
        super(Type_Union_datum_spec);
        const types: Datum[] = [];
        for (let type of parameters)
            if (type instanceof Type_Union)
                types.push(...type.types);
            else types.push(type);
        this.types = new Set(types);
    }
}

export const Type_Intersection_datum_spec = new Host_Datum_Spec(
    'type_intersection', []);

export class Type_Intersection extends Host_Datum {
    types: Set<Datum>;

    constructor(...parameters: Datum[]) {
        super(Type_Intersection_datum_spec);
        const types: Datum[] = [];
        for (let type of parameters)
            if (type instanceof Type_Intersection)
                types.push(type);
            else types.push(type);
        this.types = new Set(types);
    }
}

declare global {
    interface Number {
        datumclass(): Bundle | string;

        getslot(name: Name): Datum;
        setslot(name: Name, datum: Datum): void;
    }
    
    interface String {
        datumclass(): Bundle | string;

        getslot(name: Name): Datum;
        setslot(name: Name, datum: Datum): void;
    }

    interface Boolean {
        datumclass(): Bundle | string;

        getslot(name: Name): Datum;
        setslot(name: Name, datum: Datum): void;
    }

    interface Set<T> {
        datumclass(): Bundle | string;

        getslot(name: Name): Datum;
        setslot(name: Name, datum: Datum): void;
    }

    interface Array<T> {
        datumclass(): Bundle | string;

        getslot(name: Name): Datum;
        setslot(name: Name, datum: Datum): void;
    }
}

Number.prototype.getslot = function(name: Name): Datum {
    throw new Error('expected slot missing');
}

Number.prototype.setslot = function(name: Name, datum: Datum) {
    throw new Error('expected slot missing');
}

Number.prototype.datumclass = function(): Bundle | string { 
    return Number.isInteger(this.valueOf()) ? 'integer' : 'float'; 
};

String.prototype.getslot = function(name: Name): Datum {
    throw new Error('expected slot missing');
}

String.prototype.setslot = function(name: Name, datum: Datum) {
    throw new Error('expected slot missing');
}

String.prototype.datumclass = function(): Bundle | string {
    return 'string';
}

Boolean.prototype.getslot = function(name: Name): Datum {
    throw new Error('expected slot missing');
}

Boolean.prototype.setslot = function(name: Name, datum: Datum) {
    throw new Error('expected slot missing');
}

Boolean.prototype.datumclass = function(): Bundle | string {
    return this ? '_true' : '_false';
}

Set.prototype.getslot = function(name: Name): Datum {
    throw new Error('expected slot missing');
}

Set.prototype.setslot = function(name: Name, datum: Datum) {
    throw new Error('expected slot missing');
}

Set.prototype.datumclass = function(): Bundle | string {
    return 'internal_set';
}

Array.prototype.getslot = function(name: Name): Datum {
    throw new Error('expected slot missing');
}

Array.prototype.setslot = function(name: Name, datum: Datum) {
    throw new Error('expected slot missing');
}

Array.prototype.datumclass = function(): Bundle | string {
    return 'internal_list';
}
