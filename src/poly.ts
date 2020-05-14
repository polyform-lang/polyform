import { Token_From_Char_Stream, File_Char_Stream, Lexer, Poly_Error, Source_Position } from "./token";
import { init_modules_Module } from "./builtin_modules";
import { parse_file, Module, Expression, lookup_known_definition, generic_context_of } from "./expression";
import { JS_compile, JS_context, JS_optimize, JS_body_statement, JS_plain_expression, JS_codeblock_statement, JS_assigment_expression, JS_expression, JS_property_access_expression, JS_call_expression, JS_statement, JS_unroll_statement, JS_compile_method } from "./js_compile";
import { JS_object_reconstructor } from "./js_reconstruct";
import { Bundle, Macro_Context, Name } from "./datum";
import * as fs from 'fs';
import { Runtime } from "./js_runtime";
import { Method_Environment, Runtime_Method_Datum } from './method';
import { Typer_Context } from "./typer";
import { optimize } from "./optimize";
import { js_beautify } from 'js-beautify';
import { relative, dirname } from "path";

export function JS_beatify(js_code: string): string {
    return js_beautify(js_code);
}

function debug_definitions(module: Module, cons: JS_object_reconstructor, body: JS_statement[]) {
    const stringer = lookup_known_definition(module, 'string');
    const stringer_expr = cons.reconstructor_of(stringer);
    for (let defn of module.definitions.values()) {
        if ((defn as any).value && ((defn as any).value instanceof Bundle || (defn as any).value instanceof Module)) {
            continue;
        }
        const _plain = (s: string) => new JS_plain_expression(s, false);
        const label = JSON.stringify(`#${(defn as any).name.spelling}`);
        const reconstruction = cons.reconstructor_of(defn);
        const access_expression = new JS_property_access_expression(reconstruction, 'value');
        const print_exprssion = new JS_call_expression(
            _plain('console.log'),
            [_plain(label), 
             new JS_call_expression(_plain('$poly.call'), 
                [_plain('0'), stringer_expr, access_expression])],
        );
        body.push(print_exprssion);
    }
}

class File_Expression {
    module: Module;
    expression: Expression;

    constructor(module: Module, expression: Expression) {
        this.module = module;
        this.expression = expression;
    }
}

function compile_file(file: string, modules: Module): File_Expression {
    const file_char_stream = new File_Char_Stream(file,  fs.readFileSync(file, 'utf8'));
    const lexer = new Lexer([new Token_From_Char_Stream(file_char_stream)]);
    let file_expression: Expression = parse_file(lexer, 0, modules, true);
    return new File_Expression(modules, file_expression);
}


function JS_convert_to_self_container_bundle(output_path: string, compiled_files: File_Expression[]) {
    const $poly = Runtime.instance;
    const js_context = new JS_context($poly.modules as Module);
    const js_reconstructor = new JS_object_reconstructor(js_context, $poly.mapper);
    js_reconstructor.environment = Method_Environment.Integrated;

    const reconstruct_runtime_property = (key: string, value: any) => {
        if (value instanceof JS_statement && !(value instanceof JS_expression)) {
            js_reconstructor.init_statements.push(value);
            JS_unroll_statement(js_reconstructor.init_statements, js_context);
            value = js_reconstructor.init_statements.pop();
        }
        const assigment = new JS_assigment_expression(
            new JS_plain_expression(`$poly.${key}`, false),
            value instanceof JS_expression ? 
                value : js_reconstructor.reconstructor_of(value));
        js_reconstructor.init_statements.push(assigment);
        return assigment;
    }

    const compiled = new JS_body_statement([]);

    const prehead_mapper_keys = [
        'Host_Datum_Spec',
        'Host_Datum',
    ];

    for (let key in $poly.mapper.objects) {
        if (prehead_mapper_keys.find(k => k == key))
            continue;
        const context = new Macro_Context($poly.modules as Module);
        const value = $poly.mapper.objects[key];
        const expression = js_reconstructor.reconstructor_of(value);
        const name = Name.make(key, context);
        js_reconstructor.add_reconstructor(value, expression, js_context.mangled_binding(name, value));
    }

    reconstruct_runtime_property('instance_bundles', $poly.instance_bundles);
    const module_expression = js_reconstructor.reconstructor_of($poly.modules);
    for (var i = 1; i <= 2; i++) for (let m of $poly.method_datums)
        JS_compile_method(m.id, js_reconstructor);

    for (let bundle of $poly.instance_bundles)
        if (bundle.function) for (let m of bundle.function.methods)
            js_reconstructor.required_method_ids.add(m.id);
        
    reconstruct_runtime_property('method_heads', $poly.method_heads.map(h =>
        js_reconstructor.required_method_ids.has(h.id) ? h : undefined));
    // reconstruct_runtime_property('generic_method_expressions', $poly.generic_method_expressions);
    reconstruct_runtime_property('generic_method_heads', $poly.generic_method_heads);
    reconstruct_runtime_property('modules', module_expression);

    for (var i = 0; i < $poly.class_expressions.length; i++) {
        const class_expression = $poly.class_expressions[i];
        if (!class_expression) continue;
        // reconstruct_runtime_property(`class_expressions[${i}]`, class_expression);
    }
    reconstruct_runtime_property('generic_class_instances', $poly.generic_class_instances);
    reconstruct_runtime_property('generic_class_instance_constructors', $poly.generic_class_instance_constructors);
    reconstruct_runtime_property('generic_class_instance_makers', $poly.generic_class_instance_makers);
    reconstruct_runtime_property('class_index', $poly.class_index);
    reconstruct_runtime_property('method_index', $poly.method_index);
    reconstruct_runtime_property('generic_method_index', $poly.generic_method_index);
    
    const compiled_prototypes: JS_statement[] = [];
    for (let proto of Runtime.instance.mapper.compiled_prototypes) {
        js_reconstructor.init_statements.push(proto.statement);
        JS_unroll_statement(js_reconstructor.init_statements, js_context);
        const assigment = new JS_assigment_expression(
            new JS_property_access_expression(new JS_plain_expression(`$poly.objmap`, false), proto.key),
            js_reconstructor.init_statements.pop() as JS_expression);
        compiled_prototypes.push(assigment);
    }
    const file_statements: JS_statement[] = [];
    for (let file of compiled_files) {
        const js_file = JS_optimize(JS_compile(file.expression, js_context, js_reconstructor));
        file_statements.push(js_file);
    }
    compiled.body.unshift(...js_reconstructor.init_statements);
    compiled.body.unshift(...compiled_prototypes);

    let runtime_path = relative(dirname(output_path), "./bin/js_runtime.js");
    if (!runtime_path.startsWith('.'))
        runtime_path = './' + runtime_path;
    const runtime_initializer = new JS_codeblock_statement(
        `const $runtime = require(${JSON.stringify(runtime_path)});
         (typeof window === 'undefined' ? global : window).$poly = new $runtime.Runtime();
         $runtime.Runtime.instance = $poly;`);
         compiled.body.unshift(runtime_initializer);

    compiled.body.push(...file_statements);
        
    debug_definitions($poly.modules as Module, js_reconstructor, compiled.body); 
    const final_statement = JS_optimize(compiled);
    
    return final_statement;
}

function compile_files(files: string[], output: string, flags: Set<string>) {
    if (files.length == 0) {
        console.error("error: no .poly files listed");
        return;
    }
    init_modules_Module(Runtime.instance);
    const $poly = Runtime.instance;

    const standart_library: string[] = [
        'std/basics.poly',
    ];
    files = standart_library.concat(files);
    if (flags.has('--stat')) console.log(format_input_files_list(files));
    const compiled_files: File_Expression[] = [];
    for (let file of files) {
        const ts_compilation_start = process.hrtime.bigint();
        
        const compiled = compile_file(file, $poly.modules as Module);
        compiled_files.push(compiled);

        const ts_compilation_end = process.hrtime.bigint();
        if (flags.has('--stat')) {
            const ts_elapsed = format_hrtime(ts_compilation_end, ts_compilation_start);
            console.log(format_stat('compiled', ts_elapsed, file));
        }
    }

    const ts_optimize_start = process.hrtime.bigint()
    Typer_Context.enable_aggressive_inlining = true;
    for (var i = 1; i <= 5; i++) {
        for (let file of compiled_files)
            file.expression = optimize(Typer_Context.from_scope(file.module), file.expression, file.module);
        for (let m of $poly.method_expressions) if (m && generic_context_of(m.body, m.formal_parameters.scope).size == 0) 
            optimize(Typer_Context.from_scope(m.formal_parameters.scope), m.body, m.formal_parameters.scope);
    }
    const ts_optimize_end = process.hrtime.bigint();
    if (flags.has('--stat')) {
        const ts_elapsed = format_hrtime(ts_optimize_end, ts_optimize_start);
        console.log(format_stat('optimized', ts_elapsed, $poly.method_index + ' methods'));
    }
    
    const ts_js_output_start = process.hrtime.bigint()
    const final_statement = JS_convert_to_self_container_bundle(output, compiled_files);
    const js_output = final_statement.compile_statement();
    fs.writeFileSync(output, flags.has('--beatify') ? JS_beatify(js_output) : js_output); 
    const ts_js_output_end = process.hrtime.bigint()
    if (flags.has('--stat')) {
        const ts_elapsed = format_hrtime(ts_js_output_end, ts_js_output_start);
        console.log(format_stat('generated', ts_elapsed, 'js output'));
    }
}

export const terminal_colors = {
    reset: "\x1b[0m",
    bright: "\x1b[1m",
    dim: "\x1b[2m",
    underscore: "\x1b[4m",
    blink: "\x1b[5m",
    reverse: "\x1b[7m",
    hidden: "\x1b[8m",

    fg_black: "\x1b[30m",
    fg_red: "\x1b[31m",
    fg_green: "\x1b[32m",
    fg_yellow: "\x1b[33m",
    fg_blue: "\x1b[34m",
    fg_magenta: "\x1b[35m",
    fg_cyan: "\x1b[36m",
    fg_white: "\x1b[37m",

    bg_black: "\x1b[40m",
    bg_red: "\x1b[41m",
    bg_green: "\x1b[42m",
    bg_yellow: "\x1b[43m",
    bg_blue: "\x1b[44m",
    bg_magenta: "\x1b[45m",
    bg_cyan: "\x1b[46m",
    bg_white: "\x1b[47m",
}

function format_stat(header: string, elapsed: string, label?: string) {
    const tc = terminal_colors;
    return header + (label ? ' ' + tc.fg_yellow + label + 
        tc.reset : '') + ' in ' + tc.fg_cyan + elapsed + tc.reset;
}

function format_hrtime(t1: bigint, t2: bigint) {
    const since = new Number(t1 - t2).valueOf();
    return (since / 1000000).toFixed(2) + ' ms';
}

function format_poly_error(e: Poly_Error) {
    const tc = terminal_colors;
    const c = [
        tc.reset,
        tc.reset + tc.bright + tc.fg_cyan,
        tc.reset + tc.bright + tc.fg_yellow,
        tc.reset + tc.bright + tc.fg_red,
    ];
    const position = e.position ?
        e.position : new Source_Position('unknown', -1);
    let message = 
        c[1] + position.name + 
        c[0] + ':' + 
        c[2] + position.line +
        c[0] + ' - ' +
        c[3] + e.domain +
        c[0] + ': ' +
        c[0] + e.message;
    const stack = e.poly_stack ?
        e.poly_stack : Runtime.instance.call_stack;
    for (var i = stack.stack.length - 1; i >= 0; i--) {
        const entry = stack.stack[i];
        const position = stack.make_source_position(entry.location);
        const fmt_position =
            position.name != 'unknown' ?
                position.name + ':' + position.line :
                'internal';
        let method_fmt = 'unknown';
        if (typeof entry.method == 'string') method_fmt = entry.method;
        else if (entry.method instanceof Runtime_Method_Datum) {
            const head = Runtime.instance.method_heads[entry.method.id];
            if (head.name?.spelling) method_fmt = head.name.spelling;
        }
        method_fmt = tc.reset + tc.fg_yellow + method_fmt + tc.reset;
        message += '\n  at ' + method_fmt + ' ' + fmt_position;
    }
    return message;
}

function format_input_files_list(files: string[]) {
    const tc = terminal_colors;
    let message = 'input files:' + tc.reset + '\n';
    for (let k of files.keys())
        message += (k > 0 ? '\n' : '') + '  [' + k.toString() + '] ' + 
            tc.fg_yellow + files[k] + tc.reset;
    return message;
}

function main(args: string[]) {
    if (args.length < 1) {
        console.error("fatal error: help command does not exist...");
        return;
    }
    const flags = new Set(args.filter(f => f.startsWith('--')));
    args = args.filter(f => !f.startsWith('--'));
    switch (args[0]) {
    case "compile":
        try {
            let output_path = './examples/webpack/src/index.js';
            args = args.slice(1);
            if (args[0] == '-o') {
                output_path = args[1]
                args = args.slice(2)
            }
            compile_files(args, output_path, flags);
        } catch (e) {
            if (e instanceof Poly_Error) {
                console.error(format_poly_error(e));
                process.exit(-1);
                return;
            }
            throw e
        }
        break;
    default:
        console.error("error: unknown compiler command");
        return;
    }
}

main(process.argv.slice(2));