import { Expression } from "./expression";
import { Datum, Bundle, Char, Name, Host_Datum_Spec, Host_Datum } from "./datum";
import { Call_Stack } from "./js_runtime";

export class Poly_Error extends Error {
    position?: Source_Position;
    domain: string;
    poly_stack?: Call_Stack;

    constructor(position: Source_Position | undefined, domain: string, message: string, stack?: Call_Stack) {
        super(message);
        this.position = position;
        this.domain = domain;
        if (stack) this.poly_stack = stack;
    }
}

export class Parse_Error extends Poly_Error {
    constructor(position: Source_Position | Lexer | undefined, message: string) {
        super(position instanceof Lexer ? position.position() : position, 'parse error', message);   
    }
}

export const Newline_datum_spec = new Host_Datum_Spec(
    'newline', []);

export class Newline extends Host_Datum {
    readonly indentation: number;
    readonly relative?: boolean;

    constructor(indentation: number, relative?: boolean) {
        super(Newline_datum_spec);
        this.indentation = indentation;
        if (relative) this.relative = true;
    }
}

export const Keyword_datum_spec = new Host_Datum_Spec(
    'keyword', []);

export class Keyword extends Host_Datum {
    readonly name: Name;

    constructor(name: Name) {
        super(Keyword_datum_spec);
        this.name = name;
    }
}

export type Literal = number | string | Char;
export type Token = Keyword | Newline | Expression;

export interface Token_Stream {
    read(adjust_position?: number): Token | undefined;
    position(): Source_Position;
}

export class Token_Array_Stream implements Token_Stream {
    tokens: Token[];
    token_position: number;
    source_position?: Source_Position;

    constructor(tokens: Token[], position: Source_Position) {
        this.tokens = tokens;
        for (let i = 0; i < tokens.length; i++) {
            const token = tokens[i];
            if (token instanceof Newline && token.relative) {
                if (position.colon < 0) throw new Error('ughhhhm....');
                tokens[i] = new Newline(token.indentation + position.colon);
            }
        }
        this.token_position = 0;
        this.source_position = position;
    }

    read(adjust_position: number = 0): Token | undefined {
        const token = this.tokens[this.token_position];
        this.token_position += adjust_position;
        return token;
    }

    position(): Source_Position {
        return this.source_position ? 
            this.source_position : new Source_Position('unknown', -1, -1);
    }
}

export class Token_Stream_Cast implements Token_Stream {
    readonly streams: Token_Stream[];

    read(adjust_position: number = 0): Token | undefined {
        if (this.streams.length == 0) {
            return undefined;
        }
        const active_stream = this.streams[this.streams.length - 1];
        if (active_stream.read(0) === undefined && this.streams.length > 1) {
            this.streams.pop();
            return this.read(adjust_position);
        }
        const token = active_stream.read(adjust_position);
        return token;
    }

    insert(stream: Token_Stream | Token[], position?: Source_Position) {
        const _stream: Token_Stream = Array.isArray(stream) ?
            new Token_Array_Stream(stream, position ? position : this.position())
            : stream;
        this.streams.push(_stream);
    }

    position(): Source_Position {
        if (this.streams.length == 0) {
            return new Source_Position(
                "unknown", -1, -1);
        }
        return this.streams[this.streams.length - 1].position();
    }

    constructor(streams: Token_Stream[] = []) {
        this.streams = streams;
    }
}

export class Lexer extends Token_Stream_Cast implements Datum {    
    match_name(spelling: Name | string): Name | undefined {
        const token = this.read(0);
        if (token instanceof Name && Name.same_spelling(spelling, token)) {
            this.read(1);
            return token;
        }
        return undefined;
    }

    must_match_name(spelling: Name | string): Name {
        spelling = spelling instanceof Name ? spelling.spelling : spelling;
        const name = this.match_name(spelling);
        if (!name) {
            throw new Parse_Error(this, `expected token ${spelling}`);
        }
        return name;
    }

    match_keyword(spelling: string): Keyword | undefined {
        const token = this.read(0);
        if (token instanceof Keyword && Name.same_spelling(token.name, spelling)) {
            this.read(1);
            return token;
        }
        return undefined;
    }

    match_newline(indentation: number, indent: boolean): Newline | undefined {
        const token = this.read(0);
        if (token instanceof Newline) {
            if (indent && token.indentation < indentation) {
                return undefined;
            }
            if (!indent && token.indentation != indentation) {
                return undefined;
            }
            this.read(1);
            return token;
        }
        return undefined;
    }

    read(adjust_position: number = 0): Token | undefined {
        const token = super.read(adjust_position);
        return token;
    }

    datumclass(): Bundle | string {
        return 'token_stream';
    }

    getslot(name: Name): Datum {
        return false;
    }

    setslot(name: Name, datum: Datum) {
        return false;
    }
}

export class Token_From_Char_Stream implements Token_Stream {
    char_stream: Positioned_Char_Stream;
    token: Token | undefined;
    token_position: Source_Position;

    constructor(char_stream: Positioned_Char_Stream) {
        this.char_stream = char_stream;
        this.token_position = this.char_stream.position();
        this.token = parse_Token(this.char_stream);
    }

    read(adjust_position: number = 0): Token | undefined {
        const token = this.token;
        for (let i = 0; i < adjust_position; i++) {
            this.token_position = this.char_stream.position();
            this.token = parse_Token(this.char_stream);
        }
        return token;
    }

    position(): Source_Position {
        return this.token_position;
    }
}

export function parse_Token(s: Positioned_Char_Stream): Token | undefined {
    let char = s.read(0);
    const next = () => {
        const previous = s.read(1);
        char = s.read(0);
        return previous;
    };

    // skip whitespace and comments and/or parse newline token
    {
        let potential_indentation = 0;
        let newlines = 0;
        let skipping_comment = false;

        while (is_whitespace(char) || char == ';' || skipping_comment || char == '\\') {
            if (char == '\\' && !skipping_comment) {
                s.read(1);
                const char_after_slash = s.read(0);
                if (!is_newline(char_after_slash)) {
                    s.read(-1);
                    break;
                }
                s.read(-1);
                next();
                next();
                continue;
            } if (char == ';') {
                skipping_comment = true;
            } else if (is_newline(char)) {
                potential_indentation = 0;
                newlines += 1;
                skipping_comment = false;
            } else {
                potential_indentation += 1;
            }
            if (char === undefined) {
                return undefined;
            }
            next();
        }

        if (char && newlines > 0) {
            return new Newline(potential_indentation);
        }
    }

    // parsing Integer or Float
    if (is_numeric(char)) {
        let literal = '';
        let decimal_delimeters = 0;
        while(is_numeric(char) || char == '.') {
            if (char == '.') {
                decimal_delimeters++;
                next();
                if (!is_numeric(char)) {
                    s.read(-1);
                    return parseInt(literal);
                }
                literal += '.';
                continue;
            }
            literal += next();
        }
        if (literal[literal.length - 1] == '.') {
            s.read(-1);
            return parseInt(literal.slice(0, literal.length - 1));
        }
        if (decimal_delimeters == 0) {
            return parseInt(literal);
        }
        return parseFloat(literal);
    }

    // parsing alphanumeric Name or Keyword
    if (is_alphanumeric(char)) {
        let literal = '';
        while(is_alphanumeric(char) || is_numeric(char)) {
            literal += next();
        }
        const name = Name.make(literal);
        if (char == ':') {
            next();
            return new Keyword(name);
        }
        return name;
    }

    // parsing punctuation Name
    if (is_punctuation(char)) {
        const spelling = next();
        return Name.make(spelling as string);
    }

    // parsing symbolic Name
    if (is_symbolic(char)) {
        let literal = '';
        while (is_symbolic(char)) {
            literal += next();
        }
        return Name.make(literal);
    }

    // parsing String
    if (char == '"') {
        const start_position = s.position();
        next();
        let literal = '';
        while (char != '"' && char) {
            literal += next();
        }
        if (char === undefined) {
            throw new Parse_Error(start_position, "unexpected eof while parsing string literal");
        }
        next();
        return literal;
    }

    // parsing Character
    if (char == "'")  {
        const start_position = s.position();
        next();
        let literal = '';
        while (char != "'" && char) {
            literal += next();
        }
        if (char === undefined) {
            throw new Parse_Error(start_position, "unexpected eof while parsing character literal");
        }
        next();
        return new Char(literal);
    }

    if (char !== undefined) {
        throw new Parse_Error(s.position(), "invalid token!");
    }

    return undefined;
}

export interface Char_Stream {
    read(adjust_position?: number): string | undefined;
}

export class Source_Position {
    name: string;
    line: number;
    colon: number;

    constructor(source_name: string, source_line: number, source_colon: number = -1) {
        this.name = source_name;
        this.line = source_line;
        this.colon = source_colon;
    }
}

export interface Positioned_Char_Stream extends Char_Stream {
    position(): Source_Position
}

export class File_Char_Stream implements Positioned_Char_Stream {
    file_content: string;
    readonly file_name: string;
    
    file_position: number;
    file_line_number: number;
    line_positions: number[] = [0];

    _offset: number = 0;

    constructor(file_name: string, file_content: string) {
        this.file_content =file_content;
        if (!this.file_content) {
            throw new Error(`unable to read content of "${file_name}"`);
        }
        this.file_name = file_name;

        this.file_line_number = 1;
        this.file_position = 0;
    }

    read(adjust_position: number = 0): string | undefined {
        if (this.file_content.length <= this.file_position) {
            return undefined;
        }
        const char = this.file_content[this.file_position];
        if (adjust_position != 0) {
            this._correct_line_number(adjust_position);
            while (this.line_positions.length > this.file_line_number + 1 && 
                    this.file_position + adjust_position > this.line_position)
                this.file_line_number++;
            for (var i = this.file_position; i < this.file_position + adjust_position; i++) {
                if (this._offset < 0) {
                    this._offset++;
                    continue;
                }
                const skip_char = this.file_content[i];
                if (skip_char == '\n') {
                    this.file_line_number++;
                    this.line_positions[this.file_line_number] = i+1;
                } 
            }
            this.file_position += adjust_position;
            if (adjust_position < 0) this._offset += adjust_position;   
            this._correct_line_number();
        }
        return char;
    }

    // pretty dirty stuff ... line/colon detection mechanism needs to be different...
    _correct_line_number(adjust: number = 0) {
        while (this.file_position + adjust < this.line_position)
            this.file_line_number--;
        while (this.line_positions.length > this.file_line_number + 1 &&
            this.file_position + adjust > this.line_position)
            this.file_line_number++;
    }

    get line_position(): number {
        return this.line_positions[this.file_line_number];
    }

    position(): Source_Position {
        return new Source_Position(
            this.file_name, this.file_line_number, 
            this.file_position - this.line_position);
    }
}

function every_char(str: string, cond: (c: string) => boolean): boolean {
    if (str.length == 0) {
        return false;
    }
    for (let i = 0; i < str.length; i++) {
        if (!cond(str.charAt(i))) {
            return false;
        }
    }
    return true;
}

export function is_letters(str: string = ''): boolean {
    return every_char(str, (c) => (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'));
}

export function is_numeric(str: string = ''): boolean {
    return every_char(str, (c) => c >= '0' && c <= '9');
}

var _punctuation = new Set(['`', '@', '#', '$', '(', ')', '[', ']', '{', '}', '\\', ',', '...']);
export function is_punctuation(c: string = ''): boolean {
    return _punctuation.has(c);
}

var _symbolic = new Set(['+', '-', '*', '/', '%', '^', '~', '&', '|', '=', '<', '>', ':', '.']);
export function is_symbolic(str: string = ''): boolean {
    return every_char(str, (c) => _symbolic.has(c));
}

var _alphanumeric_additional = new Set(['_', '?', '!', '¿', '¡',]);
export function is_alphanumeric(str: string = ''): boolean {
    if (str.length == 0) {
        return false;
    }
    if (is_numeric(str.charAt(0))) {
        return false;
    }
    return every_char(str, (c) => 
        is_letters(c) || is_numeric(c) || _alphanumeric_additional.has(c));
}

export function is_whitespace(c: string = ''): boolean {
    return/^\s+$/.test(c);   
}

export function is_newline(c: string = ''): boolean {
    return /^\n+$/.test(c);
}