{
open Parser

exception Error of string * Lexing.position

let lexing_error lexbuf =
  let invalid_input = String.make 1 (Lexing.lexeme_char lexbuf 0) in
  raise (Error (invalid_input, lexbuf.Lexing.lex_curr_p))

let classify_identifier ident =
  match ident.[0] with
  | 'a' -> A_IDENTIFIER ident
  | 'e' -> E_IDENTIFIER ident
  | 'z' -> Z_IDENTIFIER ident
  | _ -> OTHER_IDENTIFIER ident
}

let int_literal = ['0'-'9'] ['0'-'9']*
let blank = [' ' '\t']+
let newline = ('\r'* '\n')
let identifier = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']*
let register = ('r' ['1' - '7'] | "ra")

rule token = parse
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | blank+ { token lexbuf }
  | int_literal { INTEGER (int_of_string (Lexing.lexeme lexbuf)) }
  | "unit" { UNIT }
  | "int" { INT }
  | "exists" { EXISTS }
  | "." { DOT }
  | "mu" { MU }
  | "<" { LANGLE }
  | "," { COMMA }
  | ">" { RANGLE }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "pack "{ PACK }
  | "as" { AS }
  | "fold" { FOLD }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | register { REGISTER (Lexing.lexeme lexbuf) }
  | "forall" { FORALL }
  | "{" { LBRACKET }
  | ";" { SEMICOLON }
  | "}" { RBRACKET }
  | ":" { COLON }
  | "::" { DOUBLECOLON }
  | "end" { END }
  | "out" { OUT }
  | "unpack" { UNPACK }
  | "unfold" { UNFOLD }
  | "if0" { IF0 }
  | "pi" { PI }
  | "+" { PLUS }
  | "-" { MINUS }
  | "*" { TIMES }
  | "lam"  { LAMBDA }
  | "->" { ARROW }
  | "?" { QUESTION }
  | identifier { classify_identifier (Lexing.lexeme lexbuf) }
  | eof { EOF }
  | _ { lexing_error lexbuf }
