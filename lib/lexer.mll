{
open Parser        (* The type token is defined in parser.mli *)

let convert_pos pos =
  { Source.file = pos.Lexing.pos_fname;
    Source.line = pos.Lexing.pos_lnum;
    Source.column = pos.Lexing.pos_cnum - pos.Lexing.pos_bol
  }

}

let letter = ['a'-'z''A'-'Z']
let name = letter+

rule token = parse
    [' ' '\t' '\n']       { token lexbuf }     (* skip blanks *)
  | ['0'-'9']+ as lxm { NAT(int_of_string lxm) }
  | '+'            { PLUS }
  | '-'            { MINUS }
  | '*'            { TIMES }
  | '/'            { DIV }
  | '('            { LPAREN }
  | ')'            { RPAREN }
  | '{'            { LBRACK }
  | '}'            { RBRACK }
  | ":"            { COLON }
  | ','            { COMMA }
  | '.'            { DOT }
  | "="            { EQ }
  | "!="           { NEQ }
  | "<="           { LE }
  | "<"            { LT}
  | ">="           { GE }
  | ">"            { GT }
  | '~'            { NEG }
  | '&'            { AND }
  | '|'            { OR }
  | "->"           { RARROW }
  | "fn"           { FN }
  | "let"          { LET }
  | "in"           { IN }
  | "True"         { L_TRUE }
  | "true"         { E_TRUE }
  | "False"        { L_FALSE }
  | "false"        { E_FALSE }
  | "int"          { INT }
  | "bool"         { BOOL }
  | name as s      { VAR s }
  | eof { EOF }
