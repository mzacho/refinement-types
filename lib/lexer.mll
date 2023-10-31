{
open Parser        (* The type token is defined in parser.mli *)

let convert_pos pos =
  { Source.file = pos.Lexing.pos_fname;
    Source.line = pos.Lexing.pos_lnum;
    Source.column = pos.Lexing.pos_cnum - pos.Lexing.pos_bol
  }

}
rule token = parse
[' ' '\t' '\n']       { token lexbuf }     (* skip blanks *)
  | ['0'-'9']+ as lxm { NAT(int_of_string lxm) }
  | '+'            { PLUS }
  | '-'            { MINUS }
  | '*'            { TIMES }
  | '/'            { DIV }
  | '('            { LPAREN }
  | ')'            { RPAREN }
  | ':'            { COLON }
  | ','            { COMMA }
  | "->"           { RARROW }
  | "fn"           { FN }
  | eof { EOF }
