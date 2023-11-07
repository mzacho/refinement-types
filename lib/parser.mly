%{
open Source

(* let error at msg = raise (Error.Syntax (at, msg)) *)

(* Position handling *)

let position_to_pos position =
  { file = position.Lexing.pos_fname;
    line = position.Lexing.pos_lnum;
    column = position.Lexing.pos_cnum - position.Lexing.pos_bol
  }

let positions_to_region position1 position2 =
  { left = position_to_pos position1;
    right = position_to_pos position2
  }

let at () =
  positions_to_region (Parsing.symbol_start_pos ()) (Parsing.symbol_end_pos ())

%}

%token <int> NAT
%token PLUS MINUS TIMES DIV
%token LPAREN RPAREN COLON COMMA RARROW
%token FN
%token EOF
%left PLUS MINUS        /* lowest precedence */
%left TIMES DIV         /* medium precedence */
%nonassoc UMINUS        /* highest precedence */
%start program1             /* the entry point */
%type <Ast.program> program1

%%
program1:
  | program EOF  { $1 }

program:
  | expr  { $1 }

expr:
  | var { Ast.E_Var $1 }
  /* fun abstractions */
  | LPAREN FN LPAREN param_list RPAREN expr RPAREN
    { Ast.E_Abs ($4, $6) }
  /* fun applications */
  | expr expr { Ast.E_App ($1, $2) }

/* todo: dumb parsing, always terminates with a , */
param_list:
  | /* empty */ { [] }
  | param COMMA param_list { $1 :: $3 }

param:
  | var COLON ty { ($1, $3) }

var:
  | NAT { $1 }

ty:
  | var { (Ast.T_Var $1) }
  | ty RARROW ty { Ast.T_Arrow ($1, $3) }
