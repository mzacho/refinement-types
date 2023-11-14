%{

%}

%token <int> NAT
%token <string> VAR
%token PLUS MINUS TIMES DIV AND OR NEG DOT
%token LPAREN RPAREN LBRACK RBRACK COLON COMMA RARROW
%token FN LET IN
%token TRUE FALSE EQ NEQ GE GT LE LT
%token INT
%token EOF
%left PLUS MINUS        /* lowest precedence */
%left TIMES DIV         /* medium precedence */
%nonassoc UMINUS        /* highest precedence */
%start program1 ty1             /* the entry points */
%type <Ast.program> program1
%type <Ast.ty> ty1

%%
program1:
  | program EOF  { $1 }

program:
  | expr  { $1 }

expr:
  | var { Ast.E_Var $1 }
  | NAT { Ast.E_Const $1 }
  | LPAREN FN var DOT expr RPAREN
    { Ast.E_Abs ($3, $5) }
  | expr var { Ast.E_App ($1, $2) }
  | LET var EQ expr IN expr
    { Ast.E_Let ($2, $4, $6) }
  | expr COLON ty
    { Ast.E_Ann ($1, $3) }

param:
  | var COLON ty { ($1, $3) }

var:
  | VAR { $1 } /* todo: parse string $1 */

pred:
  | var { Logic.P_Var $1 }
  | TRUE { Logic.P_True }
  | FALSE { Logic.P_False }
  | NAT { Logic.P_Int $1 }
  | pred AND pred { Logic.P_Conj ($1, $3) }
  | pred OR pred { Logic.P_Disj ($1, $3) }
  | NEG pred { Logic.P_Neg $2 }
  | pred EQ pred { Logic.P_Op (O_Eq, $1, $3) }
  | pred NEQ pred { Logic.P_Neg (Logic.P_Op (O_Eq, $1, $3)) }
  | pred LT pred { Logic.P_Op (O_Lt, $1, $3) }
  | pred LE pred { Logic.P_Op (O_Le, $1, $3) }
  | pred GT pred { Logic.P_Op (O_Gt, $1, $3) }
  | pred GE pred { Logic.P_Op (O_Ge, $1, $3) }

ty1:
  | ty EOF { $1 }

base_ty:
  | INT { Ast.B_Int }

ty:
  /* | base_ty */
  | base_ty LBRACK var COLON pred RBRACK
    { Ast.T_Refined ($1, $3, $5) }
/* { Data.t1 } */
  | var COLON ty RARROW ty { Ast.T_Arrow ($1, $3, $5) }
