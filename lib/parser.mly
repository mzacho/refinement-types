%{

%}

%token <int> NAT
%token <string> VAR
%token PLUS MINUS TIMES DIV AND OR NEG DOT
%token LPAREN RPAREN LBRACK RBRACK COLON COMMA RARROW
%token FN LET REC IN E_TRUE E_FALSE IF THEN ELSE
%token L_TRUE L_FALSE EQ NEQ GE GT LE LT
%token INT BOOL
%token EOF
%left OR         /* for associative tokens: precedence increases downwards */
%left AND
%left PLUS MINUS
%left TIMES DIV
%left EQ NEQ GE GT LE LT

/* the entry points */
%start program1 ty1
%type <Ast.program> program1
%type <Ast.ty> ty1

%%
program1:
  | program EOF  { $1 }

program:
  | expr  { $1 }

expr:
  | E_TRUE { Ast.E_True }
  | E_FALSE { Ast.E_False }
  | VAR { Ast.E_Var $1 }
  | NAT { Ast.E_Const $1 }
  | LPAREN FN VAR DOT expr RPAREN
    { Ast.E_Abs ($3, $5) }
  | expr VAR { Ast.E_App ($1, $2) }
  | LET VAR EQ expr IN expr
    { Ast.E_Let ($2, $4, $6) }
  | LET REC VAR EQ expr IN expr
    { Ast.E_RLet ($3, $5, $7) }
  | expr COLON ty
    { Ast.E_Ann ($1, $3) }
  | IF VAR THEN expr ELSE expr { Ast.E_If ($2, $4, $6) }
  | LPAREN expr RPAREN { $2 }

param:
  | VAR COLON ty { ($1, $3) }

pred:
  | VAR { Logic.P_Var $1 }
  | NAT { Logic.P_Int $1 }
  /* base logic */
  | L_TRUE { Logic.P_True }
  | L_FALSE { Logic.P_False }
  | pred AND pred { Logic.P_Conj ($1, $3) }
  | pred OR pred { Logic.P_Disj ($1, $3) }
  | NEG pred { Logic.P_Neg $2 }
  /* operators */
  | pred PLUS pred { Logic.P_Op (O_Add, $1, $3) }
  | pred MINUS pred { Logic.P_Op (O_Sub, $1, $3) }
  | pred EQ pred { Logic.P_Op (O_Eq, $1, $3) }
  | pred NEQ pred { Logic.P_Neg (Logic.P_Op (O_Eq, $1, $3)) }
  | pred LT pred { Logic.P_Op (O_Lt, $1, $3) }
  | pred LE pred { Logic.P_Op (O_Le, $1, $3) }
  | pred GT pred { Logic.P_Op (O_Gt, $1, $3) }
  | pred GE pred { Logic.P_Op (O_Ge, $1, $3) }
  /* parentheses */
  | LPAREN pred RPAREN { $2 }

ty1:
  | ty EOF { $1 }

base_ty:
  | INT { Ast.B_Int }
  | BOOL { Ast.B_Bool }

ty:
  /* | base_ty */
  | base_ty LBRACK VAR COLON pred RBRACK
    { Ast.T_Refined ($1, $3, $5) }
/* { Data.t1 } */
  | VAR COLON ty RARROW ty { Ast.T_Arrow ($1, $3, $5) }
