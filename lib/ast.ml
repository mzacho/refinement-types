type var = int Source.phrase

type ty = ty' Source.phrase
and ty' =
  | T_Var of var
  | T_Arrow of ty * ty

type param' = (var * ty)

type param = param' Source.phrase

type params = param list

type expr = expr' Source.phrase
and expr' =
  | E_Var of var
  | E_Abs of params * expr
  | E_App of expr * expr

type program = expr
