type var = string

type base_ty =
  | B_Int

type ty =
  | T_Refined_base of (base_ty * var * Solver.pred)
  | T_Arrow of var * ty * ty

type expr =
  | E_Const of int
  | E_Var of var
  | E_Abs of var * expr
  | E_App of expr * var
  | E_Let of var * expr * expr
  | E_Ann of expr * ty

type program = expr
