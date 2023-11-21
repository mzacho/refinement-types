type var = string
type base_ty = B_Int | B_Bool

type ty =
  | T_Refined of (base_ty * var * Logic.pred) (* refined base type *)
  | T_Arrow of var * ty * ty (* function type     *)

type expr =
  | E_Const of int
  | E_Var of var
  | E_Abs of var * expr
  | E_App of expr * var
  | E_Let of var * expr * expr
  | E_Ann of expr * ty
  | E_True
  | E_False
  | E_If of var * expr * expr

type program = expr
