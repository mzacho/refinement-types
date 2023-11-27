type var = string
type base_ty = B_Int | B_Bool | B_TyCtor of string

type ty =
  | T_Refined of (base_ty * var * Logic.pred) (* refined base type *)
  | T_Arrow of var * ty * ty (* function type     *)

type ty_ctor = base_ty * (var * ty) list
type data_ctor_decl = var * (var * ty) list * (var * Logic.pred) option
type ty_ctor_decl = var * data_ctor_decl list

type metric = Logic.pred list

type expr =
  | E_Const of int
  | E_Var of var
  | E_Abs of var * expr
  | E_App of expr * var
  | E_Let of var * expr * expr
  | E_RLet of var * expr * ty * metric * expr
  | E_Ann of expr * ty
  | E_True
  | E_False
  | E_If of var * expr * expr
  | E_Switch of var * alt list

and alt = Alt of var * var list * expr

type program = Program of { ty_ctors : ty_ctor_decl list; expression : expr }
