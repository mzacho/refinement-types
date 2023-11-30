type var = string
type base_ty = B_Int | B_Bool | B_TyCtor of string

type ty =
  | T_Refined of (base_ty * var * Logic.pred) (* refined base type *)
  | T_Arrow of var * ty * ty (* function type     *)

type data_ctor = var * (var * ty) list * (var * Logic.pred) option
type ty_ctor = var * data_ctor list

let tc_to_tys (tc, dcs) =
  let dc_to_ty (dc, params, refinement) =
    let v, p =
      match refinement with Some (v, p) -> (v, p) | None -> ("v", Logic.P_True)
    in
    let dc_out = T_Refined (B_TyCtor tc, v, p) in
    let dc_ty =
      List.fold_right (fun (x, s) t -> T_Arrow (x, s, t)) params dc_out
    in
    (dc, dc_ty)
  in
  List.map dc_to_ty dcs

type expr =
  | E_Const of int
  | E_Var of var
  | E_Abs of var * expr
  | E_App of expr * var
  | E_Let of var * expr * expr
  | E_RLet of var * expr * ty * expr
  | E_Ann of expr * ty
  | E_True
  | E_False
  | E_If of var * expr * expr
  | E_Switch of var * alt list

and alt = Alt of var * var list * expr

type program = Program of { ty_ctors : ty_ctor list; expression : expr }
