type var = string
type op = O_add
(* todo *)

type sort = S_Int

type pred =
  | P_Var of var
  | P_True
  | P_False
  | P_Int of int
  | P_Op of op * pred * pred
  | P_Disj of pred * pred
  | P_Conj of pred * pred
  | P_Neg of pred
(* | P_Fun of var *)

type constraint_ =
  | C_Pred of pred
  | C_Conj of (constraint_ * constraint_)
  | C_Implication of (var * sort * pred * constraint_)

(* Transformations *)

(*
  Variable substitution in predicates: p[v1 := v2]
  
  Substitute v2 for v1 in p
*)
let substitute_pred (p : pred) (v1 : var) (v2 : var) : pred =
  let rec subst_p (p : pred) : pred =
    match p with
    | P_Var v when v = v1 -> P_Var v2
    | P_Op (o, p1, p2) -> P_Op (o, subst_p p1, subst_p p2)
    | P_Disj (p1, p2) -> P_Disj (subst_p p1, subst_p p2)
    | P_Conj (p1, p2) -> P_Conj (subst_p p1, subst_p p2)
    | P_Neg p -> P_Neg (subst_p p)
    | _ -> p
  in
  subst_p p

(*
  Variable substitution in constraints: c[v1 := v2]
  
  Substitute v2 for v1 in c, while avoiding variable capture
*)

let substitute_constraint (c : constraint_) (v1 : var) (v2 : var) : constraint_
    =
  let rec subst_c (c : constraint_) : constraint_ =
    match c with
    | C_Pred p -> C_Pred (substitute_pred p v1 v2)
    | C_Conj (c1, c2) -> C_Conj (subst_c c1, subst_c c2)
    | C_Implication (v, s, p, c') ->
        if not (v = v1) then
          C_Implication (v, s, substitute_pred p v1 v2, subst_c c')
        else c
  in
  subst_c c
