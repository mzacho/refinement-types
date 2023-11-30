type var = string
type op = O_Add | O_Sub | O_Eq | O_Lt | O_Le | O_Ge | O_Gt
type sort = S_Int | S_Bool | S_TyCtor of string
type uninterp_fun = var * sort list * sort (* f : (X1, X2, ..., Xn) -> Y *)

type pred =
  | P_Var of var
  | P_True
  | P_False
  | P_Int of int
  | P_Op of op * pred * pred
  | P_Disj of pred * pred
  | P_Conj of pred * pred
  | P_Neg of pred
  | P_FunApp of var * pred list (* f(p1, p2, ..., pn) *)

type constraint_ =
  | C_Pred of pred
  | C_Conj of (constraint_ * constraint_)
  | C_Implication of (var * sort * pred * constraint_)

(* Convenience implication infix operator:
   forall x:b. p => c ::= (x, b, p) ==> c
*)
let ( ==> ) ((x, b, p) : var * sort * pred) (c : constraint_) =
  C_Implication (x, b, p, c)

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
    | P_FunApp (f, args) -> P_FunApp (f, List.map subst_p args)
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
        if not (v = v1) then (v, s, substitute_pred p v1 v2) ==> subst_c c'
        else c
  in
  subst_c c

(* Make forall binders unique *)
let uniqueify_binders (c : constraint_) : constraint_ =
  (* Map from binders (forall bound variables) to how many times we've previously seen a binder with the same name *)
  let m : (var, int) Hashtbl.t = Hashtbl.create 42 in
  (* Find a new fresh name. NOTE: Assume that we don't have variables named with _ *)
  let rename (v : var) =
    match Hashtbl.find_opt m v with
    | None -> v
    | Some i -> v ^ "_" ^ string_of_int i
  in
  let rec uniqueify_c (c : constraint_) =
    match c with
    | C_Conj (c1, c2) -> C_Conj (uniqueify_c c1, uniqueify_c c2)
    | C_Implication (v, s, p, c) ->
        (* update the number of times we've seen v *)
        let i = match Hashtbl.find_opt m v with None -> 0 | Some i -> i + 1 in
        Hashtbl.replace m v i;
        let v' = rename v in
        (* Substitute v' for v in both predicate and constraint *)
        let p' = substitute_pred p v v' in
        let c' = substitute_constraint c v v' in
        (v', s, p') ==> uniqueify_c c'
    | _ -> c
  in
  uniqueify_c c

let rec collect_fv_p (p : pred) : var list =
  match p with
  | P_True | P_False | P_Int _ -> []
  | P_Var v -> [ v ]
  | P_Op (_, p1, p2) -> collect_fv_p p1 @ collect_fv_p p2
  | P_Disj (p1, p2) -> collect_fv_p p1 @ collect_fv_p p2
  | P_Conj (p1, p2) -> collect_fv_p p1 @ collect_fv_p p2
  | P_Neg p' -> collect_fv_p p'
  | P_FunApp (_, args) -> List.concat_map collect_fv_p args

let rec collect_fv_c (c : constraint_) : var list =
  match c with
  | C_Conj (c1, c2) -> collect_fv_c c1 @ collect_fv_c c2
  | C_Pred p -> collect_fv_p p
  | C_Implication (v, _, p, c') ->
      List.filter (fun x -> x <> v) (collect_fv_p p @ collect_fv_c c')

let occurs_free_p (v : var) (p : pred) : bool = List.mem v (collect_fv_p p)

let occurs_free_c (v : var) (c : constraint_) : bool =
  List.mem v (collect_fv_c c)
