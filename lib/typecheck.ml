open Pp
module A = Ast
module L = Logic

type env = E_Empty | E_Cons of (A.var * A.ty * env)

(* notation *)
let ( >: ) (v, t) g = E_Cons (v, t, g)
let ( ==> ) x p = L.( ==> ) x p

let base_env =
  ("add", Parse.string_to_type "x:int{v:True}->y:int{v:True}->int{z:z=(x+y)}")
  >: (( "sub",
        Parse.string_to_type "x:int{v:True}->y:int{v:True}->int{z:z=(x-y)}" )
     >: E_Empty)

exception Invalid_arrow_type of string
exception Synthesis_error of string
exception Subtyping_error of string

let debug = ref false

let rec lookup (g : env) (v : A.var) : A.ty option =
  match g with
  | E_Empty -> None
  | E_Cons (v', t', g') -> if String.equal v' v then Some t' else lookup g' v

let ty_to_sort (t : A.base_ty) =
  match t with A.B_Int -> L.S_Int | A.B_Bool -> L.S_Bool

let implication (x : A.var) (t : A.ty) (c : L.constraint_) : L.constraint_ =
  match t with
  | A.T_Refined (bt, v, p) -> (x, ty_to_sort bt, L.substitute_pred p v x) ==> c
  | _ -> c

(* Computes t[y := z] in a capture avoiding manner, see RTT 3.1 *)
let rec substitute_type (t : A.ty) (y : A.var) (z : A.var) : A.ty =
  match t with
  | T_Refined (b, v, p) ->
      if String.equal v y then t else T_Refined (b, v, L.substitute_pred p y z)
  | T_Arrow (v, s, t) ->
      if String.equal v y then T_Arrow (v, substitute_type s y z, t)
      else T_Arrow (v, substitute_type s y z, substitute_type t y z)

let rec sub (s : A.ty) (t : A.ty) : L.constraint_ =
  match s with
  | T_Refined (b, v1, p1) -> (
      match t with
      | T_Refined (b', v2, p2) ->
          if b != b' then
            raise (Subtyping_error "Refined types have different base types")
          else (v1, ty_to_sort b, p1) ==> L.C_Pred (L.substitute_pred p2 v2 v1)
      | T_Arrow _ -> raise (Subtyping_error "Expected refined type"))
  | T_Arrow (x1, s1, t1) -> (
      match t with
      | T_Arrow (x2, s2, t2) ->
          let ci = sub s2 s1 in
          let co = sub (substitute_type t1 x1 x2) t2 in
          L.C_Conj (ci, implication x2 s2 co)
      | T_Refined _ -> raise (Subtyping_error "Expected arrow type"))

(* selfification, see Section 4 *)
let self (v : A.var) (t : A.ty) : A.ty =
  match t with
  | T_Refined (b, v', p) ->
      T_Refined (b, v', L.P_Conj (p, L.P_Op (O_Eq, P_Var v, P_Var v')))
  | T_Arrow _ -> t

let fresh_var (g : env) : A.var =
  let rec fresh_var' (suffix_candidate : int) =
    let var_cand = "fr" ^ Printf.sprintf "%d" suffix_candidate in
    match lookup g var_cand with
    | None -> var_cand
    | Some _ -> fresh_var' (suffix_candidate + 1)
  in
  fresh_var' 0

(* see ENT-EXT *)
let rec close (g : env) (c : L.constraint_) : L.constraint_ =
  match g with
  | E_Cons (x, (T_Refined _ as t), g') ->
      let c' = close g' c in
      if L.occurs_free_c x c then implication x t c' else c'
  | _ -> c

let rec check' (g : env) (e : A.expr) (ty : A.ty) : L.constraint_ =
  (* returned constraints are not necessarily closed *)
  let _ =
    if !debug then (
      print "check'";
      dbg @@ pp_expr e;
      dbg @@ pp_ty ty)
  in
  match e with
  | E_Let (x, e1, e2) ->
      let c1, t1 = synth g e1 in
      let c2 = check' ((x, t1) >: g) e2 ty in
      L.C_Conj (c1, implication x t1 c2)
  | E_RLet (x, e1, t1, e2) ->
      let g1 = (x, t1) >: g in
      (* NOTE: Fig. 4.5 in RTT has a typo, e1 should be checked againts t1, see fig. 4.2 *)
      let c1 = check g1 e1 t1 in
      let c2 = check g1 e2 ty in
      L.C_Conj (c1, c2)
  | E_Abs (x, e) -> (
      match ty with
      | A.T_Arrow (_, s, t) ->
          let c = check' ((x, s) >: g) e t in
          implication x s c
      | _ -> raise (Invalid_arrow_type "Expected arrow type on E_Abs"))
  | E_If (x, e1, e2) ->
      let y = fresh_var g in
      let c0 = check' g (A.E_Var x) (T_Refined (B_Bool, "b", L.P_True)) in
      let yt1 = A.T_Refined (B_Int, y, L.P_Var x) in
      let c1 = check' ((y, yt1) >: g) e1 ty in
      let yt2 = A.T_Refined (B_Int, y, L.P_Neg (L.P_Var x)) in
      let c2 = check' ((y, yt2) >: g) e2 ty in
      L.C_Conj (c0, L.C_Conj (implication y yt1 c1, implication y yt2 c2))
  | e ->
      let c, s = synth g e in
      let c' = sub s ty in
      L.C_Conj (c, c')

and synth (g : env) (e : A.expr) : L.constraint_ * A.ty =
  let _ =
    if !debug then (
      print "synth";
      dbg @@ pp_expr e)
  in
  match e with
  | E_Const c ->
      let t =
        A.T_Refined (A.B_Int, "v", L.P_Op (L.O_Eq, L.P_Var "v", L.P_Int c))
      in
      (L.C_Pred L.P_True, t)
  | E_True ->
      let t = A.T_Refined (A.B_Bool, "v", L.P_Var "v") in
      (L.C_Pred L.P_True, t)
  | E_False ->
      let t = A.T_Refined (A.B_Bool, "v", P_Neg (L.P_Var "v")) in
      (L.C_Pred L.P_True, t)
  | E_Var v -> (
      match lookup g v with
      | Some t -> (L.C_Pred L.P_True, self v t)
      | None ->
          raise
            (Synthesis_error
               ("Could not lookup var '" ^ pp_program e ^ "' in type env")))
  | E_App (e, y) -> (
      match synth g e with
      | c, T_Arrow (x, s, t) ->
          let c' = check' g (A.E_Var y) s in
          (L.C_Conj (c, c'), substitute_type t x y)
      | _, T_Refined _ ->
          raise (Synthesis_error "Expected exp to synthesize to arrow type"))
  | E_Ann (e, t) -> (check' g e t, t)
  | _ ->
      raise
        (Synthesis_error ("Could not synthesize expression: " ^ pp_program e))

and check (g : env) (e : A.expr) (ty : A.ty) : L.constraint_ =
  (* returned constraints are closed *)
  close g (check' g e ty)
