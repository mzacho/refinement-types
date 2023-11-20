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

let ty_to_sort (t : A.base_ty) = match t with A.B_Int -> L.S_Int

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
          else (v1, L.S_Int, p1) ==> L.C_Pred (L.substitute_pred p2 v2 v1)
      | T_Arrow _ -> raise (Subtyping_error "Expected refined type"))
  | T_Arrow (x1, s1, t1) -> (
      match t with
      | T_Arrow (x2, s2, t2) ->
          let ci = sub s2 s1 in
          let co = sub (substitute_type t1 x1 x2) t2 in
          L.C_Conj (ci, implication x2 s2 co)
      | T_Refined _ -> raise (Subtyping_error "Expected arrow type"))

let rec check (g : env) (e : A.expr) (ty : A.ty) : L.constraint_ =
  let _ =
    if !debug then (
      print "check";
      dbg @@ pp_expr e;
      dbg @@ pp_ty ty)
  in
  match e with
  | E_Let (x, e1, e2) ->
      let c1, t1 = synth g e1 in
      let c2 = check ((x, t1) >: g) e2 ty in
      L.C_Conj (c1, implication x t1 c2)
  | E_Abs (x, e) -> (
      match ty with
      | A.T_Arrow (_, s, t) ->
          let c = check ((x, s) >: g) e t in
          implication x s c
      | _ -> raise (Invalid_arrow_type "Expected arrow type on E_Abs"))
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
  | E_Var v -> (
      match lookup g v with
      | Some t -> (L.C_Pred L.P_True, t)
      | None -> raise (Synthesis_error "Could not lookup var in type env"))
  | E_App (e, y) -> (
      match synth g e with
      | c, T_Arrow (x, s, t) ->
          let c' = check g (A.E_Var y) s in
          (L.C_Conj (c, c'), substitute_type t x y)
      | _, T_Refined _ ->
          raise (Synthesis_error "Expected exp to synthesize to arrow type"))
  | E_Ann (e, t) -> (check g e t, t)
  | _ ->
      raise
        (Synthesis_error ("Could not synthesize expression: " ^ pp_program e))
