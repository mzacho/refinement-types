open Pp

type env = E_Empty | E_Cons of (Ast.var * Ast.ty * env)

(* notation *)
let ( >: ) g (v,t) = E_Cons (v, t, g)

exception Invalid_arrow_type of string
exception Synthesis_error of string
exception Subtyping_error of string


let rec lookup (g : env) (v : Ast.var) : Ast.ty option =
  match g with
  | E_Empty -> None
  | E_Cons (v', t', g') -> if String.equal v' v then Some t' else lookup g' v

let ty_to_sort (t : Ast.base_ty) = match t with Ast.B_Int -> Logic.S_Int

let implication (x : Ast.var) (t : Ast.ty) (c : Logic.constraint_) :
    Logic.constraint_ =
  match t with
  | Ast.T_Refined (bt, v, p) ->
      Logic.C_Implication (x, ty_to_sort bt, Logic.substitute_pred p v x, c)
  | _ -> c

(* Computes t[y := z] in a capture avoiding manner, see RTT 3.1 *)
let rec substitute_type (t: Ast.ty) (y: Ast.var) (z: Ast.var) : Ast.ty =
  match t with
  | T_Refined (b, v, p) ->
     if String.equal v y
     then t
     else T_Refined (b, v, Logic.substitute_pred p y z)
  | T_Arrow (v, s, t) ->
     if String.equal v y
     then T_Arrow (v, substitute_type s y z, t)
     else T_Arrow (v, substitute_type s y z, substitute_type t y z)

let rec sub (s : Ast.ty) (t : Ast.ty) =
  match s with
  | T_Refined (b, v1, p1) -> (
    match t with
    | T_Refined (b', v2, p2) -> (
      if b != b'
      then raise (Subtyping_error "Refined types have different base types")
      else
        Logic.C_Implication (v1, Logic.S_Int, p1, Logic.C_Pred (Logic.substitute_pred p2 v2 v1))

    )
    | T_Arrow _ -> raise (Subtyping_error "Expected refined type")
  )
  | T_Arrow (x1, s1, t1) -> (
    match t with
    | T_Arrow (x2, s2, t2) ->
       let ci = sub s2 s1 in
       let co = sub (substitute_type t1 x1 x2) t2 in
       Logic.C_Conj (ci, implication x2 s2 co)


    | T_Refined _ -> raise (Subtyping_error "Expected arrow type")
  )

let rec check (g : env) (e : Ast.expr) (ty : Ast.ty) : Logic.constraint_ =
  match e with
  | E_Let (x, e1, e2) ->
      let c1, t1 = synth g e1 in
      let c2 = check (g >: (x, t1)) e2 ty in
      Logic.C_Conj (c1, implication x t1 c2)
  | E_Abs (x, e) -> (
      match ty with
      | Ast.T_Arrow (_, s, t) ->
          let c = check (g >: (x, s)) e t in
          implication x s c
      | _ -> raise (Invalid_arrow_type "Expected arrow type on E_Abs"))
  | e ->
      let c, s = synth g e in
      let c' = sub s ty in
      Logic.C_Conj (c, c')

and synth (g : env) (e : Ast.expr) : Logic.constraint_ * Ast.ty =
  match e with
  | E_Const c ->
     let t = Ast.T_Refined (Ast.B_Int, "v", Logic.P_Op (Logic.O_Eq, Logic.P_Var "v", Logic.P_Int c)) in
     (Logic.C_Pred Logic.P_True, t)
  | E_Var v -> (
    match lookup g v with
    | Some t -> (Logic.C_Pred Logic.P_True, t)
    | None -> raise (Synthesis_error "Could not lookup var in type env")
  )
  | E_App (_,_) -> failwith "not implemented"
  | E_Ann (_,_) -> failwith "not implemented"
  | _ -> raise (Synthesis_error ("Could not synthesize expression" ^ pp_program e))
