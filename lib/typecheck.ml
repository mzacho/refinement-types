type env = E_Empty | E_Cons of (Ast.var * Ast.ty * env)

exception Invalid_arrow_type of string

let rec lookup (g : env) (v : Ast.var) : Ast.ty option =
  match g with
  | E_Empty -> None
  | E_Cons (v', t', g') -> if v' == v then Some t' else lookup g' v

let ty_to_sort (t : Ast.base_ty) = match t with Ast.B_Int -> Logic.S_Int

let implication (x : Ast.var) (t : Ast.ty) (c : Logic.constraint_) :
    Logic.constraint_ =
  match t with
  | Ast.T_Refined (bt, v, p) ->
      Logic.C_Implication (x, ty_to_sort bt, Logic.substitute_pred p v x, c)
  | _ -> c

let sub (s : Ast.ty) (t : Ast.ty) =
  let _ = s in
  let _ = t in
  Logic.C_Pred Logic.P_True

let rec check (g : env) (e : Ast.expr) (ty : Ast.ty) : Logic.constraint_ =
  match e with
  | E_Let (x, e1, e2) ->
      let c1, t1 = synth g e1 in
      let c2 = check (E_Cons (x, t1, g)) e2 ty in
      Logic.C_Conj (c1, implication x t1 c2)
  | E_Abs (_, e) -> (
      match ty with
      | Ast.T_Arrow (x, s, t) ->
          let c = check (E_Cons (x, s, g)) e t in
          implication x s c
      | _ -> raise (Invalid_arrow_type "Expected arrow type on E_Abs"))
  | e ->
      let c, s = synth g e in
      let c' = sub s ty in
      Logic.C_Conj (c, c')

and synth (g : env) (e : Ast.expr) : Logic.constraint_ * Ast.ty =
  let _ = g in
  let _ = e in
  (Logic.C_Pred Logic.P_True, Ast.T_Refined (Ast.B_Int, "x", Logic.P_True))
