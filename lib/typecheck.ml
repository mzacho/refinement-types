type env = E_Empty | E_Cons of (Ast.var * Ast.ty * env)

let rec lookup (g : env) (v : Ast.var) : Ast.ty option =
  match g with
  | E_Empty -> None
  | E_Cons (v', t', g') -> if v' == v then Some t' else lookup g' v

let check (g : env) (e : Ast.expr) (ty : Ast.ty) : Logic.constraint_ =
  match e with
  | E_Let (x, e1, e2) ->
      let (c1, t1) = synth g e1 in
      let c2 = check (E_Cons (x, t1, g)) e2 ty in

  | E_Abs (v, e') ->
  | _ ->

let synth (g : env) (e : Ast.expr) : Logic.constraint_ * Ast.ty =
  let _ = g in
  let _ = e in
  (Logic.C_Pred Logic.P_True, Ast.T_Refined (Ast.B_Int, "x", Logic.P_True))
