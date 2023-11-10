type env = E_Empty | E_Cons of (Ast.var * Ast.ty * env)

let check (g : env) (e : Ast.expr) (ty : Ast.ty) : Logic.constraint_ =
  let _ = g in
  let _ = e in
  let _ = ty in
  Logic.C_Pred Logic.P_True

let synth (g : env) (e : Ast.expr) : Logic.constraint_ * Ast.ty =
  let _ = g in
  let _ = e in
  (Logic.C_Pred Logic.P_True, Ast.T_Refined (Ast.B_Int, "x", Logic.P_True))
