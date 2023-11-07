type env =
  | E_Empty
  | E_Cons of (Ast.var * Ast.ty * env)

let check (g: env) (e: Ast.expr) (ty: Ast.ty): Solver.constraint_ =
  let _ = g in let _ = e in let _ = ty in
  Solver.C_Pred Solver.P_True

let synth (g: env) (e: Ast.expr): Solver.constraint_ * Ast.ty =
  let _ = g in let _ = e in
  (Solver.C_Pred Solver.P_True, Ast.T_Refined_base (Ast.B_Int, "x", Solver.P_True))
