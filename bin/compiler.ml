module M = Atlp2023

let _ =
  let e = M.Parse.string_to_expr "x" in
  let ty = M.Parse.string_to_type "int{x: False}" in
  let gamma = M.Typecheck.E_Empty in
  let cs = M.Typecheck.check gamma e ty in
  M.Solver.check cs
