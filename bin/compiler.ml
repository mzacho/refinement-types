module M = Atlp2023

let _ =
  let ast = M.Parse.string_to_program "x" in
  let ty = M.Parse.string_to_type "int{x: False}" in
  let gamma = M.Typecheck.E_Empty in
  let cs = M.Typecheck.check gamma ast ty in
  M.Solver.check cs
