module M = Atlp2023

let _ =
  (* let ast = M.Parse.string_to_program "(fn () 0)" in *)
  let ast = M.Parse.string_to_program "0" in
  let ty = M.Parse.string_to_type "int{v: True}" in
  let gamma = M.Typecheck.E_Empty in
  let cs = M.Typecheck.check gamma ast ty in
  Solver.check cs
