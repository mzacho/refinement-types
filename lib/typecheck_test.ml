let%test "Integer identity function typechecks" =
  let e = Parse.string_to_program "(fn x. x)" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "x:int{v: True} -> int{v: True}" in
  Solver.check (Typecheck.check g e t)

let%test "Fail when trying to check an abstraction against an int" =
  let e = Parse.string_to_program "(fn x. x)" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{v: True}" in
  try Solver.check (Typecheck.check g e t)
  with Typecheck.Invalid_arrow_type _ -> true

let%test "Integer constant 0 checks" =
  let e = Parse.string_to_program "0" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{v: False}" in
  not (Solver.check (Typecheck.check g e t))
