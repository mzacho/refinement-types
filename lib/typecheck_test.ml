(* open Pp *)

(* Subtyping tests *)
let%test "Fail subtyping: int <: (int -> int)" =
  let t = Parse.string_to_type "int{v: False}" in
  let t' = Parse.string_to_type "x:int{v: True} -> int{v: True}" in
  try Solver.check (Typecheck.sub t t')
  with Typecheck.Subtyping_error _ -> true

let%test "Fail subtyping: int :> (int -> int)" =
  let t' = Parse.string_to_type "int{v: True}" in
  let t = Parse.string_to_type "x:int{v: True} -> int{v: True}" in
  try Solver.check (Typecheck.sub t t')
  with Typecheck.Subtyping_error _ -> true

let%test "Successfull subtyping: (int -> int) <: (int -> int)" =
  let t = Parse.string_to_type "x:int{v: True} -> int{v: True}" in
  Solver.check (Typecheck.sub t t)

let%test "Fail subtyping: int :> bool)" =
  let t' = Parse.string_to_type "bool{v: True}" in
  let t = Parse.string_to_type "int{v: True}" in
  try Solver.check (Typecheck.sub t t')
  with Typecheck.Subtyping_error _ -> true

(* Type checking tests *)
let%test "Integer identity function typechecks" =
  let e = Parse.string_to_program "(fn x. x)" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "x:int{v: True} -> int{v: True}" in
  let c = Typecheck.check g e t in
  (* dbg @@ pp_constraint c; *)
  Solver.check c

let%test "Fail when trying to check an abstraction against an int" =
  let e = Parse.string_to_program "(fn x. x)" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{v: True}" in
  try Solver.check (Typecheck.check g e t)
  with Typecheck.Invalid_arrow_type _ -> true

let%test "Constant 0 checks" =
  let e = Parse.string_to_program "0" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{v: False}" in
  not (Solver.check (Typecheck.check g e t))

let%test "Constant 0 refined precicely" =
  let e = Parse.string_to_program "0" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{v: v = 0}" in
  Solver.check (Typecheck.check g e t)

let%test "Constant 5 refined gt 4" =
  let e = Parse.string_to_program "5" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{v: v > 4}" in
  Solver.check (Typecheck.check g e t)

let%test "Constant 5 refined lt 10" =
  let e = Parse.string_to_program "5" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{v: v < 10}" in
  Solver.check (Typecheck.check g e t)

let%test "Var checks with same type as in environment" =
  let e = Parse.string_to_program "y" in
  let t = Parse.string_to_type "int{v: True}" in
  let g = Typecheck.E_Cons ("y", t, Typecheck.E_Empty) in
  Solver.check (Typecheck.check g e t)

let%test "Var checks with subtype of type in environment" =
  let e = Parse.string_to_program "x" in
  let s = Parse.string_to_type "int{v: v = 42}" in
  let g = Typecheck.E_Cons ("x", s, Typecheck.E_Empty) in
  let t = Parse.string_to_type "int{v: True}" in
  Solver.check (Typecheck.check g e t)

let%test "Var doesn't check with supertype of type in environment" =
  let e = Parse.string_to_program "x" in
  let s = Parse.string_to_type "int{v: True}" in
  let g = Typecheck.E_Cons ("x", s, Typecheck.E_Empty) in
  let t = Parse.string_to_type "int{v: v = 42}" in
  not (Solver.check (Typecheck.check g e t))

let%test "Fun app without annotation doesn't check" =
  let e = Parse.string_to_program "(fn x. x) x" in
  let t = Parse.string_to_type "int{v: 42}" in
  let g = Typecheck.E_Cons ("x", t, Typecheck.E_Empty) in
  try Solver.check (Typecheck.check g e t)
  with Typecheck.Synthesis_error _ -> true

let%test "Fun app first exp not a function type" =
  let e = Parse.string_to_program "x x" in
  let t = Parse.string_to_type "int{v: 42}" in
  let g = Typecheck.E_Cons ("x", t, Typecheck.E_Empty) in
  try Solver.check (Typecheck.check g e t)
  with Typecheck.Synthesis_error _ -> true

let%test "Var not in Γ doesnt check" =
  let e = Parse.string_to_program "y" in
  let t = Parse.string_to_type "int{v: True}" in
  let g = Typecheck.E_Cons ("x", t, Typecheck.E_Empty) in
  try Solver.check (Typecheck.check g e t)
  with Typecheck.Synthesis_error _ -> true

let%test "Fun app with annotation checks" =
  let e =
    Parse.string_to_program "(fn x. x):y:int{v: True} -> int{v: True} z"
  in
  let t = Parse.string_to_type "int{v: v = 42}" in
  let t' = Parse.string_to_type "int{v: True}" in
  let g = Typecheck.E_Cons ("z", t, Typecheck.E_Empty) in
  Solver.check (Typecheck.check g e t')

let%test "Let exp checks (int)" =
  let e = Parse.string_to_program "let x = 42 in x" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{z: z <= 42}" in
  Solver.check (Typecheck.check g e t)

let%test "Let exp checks (bool)" =
  let e = Parse.string_to_program "let x = true in (let y = false in x)" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "bool{z: z}" in
  Solver.check (Typecheck.check g e t)

let%test "42 + 10 checks with precice refined type" =
  let e = Parse.string_to_program "let x = 42 in let y = 10 in add x y" in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{z: z = 52}" in
  Solver.check (Typecheck.check g e t)

let%test "If-then-else checks (with path-dependency)" =
  let e = Parse.string_to_program "let x = true in (if x then 1 else 0)" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{n: n = 1}" in
  let c = Typecheck.check g e t in
  (*  dbg @@ pp_constraint c; *)
  Solver.check c
