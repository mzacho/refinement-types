module M = Atlp2023
open M.Logic

(****** EXAMPLE PROGRAMS *******)

(****** CONSTANT 42 *******)
let ex_42_expr = M.Parse.string_to_expr "42"
let ex_42_type = M.Parse.string_to_type "int{v: v=42}"
let ex_42_fs = []
let ex_42_denv = []
let ex_42_gamma = M.Typecheck.E_Empty

(****** ACKERMANN *******)
let ack_expr =
  M.Parse.string_to_expr
    {|
        let zero = 0 in let one = 1 in
        let rec ack =
        (fn m. (fn n.
          let b = (eq m) zero in
          if b then (add n) one
          else let newm = (sub m) one in
               let b = (eq n) zero in
               if b then (ack newm) one
               else let newn = (sub n) one in
                    let ackres = (ack m) newn in
                    (ack newm) ackres))
        : m:int{v:v>=0} -> n:int{v:v>=0} -> int{v:v>=0} / m, n
        in
        let x = 42 in
        let y = 1337 in (ack x) y
    |}

let ack_type = M.Parse.string_to_type "int{v: v>=0}"
let ack_fs = []
let ack_denv = []
let ack_gamma = M.Typecheck.base_env

(****** LOOP *******)
let loop_expr =
  M.Parse.string_to_expr
    {|
    let rec f =
      (fn n. f n) : n:int{v: True} -> int{v:True} / n
    in 42
  |}

let loop_type = M.Parse.string_to_type "int{v: True}"
let loop_fs = []
let loop_denv = []
let loop_gamma = M.Typecheck.E_Empty

(****** LIST DATATYPES *******)
let list_sort = S_TyCtor "list"

let len : uninterp_fun =
  ( "len",
    [ list_sort ],
    S_Int,
    Some
      (("l", list_sort, P_Op (O_Le, P_Int 0, P_FunApp ("len", [ P_Var "l" ])))
      ==> C_Pred P_True) )

let list_tc =
  M.Parse.string_to_ty_ctor
    {|
type list =
  | Nil => {v: len(v) = 0 }
  | Cons(x:int{v: True}, xs:list{v: True}) => {v: len(v) = 1 + len(xs)}.
     |}

let list_data_env = M.Typecheck.build_data_env [ list_tc ]

(****** LENGTH REFLECT LEN *******)
let length_expr =
  M.Parse.string_to_expr
    {|
      let rec length =
         (fn xs.
             switch xs {
             | Cons(hd, tl) => let lengthtail = length tl in
                               let one = 1 in
                               add lengthtail one
             | Nil => 0
             }
          ) : xs:list{v: True} -> int{v: v = len(xs)} / len(xs) in
      length
    |}

let length_type =
  M.Parse.string_to_type "xs:list{v: True} -> int{v: v = len(xs)}"

let length_fs = [ len ]
let length_denv = list_data_env
let length_gamma = M.Typecheck.base_env

(****** APPEND *******)
let append_expr =
  M.Parse.string_to_expr
    {|
             let rec append =
             (fn xs.
               (fn ys.
                 switch xs {
                 | Nil => ys
                 | Cons(hd, tl) => let apptl = append tl ys in Cons hd apptl
                 }
               )
             ) : xs:list{v: True} -> ys:list{v: True} -> list{v: len(v) = len(xs) + len(ys)} / len(xs)
             in true
      |}

let append_type = M.Parse.string_to_type "bool{v: True}"
let append_fs = [ len ]
let append_denv = list_data_env
let append_gamma = M.Typecheck.base_env

(****** END EXAMPLE PROGRAMS *******)

(****** CMDLINE PARSING *******)

let debug = ref false
let program = ref None

let set_program s =
  Printf.fprintf stdout "Using test program: %s\n" s;
  match s with
  | "42" ->
      program := Some (ex_42_expr, ex_42_type, ex_42_fs, ex_42_denv, ex_42_gamma)
  | "loop" ->
      program := Some (loop_expr, loop_type, loop_fs, loop_denv, loop_gamma)
  | "ackermann" ->
      program := Some (ack_expr, ack_type, ack_fs, ack_denv, ack_gamma)
  | "length" ->
      program :=
        Some (length_expr, length_type, length_fs, length_denv, length_gamma)
  | "append" ->
      program :=
        Some (append_expr, append_type, append_fs, append_denv, append_gamma)
  | _ -> ()

let speclist =
  [
    ("-example", Arg.String set_program, "Use example program <p>");
    ( "-debug",
      Arg.Set debug,
      "Debug: Print constraint and counter example output" );
  ]

let usage_msg =
  {|
=========================================
  HELP
=========================================
  Things you can do:

  - typecheck example programs: make demo-<TAB>

  - compute test coverage: make coverage

=========================================
  EXAMPLE

  ./main.exe -example 42 -debug

=========================================
  The following commands are available:
|}

(****** MAIN *******)
let () =
  print_endline "";
  Arg.parse speclist (fun _ -> ()) usage_msg;

  match !program with
  | None ->
      failwith "No input program given, please specify one e.g. with -example 1"
  | Some (e, ty, fs, denv, g) ->
      let cs = M.Typecheck.check ~denv ~fs g e ty in
      if !debug then
        Printf.fprintf stdout "Generated constraint: \n\n%s\n\n"
          (M.Pp.doc_to_string @@ M.Pp.pp_constraint cs);
      let _ =
        if M.Solver.check ~dbg:false ~fs cs then
          Printf.fprintf stdout "Z3: success! Tautology.\n"
        else Printf.fprintf stdout "Z3: fail! No tautology.\n"
      in
      ()
