module M = Atlp2023

(****** EXAMPLE PROGRAMS *******)

let ex_4_expr = M.Parse.string_to_expr "4"
let ex_4_type = M.Parse.string_to_type "int{v: v=4}"
let ex_4_gamma = M.Typecheck.E_Empty

(****** END EXAMPLE PROGRAMS *******)

(****** CMDLINE PARSING *******)

let debug = ref false
let program = ref None

let set_program s =
  Printf.fprintf stdout "Using test program: %s\n" s;
  match s with
  | "4" -> program := Some (ex_4_expr, ex_4_type, ex_4_gamma)
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
  Things you can do at the moment:

  - typecheck example program

=========================================
  EXAMPLE

  ./main.exe -example funapp -debug

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
  | Some (e, ty, g) ->
      let cs = M.Typecheck.check g e ty in
      if !debug then
        Printf.fprintf stdout "Generated constraint: \n\n%s\n\n"
          (M.Pp.doc_to_string @@ M.Pp.pp_constraint cs);
      let _ =
        if M.Solver.check ~dbg:false cs then
          Printf.fprintf stdout "Z3: success! Tautology.\n"
        else Printf.fprintf stdout "Z3: fail! No tautology.\n"
      in
      ()
