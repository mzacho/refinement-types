module M = Atlp2023

let _ =
  let _ = M.Parse.string_to_program "(fn () 0)" in ()
  (* Ast.pp ast ; print_newline(); flush stdout *)
