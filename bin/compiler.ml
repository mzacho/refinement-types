module M = Atlp2023

let _ =
  try
    let lexbuf = Lexing.from_channel stdin in
    while true do
      let result = M.Parser.main M.Lexer.token lexbuf in
      print_int result; print_newline(); flush stdout
    done
  with M.Lexer.Eof ->
    exit 0
