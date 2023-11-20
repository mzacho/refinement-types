[@@@coverage exclude_file]

type 'a start = Program : Ast.program start | Type : Ast.ty start

let parse' name lexbuf start =
  lexbuf.Lexing.lex_curr_p <-
    { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = name };
  try start Lexer.token lexbuf
  with Error.Syntax (region, s) ->
    let region' =
      if region <> Source.no_region then region
      else
        {
          Source.left = Lexer.convert_pos lexbuf.Lexing.lex_start_p;
          Source.right = Lexer.convert_pos lexbuf.Lexing.lex_curr_p;
        }
    in
    raise (Error.Syntax (region', s))

let parse (type a) name lexbuf : a start -> a = function
  | Program -> parse' name lexbuf Parser.program1
  | Type -> parse' name lexbuf Parser.ty1

let string_to_program s : Ast.program =
  let lexbuf = Lexing.from_string s in
  parse "string" lexbuf Program

let string_to_type s : Ast.ty =
  let lexbuf = Lexing.from_string s in
  parse "string" lexbuf Type
