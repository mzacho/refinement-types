[@@@coverage exclude_file]

type 'a start =
  | Program : Ast.program start
  | Expression : Ast.expr start
  | Type : Ast.ty start
  | TyCtor : Ast.ty_ctor_decl start

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
  | Expression -> parse' name lexbuf Parser.expr1
  | Type -> parse' name lexbuf Parser.ty1
  | TyCtor -> parse' name lexbuf Parser.ty_ctor1

let string_to_ty_ctor s : Ast.ty_ctor_decl =
  let lexbuf = Lexing.from_string s in
  parse "string" lexbuf TyCtor

let string_to_expr s : Ast.expr =
  let lexbuf = Lexing.from_string s in
  parse "string" lexbuf Expression

let string_to_type s : Ast.ty =
  let lexbuf = Lexing.from_string s in
  parse "string" lexbuf Type

let string_to_program s : Ast.program =
  let lexbuf = Lexing.from_string s in
  parse "string" lexbuf Program
