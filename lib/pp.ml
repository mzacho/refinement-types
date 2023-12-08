[@@@coverage exclude_file]

open Ast
open Logic

let int i = PPrint.string @@ Printf.sprintf "%d" i
let str s = PPrint.string s
let nl = PPrint.hardline
let nest = PPrint.nest 2
let ( ^^ ) = PPrint.( ^^ )

let pp_op (o : op) : PPrint.document =
  match o with
  | O_Add -> str "+"
  | O_Sub -> str "-"
  | O_Mul -> str "*"
  | O_Eq -> str "="
  | O_Lt -> str "<"
  | O_Le -> str "<="
  | O_Gt -> str ">"
  | O_Ge -> str ">="

let rec pp_pred (p : pred) : PPrint.document =
  match p with
  | P_Var v -> str v
  | P_True -> str "True"
  | P_False -> str "False"
  | P_Int i -> int i
  | P_Op (op, p, p') -> pp_pred p ^^ pp_op op ^^ pp_pred p'
  | P_Disj (p, p') -> str "(" ^^ pp_pred p ^^ str " ∨ " ^^ pp_pred p' ^^ str ")"
  | P_Conj (p, p') -> str "(" ^^ pp_pred p ^^ str " ∧ " ^^ pp_pred p' ^^ str ")"
  | P_Neg p -> str "¬" ^^ pp_pred p
  | P_FunApp (f, args) ->
      str f ^^ str "(" ^^ PPrint.separate_map (str ", ") pp_pred args ^^ str ")"

let pp_sort (s : sort) : PPrint.document =
  match s with S_Int -> str "ℤ" | S_Bool -> str "𝔹" | S_TyCtor tc -> str tc

let rec pp_constraint (c : constraint_) : PPrint.document =
  match c with
  | C_Pred p -> pp_pred p
  | C_Conj (c1, c2) -> pp_constraint c1 ^^ str " ∧ " ^^ nl ^^ pp_constraint c2
  | C_Implication (v, s, p, c) ->
      str "(∀" ^^ str v ^^ str ":" ^^ pp_sort s ^^ str ". " ^^ pp_pred p
      ^^ str " ⇒ " ^^ nl
      ^^ nest (pp_constraint c)
      ^^ str ")"

let rec pp_ty (t : ty) : PPrint.document =
  match t with
  | T_Refined (t, v, p) ->
      let base_ty =
        match t with
        | B_Int -> str "int"
        | B_Bool -> str "bool"
        | B_TyCtor tc -> str tc
      in
      base_ty ^^ str "{" ^^ str v ^^ str ":" ^^ pp_pred p ^^ str "}"
  | T_Arrow (v, t, t') -> str v ^^ str ":" ^^ pp_ty t ^^ str "->" ^^ pp_ty t'

let rec pp_metric (m : metric) : PPrint.document =
  match m with
  | [] -> str ""
  | p :: [] -> pp_pred p
  | p :: m' -> pp_pred p ^^ str ", " ^^ pp_metric m'

let pp_env (g : (var * ty) list) : PPrint.document =
  let rec aux g =
    match g with
    | [] -> str ""
    | [ (x, t) ] -> str x ^^ str ":" ^^ pp_ty t
    | (x, t) :: g' -> str x ^^ str ":" ^^ pp_ty t ^^ str ", " ^^ aux g'
  in
  str "[" ^^ aux g ^^ str "]"

let rec pp_expr' (e : expr) : PPrint.document =
  match e with
  | E_Const n -> int n
  | E_Var v -> str v
  | E_Abs (v, e) -> str "(fn " ^^ str v ^^ str ": " ^^ pp_expr' e ^^ str ")"
  | E_App (e, v) -> pp_expr' e ^^ str " " ^^ str v
  | E_Let (v, e1, e2) ->
      str "let " ^^ str v ^^ str " = " ^^ pp_expr' e1 ^^ str " in "
      ^^ pp_expr' e2
  | E_RLet (v, e1, t, m, e2) ->
      str "let rec " ^^ str v ^^ str " = " ^^ pp_expr' e1 ^^ str " : "
      ^^ pp_ty t ^^ str " / " ^^ pp_metric m ^^ str " in " ^^ pp_expr' e2
  | E_Ann (e, t) -> pp_expr' e ^^ str ":" ^^ pp_ty t
  | E_True -> str "true"
  | E_False -> str "false"
  | E_If (v, then_br, else_br) ->
      str "if " ^^ str v ^^ str " then " ^^ pp_expr' then_br ^^ str " else "
      ^^ pp_expr' else_br
  | E_Switch (v, alts) ->
      str ("switch " ^ v ^ " {")
      ^^ PPrint.separate_map (str "| ") pp_alt alts
      ^^ str "}"

and pp_alt (Alt (d, params, e) : alt) : PPrint.document =
  str (d ^ "(" ^ String.concat ", " params ^ ") => ") ^^ pp_expr' e

let dbg d : unit =
  let ch = stdout in
  PPrint.ToChannel.pretty 1.0 100 ch d;
  Printf.fprintf ch "%s\n" "";
  flush_all ()

let print s : unit = Printf.fprintf stdout "%s" s

let rec print_indent indent =
  if indent = 0 then () else print_indent (indent - 1);
  print "." (* (Printf.sprintf " %i " indent) *)

let doc_to_string (doc : PPrint.document) : string =
  let buf = Buffer.create 0 in
  PPrint.ToBuffer.pretty 1.0 100 buf doc;
  Buffer.contents buf

let pp_expr (e : expr) = doc_to_string @@ pp_expr' e
let pp_type (ty : ty) = doc_to_string @@ pp_ty ty
let pp_program (_p : program) = failwith "TODO"
