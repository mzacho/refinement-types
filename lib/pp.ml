[@@@coverage exclude_file]

open Ast
open Logic

let int i = PPrint.string @@ Printf.sprintf "%d" i
let str s = PPrint.string s
let ( ^^ ) = PPrint.( ^^ )

let pp_op (o : op) : PPrint.document =
  match o with
  | O_Add -> str "+"
  | O_Sub -> str "-"
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
  | P_Disj (p, p') -> pp_pred p ^^ str " ∨ " ^^ pp_pred p'
  | P_Conj (p, p') -> pp_pred p ^^ str " ∧ " ^^ pp_pred p'
  | P_Neg p -> str "~" ^^ pp_pred p

let pp_sort (s : sort) : PPrint.document =
  match s with S_Int -> str "ℤ" | S_Bool -> str "𝔹"

let rec pp_constraint (c : constraint_) : PPrint.document =
  match c with
  | C_Pred p -> pp_pred p
  | C_Conj (c1, c2) ->
      str "(" ^^ pp_constraint c1 ^^ str " ∧ " ^^ pp_constraint c2 ^^ str ")"
  | C_Implication (v, s, p, c) ->
      str "∀" ^^ str v ^^ str ": " ^^ pp_sort s ^^ str ". " ^^ pp_pred p
      ^^ str " ⇒ " ^^ pp_constraint c

let rec pp_ty (t : ty) : PPrint.document =
  match t with
  | T_Refined (t, v, p) ->
      let base_ty = match t with B_Int -> str "int" | B_Bool -> str "bool" in
      base_ty ^^ str "{" ^^ str v ^^ str ":" ^^ pp_pred p ^^ str "}"
  | T_Arrow (v, t, t') -> str v ^^ str ":" ^^ pp_ty t ^^ str "->" ^^ pp_ty t'

let rec pp_expr (ast : program) : PPrint.document =
  match ast with
  | E_Const n -> int n
  | E_Var v -> str v
  | E_Abs (v, e) -> str "(fn " ^^ str v ^^ str ": " ^^ pp_expr e ^^ str ")"
  | E_App (e, v) -> pp_expr e ^^ str " " ^^ str v
  | E_Let (v, e1, e2) ->
      str "let " ^^ str v ^^ str "." ^^ pp_expr e1 ^^ str "in" ^^ pp_expr e2
  | E_Ann (e, t) -> pp_expr e ^^ str ":" ^^ pp_ty t
  | E_True -> str "true"
  | E_False -> str "false"
  | E_If (v, then_br, else_br) ->
      str "if " ^^ str v ^^ str " then " ^^ pp_expr then_br ^^ str " else "
      ^^ pp_expr else_br

let dbg d : unit =
  let ch = stdout in
  PPrint.ToChannel.pretty 1.0 100 ch d;
  Printf.fprintf ch "%s\n" "";
  flush_all ()

let print s : unit = Printf.fprintf stdout "%s\n" s

let doc_to_string doc : string =
  let buf = Buffer.create 0 in
  PPrint.ToBuffer.pretty 1.0 100 buf doc;
  Buffer.contents buf

let pp_program (ast : program) = doc_to_string @@ pp_expr ast
let pp_type (ty : ty) = doc_to_string @@ pp_ty ty
