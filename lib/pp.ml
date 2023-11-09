open Ast
open Logic

let int i = PPrint.string @@ Printf.sprintf "%d" i
let str s = PPrint.string s
let ( ^^ ) = PPrint.( ^^ )

let pp_op (o : op) : PPrint.document =
  match o with
  | O_add -> str "+"
  | O_Eq -> str "="
  | O_Lt -> str "<"
  | O_Le -> str "<="

let rec pp_pred (p : pred) : PPrint.document =
  match p with
  | P_Var v -> str v
  | P_True -> str "True"
  | P_False -> str "False"
  | P_Int i -> int i
  | P_Op (op, p, p') -> pp_pred p ^^ pp_op op ^^ pp_pred p'
  | P_Disj (p, p') -> pp_pred p ^^ str "\\/" ^^ pp_pred p'
  | P_Conj (p, p') -> pp_pred p ^^ str "/\\" ^^ pp_pred p'
  | P_Neg p -> str "~" ^^ pp_pred p

let rec pp_ty (t : ty) : PPrint.document =
  match t with
  | T_Refined (t, v, p) -> (
      match t with
      | B_Int -> str "int{" ^^ str v ^^ str ":" ^^ pp_pred p ^^ str "}")
  | T_Arrow (v, t, t') -> str v ^^ pp_ty t ^^ str "->" ^^ pp_ty t'

let rec pp_expr (ast : program) : PPrint.document =
  match ast with
  | E_Const n -> int n
  | E_Var v -> str v
  | E_Abs (v, e) -> str v ^^ pp_expr e
  | E_App (e, v) -> pp_expr e ^^ str v
  | E_Let (v, e1, e2) ->
      str "let " ^^ str v ^^ str "." ^^ pp_expr e1 ^^ str "in" ^^ pp_expr e2
  | E_Ann (e, t) -> pp_expr e ^^ str ":" ^^ pp_ty t

(* let print name d: unit = *)
(*   let ch = stdout in *)
(*   Printf.fprintf ch "%s:\n" name; *)
(*   PPrint.ToChannel.pretty 1.0 100 ch d; *)
(*   Printf.fprintf ch "%s\n" ""; *)
(*   flush_all () *)

let print doc : string =
  let buf = Buffer.create 0 in
  PPrint.ToBuffer.pretty 1.0 100 buf doc;
  Buffer.contents buf

let pp_program (ast : program) = print @@ pp_expr ast
let pp_type (ty : ty) = print @@ pp_ty ty
