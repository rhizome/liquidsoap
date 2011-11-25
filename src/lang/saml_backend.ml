(** AST for the backend before code emission. We should keep this as close as
    LLVM's representation as possible. *)

(** Raised by "Liquidsoap" implementations of functions when no reduction is
    possible. *)
exception Cannot_reduce

module T = struct
  (** A type. *)
  type t =
    | Float
    | Ptr of t
    | Struct of (string * t) list
end

(** An operation. *)
type op =
  (** [Load p] loads memory pointed by p. *)
  | Load
  (** [Store (p,v)] stores value v in memory pointed by p. *)
  | Store
  | FAdd | FSub | FMul | FDiv
  (* | If_then_else *)

(** An expression. *)
type expr =
  | Float of float
  | Ident of string
  | Op of op * prog array
  | Sizeof of T.t

(** A program. *)
and prog = expr list

(** A function declaration. *)
and decl =
  | Decl of proto * prog
  | External of proto

(** Prototype of a function: name, typed arguments and return type. *)
and proto = string * (string * T.t) list * T.t

(** Emit C code. *)
module Emitter_C = struct
  let rec emit_type = function
    | T.Float -> "float"
    | T.Struct s ->
      let s = List.map (fun (x,t) -> Printf.sprintf "%s %s;" (emit_type t) x) s in
      let s = String.concat " " s in
      Printf.sprintf "struct { %s }" s
    | T.Ptr t -> Printf.sprintf "%s*" (emit_type t)

  let emit_expr = function
    | Float f -> Printf.sprintf "%f" f
    | Ident x -> x

  let rec emit_prog prog =
    match prog with
      | [] -> "return;"
      | [e] -> Printf.sprintf "return %s;" (emit_expr e)
      | e::ee -> (emit_expr e) ^ "\n" ^ emit_prog ee

  let emit_decl = function
    | Decl (proto, prog) ->
      let name, args, t = proto in
      let args = List.map (fun (x,t) -> Printf.sprintf "%s %s" (emit_type t) x) args in
      let args = String.concat ", " args in
      Printf.sprintf "%s %s(%s) {\n%s\n}\n" (emit_type t) name args (emit_prog prog)

  let emit_decls d = String.concat "\n" (List.map emit_decl d)
end
