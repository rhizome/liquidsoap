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
  | FAdd | FSub | FMul | FDiv
  (* | If_then_else *)
  | Call of string

(** An expression. *)
type expr =
  | Let of string * T.t * prog
  | Float of float
  | Ident of string
  | Alloc of (T.t * prog)
  (** [Load p] loads memory pointed by p. *)
  | Load of prog
  (** [Store (p,v)] stores value v in memory pointed by p. *)
  | Store of prog * prog
  | Op of op * prog array

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

  let rec emit_expr e =
    let prog_expr p = match p with [e] -> e | _ -> assert false in
    match e with
      | Let (x,_,[Alloc (t,p)]) ->
        Printf.sprintf "%s %s = malloc(sizeof(%s)); %s = %s" (emit_type (T.Ptr t)) x (emit_type t) x (emit_expr (prog_expr p))
      | Alloc (t,p) ->
        (* TODO *)
        Printf.sprintf "malloc(sizeof(%s))" (emit_type t)
      | Let (x,t,p) -> Printf.sprintf "%s %s = %s" (emit_type t) x (emit_expr (prog_expr p))
      | Float f -> Printf.sprintf "%f" f
      | Ident x -> x
      | Load x -> Printf.sprintf "*%s" (emit_expr (prog_expr x))
      | Store (x,v) -> Printf.sprintf "%s = %s" (emit_expr (prog_expr x)) (emit_expr (prog_expr v))
      | Op (op, args) ->
        let args = Array.map (fun arg -> emit_expr (prog_expr arg)) args in
        (
          match op with
            | FMul ->
              Printf.sprintf "(%s * %s)" args.(0) args.(1)
            | Call f ->
              let args = Array.to_list args in
              let args = String.concat ", " args in
              Printf.sprintf "%s(%s)" f args
        )

  let rec emit_prog ?(return=true) prog =
    let emit_prog ?(return=return) = emit_prog ~return in
    match prog with
      | [] -> if return then "return;" else assert false
      | [e] -> Printf.sprintf "%s%s;" (if return then "return " else "") (emit_expr e)
      | e::ee -> (emit_expr e) ^ "\n" ^ emit_prog ee

  let emit_decl = function
    | Decl (proto, prog) ->
      let name, args, t = proto in
      let args = List.map (fun (x,t) -> Printf.sprintf "%s %s" (emit_type t) x) args in
      let args = String.concat ", " args in
      Printf.sprintf "%s %s(%s) {\n%s\n}\n" (emit_type t) name args (emit_prog prog)

  let emit_decls d = String.concat "\n" (List.map emit_decl d)
end
