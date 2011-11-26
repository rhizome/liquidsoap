(** AST for the backend before code emission. We should keep this as close as
    LLVM's representation as possible. *)

(** Raised by "Liquidsoap" implementations of functions when no reduction is
    possible. *)
exception Cannot_reduce

module T = struct
  (** A type. *)
  type t =
    | Void
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
  | Let of string * prog
  | Float of float
  | Ident of string
  | Alloc of T.t
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
  module Env = struct
    type t =
        {
          vars : (string * T.t) list;
          ops : (op * (T.t list * T.t)) list;
        }

    let add_var env (v,t) =
      { env with vars = (v,t)::env.vars }

    let add_vars env v =
      { env with vars = v@env.vars }

    let create () =
      let f_f = [T.Float], T.Float in
      let ff_f = [T.Float; T.Float], T.Float in
      {
        vars = [];
        ops = [ FAdd, ff_f; FSub, ff_f; FMul, ff_f; FDiv, ff_f; Call "sin", f_f ]
      }
  end

  let rec prepend_last s = function
    | [] -> assert false
    | [x] -> [s^x]
    | x::xx -> x::(prepend_last s xx)

  let rec expr_type ~env = function
    | Ident x -> List.assoc x env.Env.vars
    | Float _ -> T.Float
    | Alloc t -> T.Ptr t
    | Load r ->
      (
        match prog_type ~env r with
          | T.Ptr t -> t
          | _ -> assert false
      )
    | Store _ -> T.Void
    | Op (op, _) -> snd (List.assoc op env.Env.ops)
    | Let _ -> T.Void

  and prog_type ~env = function
    | [] -> T.Void
    | [e] -> expr_type ~env e
    | (Let (x,p))::ee ->
      let env = Env.add_var env (x,prog_type ~env p) in
      prog_type ~env ee
    | _::ee -> prog_type ~env ee

  let rec emit_type = function
    | T.Void -> "void"
    | T.Float -> "float"
    | T.Struct s ->
      let s = List.map (fun (x,t) -> Printf.sprintf "%s %s;" (emit_type t) x) s in
      let s = String.concat " " s in
      Printf.sprintf "struct { %s }" s
    | T.Ptr t -> Printf.sprintf "%s*" (emit_type t)

  let tmp_var =
    let n = ref 0 in
    fun () ->
      incr n;
      Printf.sprintf "saml_tmp%d" !n

  let rec emit_expr ?return ~env e =
    let decl x t = Printf.sprintf "%s %s;" (emit_type t) x in
    match e with
      | Alloc t -> env, [Printf.sprintf "malloc(sizeof(%s));" (emit_type t)]
      | Let (x,p) ->
        let t = prog_type ~env p in
        let _, p = emit_prog ~env p in
        let p = prepend_last "x = " p in
        let env = Env.add_var env (x,t) in
        env, (decl x t)::p
      | Float f ->  env, [Printf.sprintf "%f;" f]
      | Ident x -> env, [Printf.sprintf "%s;" x]
      | Load p ->
        let t = prog_type ~env p in
        let tmp = tmp_var () in
        let _, p = emit_prog ~env p in
        let p = prepend_last "*" p in
        env, (decl tmp t)::p
      | Store (x,p) ->
        let t = prog_type ~env x in
        let tmp = tmp_var () in
        let _, x = emit_prog ~env x in
        let x = prepend_last (tmp^" = ") x in
        let _, p = emit_prog ~env p in
        let p = prepend_last (Printf.sprintf "*%s = " tmp) p in
        env, [decl tmp t]@x@p
      | Op (op, args) ->
        let tmp = Array.map (fun _ -> tmp_var ()) args in
        let argsp = Array.map (fun p -> snd (emit_prog ~env p)) args in
        let argsp = Array.mapi (fun i p -> prepend_last (tmp.(i)^" = ") p) argsp in
        let p =
          match op with
            | FAdd -> [Printf.sprintf "(%s + %s);" tmp.(0) tmp.(1)]
            | FSub -> [Printf.sprintf "(%s - %s);" tmp.(0) tmp.(1)]
            | FMul -> [Printf.sprintf "(%s * %s);" tmp.(0) tmp.(1)]
            | FDiv -> [Printf.sprintf "(%s / %s);" tmp.(0) tmp.(1)]
            | Call f ->
              let tmp = Array.to_list tmp in
              let tmp = String.concat ", " tmp in
              [Printf.sprintf "%s(%s);" f tmp]
        in
        let tmp = Array.mapi (fun i x -> decl x (prog_type ~env args.(i))) tmp in
        let tmp = Array.to_list tmp in
        let argsp = Array.to_list argsp in
        let argsp = List.flatten argsp in
        env, tmp@argsp@p

  and emit_prog ~env prog =
    match prog with
      | [] -> env, []
      | e::ee ->
        let env, e = emit_expr ~env e in
        let env, ee = emit_prog ~env ee in
        env, e@ee

  let emit_decl ~env = function
    | Decl (proto, prog) ->
      let name, args, t = proto in
      let env = Env.add_vars env args in
      let args = List.map (fun (x,t) -> Printf.sprintf "%s %s" (emit_type t) x) args in
      let args = String.concat ", " args in
      let prog = snd (emit_prog ~env prog) in
      let prog = prepend_last "return " prog in
      let prog = String.concat "\n" prog in
      Printf.sprintf "%s %s(%s) {\n%s\n}\n" (emit_type t) name args prog

  let emit_decls d =
    let env = Env.create () in
    String.concat "\n" (List.map (emit_decl ~env) d)
end
