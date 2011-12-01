(** AST for the backend before code emission. We should keep this as close as
    LLVM's representation as possible. *)

(** Raised by "Liquidsoap" implementations of functions when no reduction is
    possible. *)
exception Cannot_reduce

module T = struct
  (** A type. *)
  type t =
    | Void
    | Int
    | Float
    | Ptr of t
    | Struct of (string * t) list
    (** An external type identifier (e.g. defined in an include). *)
    | Ident of string
    | Arr of t list * t

  let rec print = function
    | Void -> "void"
    | Int -> "int"
    | Float -> "float"
    | Ptr t -> Printf.sprintf "%s ptr" (print t)
    | Struct _ -> "struct{...}"
    | Ident x -> x
    | Arr (args,t) ->
      let args = List.map print args in
      let args = String.concat "," args in
      Printf.sprintf "(%s)->%s" args (print t)
end

(** An operation. *)
type op =
  | FAdd | FSub | FMul | FDiv
  | Call of string

(** An expression. *)
type expr =
  | Let of string * prog
  | Int of int
  | Float of float
  | Ident of string
  | Alloc of T.t
  | Free of prog
  (** [Load p] loads memory pointed by p. *)
  | Load of prog
  (** [Store (p,v)] stores value v in memory pointed by p. *)
  | Store of prog * prog
  | Field of prog * string
  | Address_of of prog
  | Op of op * prog array
  (** NULL pointer (of a given type). *)
  | Null of T.t

(** A program. *)
and prog = expr list

(** A function declaration. *)
and decl =
  | Decl of proto * prog
  | Decl_cst of string * expr
  (* | External of proto *)

(** Prototype of a function: name, typed arguments and return type. *)
and proto = string * (string * T.t) list * T.t

let print_op = function
  | FAdd -> "+"
  | FSub -> "-"
  | FMul -> "*"
  | FDiv -> "/"
  | Call x -> x

let rec print_expr = function
  | Let (x,p) -> Printf.sprintf "let %s = %s" x (print_prog p)
  | Int n -> Printf.sprintf "%d" n
  | Float f -> Printf.sprintf "%f" f
  | Ident x -> x
  | Alloc t -> Printf.sprintf "alloc{%s}" (T.print t)
  | Free p -> Printf.sprintf "free(%s)" (print_prog p)
  | Load p -> Printf.sprintf "load(%s)" (print_prog p)
  | Store (p,v) -> Printf.sprintf "store(%s,%s)" (print_prog p) (print_prog v)
  | Field (p,x) -> Printf.sprintf "(%s).%s" (print_prog p) x
  | Address_of p -> Printf.sprintf "&(%s)" (print_prog p)
  | Op (op, args) ->
    let args = Array.to_list args in
    let args = List.map print_prog args in
    let args = String.concat "," args in
    Printf.sprintf "%s(%s)" (print_op op) args
  | Null t -> Printf.sprintf "null{%s}" (T.print t)

and print_prog p =
  let p = List.map print_expr p in
  String.concat "; " p

let print_decl = function
  | Decl ((name, args, t), p) ->
    let args = List.map (fun (x,t) -> Printf.sprintf "%s : %s" x (T.print t)) args in
    let args = String.concat ", " args in
    Printf.sprintf "decl %s(%s) : %s = %s" name args (T.print t) (print_prog p)
  | Decl_cst (name, e) ->
    Printf.sprintf "decl %s = %s" name (print_expr e)

let print_decls d =
  let d = List.map print_decl d in
  String.concat "\n" d

(** Emit C code. *)
module Emitter_C = struct
  module Env = struct
    type t =
        {
          vars : (string * T.t) list;
          ops : (op * (T.t list * T.t)) list;
        }

    (* TODO: implement this in a functional way *)
    (* TODO: (T.t * string) list instead of (string * string) list*)
    let type_decls = ref []

    let add_var env (v,t) =
      { env with vars = (v,t)::env.vars }

    let add_vars env v =
      { env with vars = v@env.vars }

    let create ?(vars=[]) () =
      let f_f = [T.Float], T.Float in
      let ff_f = [T.Float; T.Float], T.Float in
      {
        vars = vars;
        ops = [ FAdd, ff_f; FSub, ff_f; FMul, ff_f; FDiv, ff_f; Call "sin", f_f ]
      }
  end

  let rec map_last f = function
    | [] -> assert false
    | [x] ->
      let x = String.sub x 0 (String.length x - 1) in
      [f x ^ ";"]
    | x::xx -> x::(map_last f xx)

  let prepend_last s l =
    map_last (fun x -> s^x) l

  let rec expr_type ~env = function
    | Ident x -> List.assoc x env.Env.vars
    | Int _ -> T.Int
    | Float _ -> T.Float
    | Alloc t -> T.Ptr t
    | Free _ -> T.Void
    | Load r ->
      (
        match prog_type ~env r with
          | T.Ptr t -> t
          | _ -> assert false
      )
    | Store _ -> T.Void
    | Op (op, _) -> snd (List.assoc op env.Env.ops)
    | Let _ -> T.Void
    | Field (r,x) ->
      let t =
        match prog_type ~env r with
          | T.Struct r -> r
          | _ -> assert false
      in
      List.assoc x t
    | Address_of r -> T.Ptr (prog_type ~env r)
    | Null t -> t

  and prog_type ~env = function
    | [] -> T.Void
    | [e] -> expr_type ~env e
    | (Let (x,p))::ee ->
      let env = Env.add_var env (x,prog_type ~env p) in
      prog_type ~env ee
    | _::ee -> prog_type ~env ee

  let type_decl =
    let n = ref 0 in
    fun t ->
      try
        List.assoc t !Env.type_decls
      with
        | Not_found ->
          incr n;
          let tn = Printf.sprintf "saml_type%d" !n in
          Env.type_decls := (t,tn) :: !Env.type_decls;
          tn

  let rec emit_type ?(use_decls=true) t =
    let emit_type ?(use_decls=use_decls) = emit_type ~use_decls in
    match t with
      | T.Void -> "void"
      | T.Int -> "int"
      | T.Float -> "float"
      | T.Struct s ->
        let t = List.map (fun (x,t) -> Printf.sprintf "%s %s;" (emit_type t) x) s in
        let t = String.concat " " t in
        let t = Printf.sprintf "struct { %s }" t in
        if use_decls then type_decl t else t
      | T.Ptr t -> Printf.sprintf "%s*" (emit_type t)
      | T.Ident t -> t

  let tmp_var =
    let n = ref 0 in
    fun () ->
      incr n;
      Printf.sprintf "saml_tmp%d" !n

  let rec emit_expr ~env e =
    let decl x t = Printf.sprintf "%s %s;" (emit_type t) x in
    match e with
      | Alloc t -> env, [Printf.sprintf "malloc(sizeof(%s));" (emit_type t)]
      | Free p ->
        let _, p = emit_prog ~env p in
        let p = map_last (fun s -> Printf.sprintf "free(%s)" s) p in
        env, p
      | Let (x,p) ->
        let t = prog_type ~env p in
        let _, p = emit_prog ~env p in
        let p = prepend_last (x^" = ") p in
        let env = Env.add_var env (x,t) in
        env, (decl x t)::p
      | Int n -> env, [Printf.sprintf "%d;" n]
      | Float f ->  env, [Printf.sprintf "%f;" f]
      | Ident x -> env, [Printf.sprintf "%s;" x]
      | Address_of p ->
        let _, p = emit_prog ~env p in
        let p = prepend_last "&" p in
        env, p
      | Load p ->
        let _, p = emit_prog ~env p in
        let p = map_last (fun s -> Printf.sprintf "(*%s)" s) p in
        env, p
      | Store ([Ident x], p) ->
        let _, p = emit_prog ~env p in
        let p = prepend_last (Printf.sprintf "*%s = " x) p in
        env, p
      | Store (x,p) ->
        let t = prog_type ~env x in
        let tmp = tmp_var () in
        let _, x = emit_prog ~env x in
        let x = prepend_last (tmp^" = ") x in
        let _, p = emit_prog ~env p in
        let p = prepend_last (Printf.sprintf "*%s = " tmp) p in
        env, [decl tmp t]@x@p
      | Field (r,x) ->
        let _, p = emit_prog ~env r in
        let p =
          let f s = Printf.sprintf "%s.%s" s x in
          map_last f p
        in
        env, p
      | Op (op, args) ->
        let tmp_vars = ref [] in
        (* Precomputation of the arguments *)
        let args_comp = ref [] in
        let args =
          Array.map
            (fun p ->
              let t = prog_type ~env p in
              let p = snd (emit_prog ~env p) in
              match p with
                | [e] -> String.sub e 0 (String.length e - 1)
                | _ ->
                  let tmp = tmp_var () in
                  let p = prepend_last (tmp^" = ") p in
                  tmp_vars := (tmp,t) :: !tmp_vars;
                  args_comp := !args_comp @ p;
                  tmp
            ) args
        in
        let p =
          match op with
            | FAdd -> [Printf.sprintf "(%s + %s);" args.(0) args.(1)]
            | FSub -> [Printf.sprintf "(%s - %s);" args.(0) args.(1)]
            | FMul -> [Printf.sprintf "(%s * %s);" args.(0) args.(1)]
            | FDiv -> [Printf.sprintf "(%s / %s);" args.(0) args.(1)]
            | Call f ->
              let args = Array.to_list args in
              let args = String.concat ", " args in
              [Printf.sprintf "%s(%s);" f args]
        in
        let tmp_decl = List.map (fun (x,t) -> decl x t) !tmp_vars in
        env, tmp_decl @ !args_comp @ p
      | Null _ -> env, ["NULL;"]

  and emit_prog ~env prog =
    match prog with
      | [] -> env, []
      | e::ee ->
        let env, e = emit_expr ~env e in
        let env, ee = emit_prog ~env ee in
        env, e@ee

  let emit_decl ~env decl =
    (* Printf.printf "emit_decl: %s\n%!" (print_decl decl); *)
    match decl with
      | Decl (proto, prog) ->
        let name, args, t = proto in
        let env = Env.add_vars env args in
        let args = List.map (fun (x,t) -> Printf.sprintf "%s %s" (emit_type t) x) args in
        let args = String.concat ", " args in
        let prog = snd (emit_prog ~env prog) in
        let prog = if t = T.Void then prog@["return;"] else prepend_last "return " prog in
        let prog = List.map (fun s -> "  " ^ s) prog in
        let prog = String.concat "\n" prog in
        Printf.sprintf "%s %s(%s) {\n%s\n}" (emit_type t) name args prog
      | Decl_cst (x,e) ->
        let t = expr_type ~env e in
        let _, e = emit_expr ~env e in
        let e =
          match e with
            | [e] -> e
            | _ -> assert false
        in
        Printf.sprintf "%s %s = %s" (emit_type t) x e

  let default_includes = ["stdlib.h"; "math.h"]

  (** Emit a list of includes. *)
  let emit_includes includes =
    let includes = List.map (fun f -> Printf.sprintf "#include <%s>" f) includes in
    String.concat "\n" includes

  (** Emit global type declarations. *)
  let emit_type_decls () =
    let td = List.map (fun (t,tn) -> Printf.sprintf "typedef %s %s;" t tn) !Env.type_decls in
    String.concat "\n\n" td

  let emit_decls d =
    Env.type_decls := [];
    let env = Env.create () in
    let d = List.map (emit_decl ~env) d in
    let td = emit_type_decls () in
    let includes = emit_includes default_includes in
    String.concat "\n\n" (includes::td::d)

  let emit_dssi ?env d =
    let dssi_descriptor_t =
      T.Struct
        [
          "DSSI_API_Version", T.Int;
        ]
    in
    Env.type_decls := [emit_type ~use_decls:false dssi_descriptor_t, "DSSI_Descriptor"];
    let env = Env.create () in
    (* TODO: we should not have to do this *)
    let env = Env.add_var env ("descriptor", T.Ptr dssi_descriptor_t) in
    let dssi_descriptor_fill =
      let f x v =
        let f = [Address_of [Field ([Load [Ident "descriptor"]], x)]] in
        Store (f, v)
      in
      [
        Store ([Ident "descriptor"], [Alloc dssi_descriptor_t]);
        f "DSSI_API_Version" [Int 1]
      ]
    in
    let init = [Decl (("init", [], T.Void), dssi_descriptor_fill)] in
    let d = (Decl_cst ("descriptor", Null (T.Ptr dssi_descriptor_t)))::d@init in
    let d = List.map (emit_decl ~env) d in
    String.concat "\n\n" d
end
