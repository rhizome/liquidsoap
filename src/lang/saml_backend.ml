(** AST for the backend before code emission. We should keep this as close as
    LLVM's representation as possible. *)

open Utils.Stdlib

module T = struct
  (** A type. *)
  type t =
    | Void
    | Bool
    | Int
    | Float
    | Ptr of t
    | Struct of (string * t) list
    (** An external type identifier (e.g. defined in an include). *)
    | Ident of string
    | Arr of t list * t

  let rec print = function
    | Void -> "void"
    | Bool -> "bool"
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
  | FAdd | FSub | FMul | FDiv | FMod
  | FEq | FLt | FGe
  | BAnd | BOr
  | Call of string

(** An expression. *)
type expr =
  | Let of string * prog
  | Int of int
  | Float of float
  | Bool of bool
  | Ident of string
  | Alloc of T.t
  | Free of prog
  (** [Load p] loads memory pointed by p. *)
  | Load of prog
  (** [Store (p,v)] stores value v in memory pointed by p. *)
  | Store of prog * prog
  | Field of prog * string
  | Address_of of prog
  | If of prog * prog * prog (** If then else *)
  | Op of op * prog array
  (** NULL pointer (of a given type). *)
  | Null of T.t

(** A program. *)
and prog = expr list

(** A function declaration. *)
and decl =
  | Decl of proto * prog
  | Decl_cst of string * expr
  | Decl_type of string * T.t
  (* | External of proto *)

(** Prototype of a function: name, typed arguments and return type. *)
and proto = string * (string * T.t) list * T.t

let print_op = function
  | FAdd -> "+"
  | FSub -> "-"
  | FMul -> "*"
  | FDiv -> "/"
  | FMod -> "mod"
  | FEq -> "=="
  | FLt -> "<"
  | FGe -> ">="
  | BAnd -> "&&"
  | BOr -> "||"
  | Call x -> x

let rec print_expr = function
  | Let (x,p) -> Printf.sprintf "let %s = [%s]" x (print_prog p)
  | Int n -> Printf.sprintf "%d" n
  | Float f -> Printf.sprintf "%f" f
  | Bool b -> Printf.sprintf "%B" b
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
  | If (p,p1,p2) ->
    if p2 = [] then
      Printf.sprintf "if (%s) then (%s)" (print_prog p) (print_prog p1)
    else
      Printf.sprintf "if (%s) then (%s) else (%s)" (print_prog p) (print_prog p1) (print_prog p2)
  | Null t -> Printf.sprintf "null{%s}" (T.print t)

and print_prog p =
  let p = List.map print_expr p in
  String.concat ";\n" p

let print_decl = function
  | Decl ((name, args, t), p) ->
    let args = List.map (fun (x,t) -> Printf.sprintf "%s : %s" x (T.print t)) args in
    let args = String.concat ", " args in
    Printf.sprintf "decl %s(%s) : %s =\n%s" name args (T.print t) (print_prog p)
  | Decl_cst (name, e) ->
    Printf.sprintf "decl %s = %s" name (print_expr e)
  | Decl_type (tn, t) ->
    Printf.sprintf "tdecl %s = %s" tn (T.print t)

let print_decls d =
  let d = List.map print_decl d in
  String.concat "\n" d

(** Types of builtin ops. *)
let builtin_ops = ref []

(** Emit C code. *)
module Emitter_C = struct
  (** Emitters for builtin ops. *)
  let builtin_ops_emitters = ref []

  module Env = struct
    type t =
        {
          (** Variables already defined together with their type. *)
          vars : (string * T.t) list;
          (** Variables already used (in order to avoid masking variables). *)
          used_vars : string list;
          (** Variables to be renamed during emission. *)
          renamings : (string * string) list;
        }

    (* TODO: implement this in a functional way *)
    (* TODO: (T.t * string) list instead of (string * string) list*)
    let type_decls = ref []

    let add_var env (v,t) =
      { env with vars = (v,t)::env.vars; used_vars = v::env.used_vars }

    let add_vars env v =
      { env with vars = v@env.vars; used_vars = (List.map fst v)@env.used_vars }

    let is_defined env v =
      List.mem_assoc v env.vars

    let create ?(vars=[]) () =
      {
        vars = vars;
        used_vars = [];
        renamings = [];
      }

  let ident env x =
    try
      List.assoc x env.renamings
    with
      | Not_found -> x

  let op_type x =
    let ot =
      let ff_f = [T.Float; T.Float], T.Float in
      let ff_b = [T.Float; T.Float], T.Bool in
      let bb_b = [T.Bool; T.Bool], T.Bool in
      [
        FAdd, ff_f; FSub, ff_f; FMul, ff_f; FDiv, ff_f; FMod, ff_f;
        FEq, ff_b; FLt, ff_b; FGe, ff_b;
        BAnd, bb_b; BOr, bb_b;
      ]
    in
    match x with
      | Call x ->
        let t = List.assoc x !builtin_ops in
        (
          match t with
            | T.Arr (t1,t2) -> t1,t2
            | _ -> assert false
        )
      | _ ->
        List.assoc x ot
  end

  let rec map_last f = function
    | [] -> []
    | [x] -> [f x]
    | x::xx -> x::(map_last f xx)

  let prepend_last s l =
    map_last (fun x -> s^x) l

  let append_last s l =
    map_last (fun x -> x^s) l

  let rec expr_type ~env e =
    (* Printf.printf "expr_type: %s\n%!" (print_expr e); *)
    match e with
      | Ident x ->
        let x = Env.ident env x in
        List.assoc x env.Env.vars
      | Int _ -> T.Int
      | Float _ -> T.Float
      | Bool _ -> T.Bool
      | Alloc t -> T.Ptr t
      | Free _ -> T.Void
      | Load r ->
        (
          match prog_type ~env r with
            | T.Ptr t -> t
            | _ -> assert false
        )
      | Store _ -> T.Void
      | Op (op, _) ->
        (* Printf.printf "expr_type_op: %s\n%!" (print_op op); *)
        snd (Env.op_type op)
      | Let _ -> T.Void
      | Field (r,x) ->
        let t =
          match prog_type ~env r with
            | T.Struct r -> r
            | _ -> assert false
        in
        List.assoc x t
      | Address_of r -> T.Ptr (prog_type ~env r)
      | If (p,p1,p2) -> prog_type ~env p1
      | Null t -> t

  and prog_type ~env = function
    | [] -> T.Void
    | [e] -> expr_type ~env e
    | (Let (x,p))::ee ->
      let env = Env.add_var env (x,prog_type ~env p) in
      prog_type ~env ee
    | _::ee -> prog_type ~env ee

  (** Rename a variable if necessary: it takes cares of the fact that in C a
      variable cannot be masked and moreover some charaters are forbidden in
      variable names. *)
  let rename_var ~env x =
    let defined x = List.mem x env.Env.used_vars in
    let x' =
      if defined x then
        let n = ref 1 in
        let x' () = Printf.sprintf "%s%d" x !n in
        while List.mem (x'()) env.Env.used_vars do
          incr n
        done;
        Printf.sprintf "%s%d" x !n
      else
        x
    in
    let x' = Str.global_replace (Str.regexp "'") "_prime" x' in
    assert (not (defined x'));
    x'

  let type_decl =
    let n = ref 0 in
    fun ?name t ->
      try
        if name <> None then raise Not_found;
        List.assoc t !Env.type_decls
      with
        | Not_found ->
          let tn =
            match name with
              | Some name -> name
              | None ->
                incr n;
                Printf.sprintf "saml_type%d" !n
          in
          Env.type_decls := (t,tn) :: !Env.type_decls;
          tn

  let rec emit_type ?(use_decls=true) t =
    let emit_type ?(use_decls=use_decls) = emit_type ~use_decls in
    match t with
      | T.Void -> "void"
      | T.Bool -> "int"
      | T.Int -> "int"
      | T.Float -> "float"
      | T.Struct s ->
        let t = List.map (fun (x,t) -> Printf.sprintf "%s %s;" (emit_type t) x) s in
        let t = String.concat " " t in
        let t = Printf.sprintf "struct { %s }" t in
        if use_decls then type_decl t else t
      | T.Ptr t -> Printf.sprintf "%s*" (emit_type t)
      | T.Ident t -> t
      | T.Arr _ -> assert false

  let tmp_var =
    let n = ref 0 in
    fun () ->
      incr n;
      Printf.sprintf "saml_tmp%d" !n

  (* used_vars should be propagated everwhere as done in the let case *)
  let rec emit_expr ?(return=fun s->s) ~env e =
    (* Printf.printf "emit_expr: %s\n%!" (print_expr e); *)
    let decl x t = Printf.sprintf "%s %s;" (emit_type t) x in
    let r f s = return (f s) in
    match e with
      | Alloc t ->
        env, [return (Printf.sprintf "malloc(sizeof(%s))" (emit_type t))]
      | Free p ->
        let return = r (fun s -> Printf.sprintf "free(%s)" s) in
        let _, p = emit_prog ~return ~env p in
        env, p
      | Let (x,p) ->
        let t = prog_type ~env p in
        let x' = rename_var ~env x in
        let return s = Printf.sprintf "%s %s = %s" (emit_type t) x' s in
        (* We have to add the variable before in order to cope with
           situations like let x = let x = ... in ... *)
        let env = { env with Env.used_vars = x'::env.Env.used_vars } in
        let env', p = emit_prog ~return ~env p in
        (* This is a hack necessary because of the situation mentionned above:
           we don't want to keep the introduced renamings in the following but
           we want to keep the names of already defined variables. *)
        let env = { env with Env.used_vars = env'.Env.used_vars } in
        let env = Env.add_var env (x',t) in
        let env =
          if x = x' then
            env
          else
            { env with Env.renamings = (x,x')::env.Env.renamings }
        in
        env, p
      | Int n ->
        env, [return (Printf.sprintf "%d" n)]
      | Float f ->
        env, [return (Printf.sprintf "%f" f)]
      | Bool b ->
        env, [return (if b then "1" else "0")]
      | Ident x ->
        let x = Env.ident env x in
        env, [return (Printf.sprintf "%s" x)]
      | Address_of p ->
        let return = r (fun s -> "&" ^ s) in
        let _, p = emit_prog ~return ~env p in
        env, p
      | Load p ->
        let return = r (fun s -> Printf.sprintf "(*%s)" s) in
        let _, p = emit_prog ~return ~env p in
        env, p
      | Store ([Ident x], p) ->
        let x = Env.ident env x in
        let return = r (fun s -> Printf.sprintf "*%s = %s" x s) in
        let _, p = emit_prog ~return ~env p in
        env, p
      | Store (x,p) ->
        let t = prog_type ~env x in
        let tmp = tmp_var () in
        let return = r (fun s -> Printf.sprintf "%s %s = %s" (emit_type t) tmp s) in
        let _, x = emit_prog ~return ~env x in
        let x = append_last ";" x in
        let return = r (fun s -> Printf.sprintf "*%s = %s" tmp s) in
        let _, p = emit_prog ~return ~env p in
        env, x@p
      | Field (rr,x) ->
        let return = r (fun s -> Printf.sprintf "%s.%s" s x) in
        let _, p = emit_prog ~return ~env rr in
        env, p
      | If (p, p1, p2) ->
        let b, btmp =
          match snd (emit_prog ~env p) with
            | [x] -> [], x
            | _ ->
              let btmp = tmp_var () in
              let _, b =
                let return s = Printf.sprintf "%s %s = %s" (emit_type T.Bool) btmp s in
                emit_prog ~return ~env p
              in
              let b = append_last ";" b in
              b, btmp
        in
        let _, p1 = emit_prog ~return ~env p1 in
        let e =
          if p2 = [] then "" else
            let _, p2 = emit_prog ~return ~env p2 in
            Printf.sprintf " else {\n%s;\n}" (String.concat "\n" p2)
        in
        env, b@[Printf.sprintf "if (%s) {\n%s;\n}%s" btmp (String.concat "\n" p1) e]
      | Op (op, args) ->
        let tmp_vars = ref [] in
        (* Precomputation of the arguments *)
        let args_comp = ref [] in
        let env, args =
          let env = ref env in
          let args =
            Array.map
              (fun p ->
                let t = prog_type ~env:!env p in
                let env', p' = emit_prog ~env:!env p in
                match p' with
                  | [e] -> env := env'; e
                  | _ ->
                    let tmp = tmp_var () in
                    let return s = Printf.sprintf "%s = %s" tmp s in
                    let env', p = emit_prog ~return ~env:!env p in
                    let p = append_last ";" p in
                    env := env';
                    tmp_vars := (tmp,t) :: !tmp_vars;
                    args_comp := !args_comp @ p;
                    tmp
              ) args
          in
          !env, args
        in
        let p =
          match op with
            | FAdd -> [return (Printf.sprintf "(%s + %s)" args.(0) args.(1))]
            | FSub -> [return (Printf.sprintf "(%s - %s)" args.(0) args.(1))]
            | FMul -> [return (Printf.sprintf "(%s * %s)" args.(0) args.(1))]
            | FDiv -> [return (Printf.sprintf "(%s / %s)" args.(0) args.(1))]
            | FMod -> [return (Printf.sprintf "remainder(%s, %s)" args.(0) args.(1))]
            | FEq -> [return (Printf.sprintf "(%s == %s)" args.(0) args.(1))]
            | FLt -> [return (Printf.sprintf "(%s < %s)" args.(0) args.(1))]
            | FGe -> [return (Printf.sprintf "(%s >= %s)" args.(0) args.(1))]
            | BAnd -> [return (Printf.sprintf "(%s && %s)" args.(0) args.(1))]
            | BOr -> [return (Printf.sprintf "(%s || %s)" args.(0) args.(1))]
            | Call f ->
              (* Printf.printf "call %s\n%!" f; *)
              if Env.is_defined env f then
                let args = Array.to_list args in
                let args = String.concat ", " args in
                [return (Printf.sprintf "%s(%s)" f args)]
              else
                [return ((List.assoc f !builtin_ops_emitters) args)]
        in
        let tmp_decl = List.map (fun (x,t) -> decl x t) !tmp_vars in
        env, tmp_decl @ !args_comp @ p
      | Null _ ->
        env, [return "NULL"]

  and emit_prog ?return ~env prog =
    match prog with
      | [] ->
        env, []
      | e::ee ->
        let env, e =
          let return = if ee = [] then return else None in
          emit_expr ?return ~env e
        in
        let e = if ee = [] then e else append_last ";" e in
        let env, ee = emit_prog ?return ~env ee in
        env, e@ee

  let emit_decl ~env decl =
    (* Printf.printf "emit_decl: %s\n%!" (print_decl decl); *)
    match decl with
      | Decl (proto, prog) ->
        let name, args, t = proto in
        let env' = Env.add_vars env args in
        let args = List.map (fun (x,t) -> Printf.sprintf "%s %s" (emit_type t) x) args in
        let args = String.concat ", " args in
        let return = if t = T.Void then (fun s -> s) else (fun s -> "return " ^ s) in
        let prog = snd (emit_prog ~return ~env:env' prog) in
        (* let prog = List.map (fun s -> "  " ^ s) prog in *)
        let prog = String.concat "\n" prog in
        let prog = prog ^ ";" in
        let env = Env.add_var env (name,t) in
        env, Printf.sprintf "inline %s %s(%s) {\n%s\n}" (emit_type t) name args prog
      | Decl_cst (x,e) ->
        let t = expr_type ~env e in
        let _, e = emit_expr ~env e in
        let e = append_last ";" e in
        let e =
          match e with
            | [e] -> e
            | _ -> assert false
        in
        let env = Env.add_var env (x,t) in
        env, Printf.sprintf "%s %s = %s;" (emit_type t) x e
      | Decl_type (name, t) ->
        ignore (type_decl ~name (emit_type ~use_decls:false t));
        env, ""

  let default_includes = ["stdlib.h"; "math.h"; "stdio.h"]

  (** Emit a list of includes. *)
  let emit_includes includes =
    let includes = List.map (fun f -> Printf.sprintf "#include <%s>" f) includes in
    String.concat "\n" includes

  (** Emit global type declarations. *)
  let emit_type_decls () =
    let td = List.map (fun (t,tn) -> Printf.sprintf "typedef %s %s;" t tn) !Env.type_decls in
    String.concat "\n\n" td

  let emit_decls ?(env=Env.create ()) d =
    Env.type_decls := [];
    let env = ref env in
    let d =
      List.map
        (fun d ->
          let e, d = emit_decl ~env:(!env) d in
          env := e;
          d
        ) d
    in
    let td = emit_type_decls () in
    let includes = emit_includes default_includes in
    String.concat "\n\n" (includes::td::d)

  let emit_dssi ?env ~name d =
    (*
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
    *)
    Env.type_decls := [];
    let env = Env.create ?vars:env () in
    let d = emit_decls ~env d in
    let ans = d ^ "\n\n" in
    let ans = ref ans in
    let add s = ans := !ans ^ s ^ "\n" in
    add (Printf.sprintf "#define STATE saml_state");
    add (Printf.sprintf "#define SAML_name %S" name);
    add (Printf.sprintf "#define SAML_synth %s" name);
    add (Printf.sprintf "#define SAML_synth_alloc %s" (name^"_alloc"));
    add (Printf.sprintf "#define SAML_synth_reset %s" (name^"_reset"));
    add (Printf.sprintf "#define SAML_synth_free %s" (name^"_free"));
    add (Printf.sprintf "#define SAML_synth_set_velocity %s" (name^"_set_velocity"));
    add (Printf.sprintf "#define SAML_synth_set_freq %s" (name^"_set_freq"));
    add (Printf.sprintf "#define SAML_synth_note_off %s" (name^"_note_off"));
    add (Printf.sprintf "#define SAML_synth_is_active %s" (name^"_is_active"));
    add (Printf.sprintf "#define SAML_synth_activate %s" (name^"_activate"));
    add Saml_dssi.c;
    !ans
end
