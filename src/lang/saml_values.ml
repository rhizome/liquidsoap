(** "Values", as manipulated by SAML. *)

open Lang_values

module B = Saml_backend
module V = Lang_values
module T = Lang_types

type t = V.term

type stateful =
    {
      prog : term;
      (* Notice that refs are in reverse order! *)
      refs : (string * term) list;
    }

let builtin_prefix = "#saml_"
let builtin_prefix_re = Str.regexp ("^"^builtin_prefix)

let meta_vars = ["period"]

let make_term ?t tm =
  let t =
    match t with
      | Some t -> t
      | None -> T.fresh_evar ~level:(-1) ~pos:None
  in
  { term = tm; t = t }

let make_let x v t =
  let l =
    {
      doc = (Doc.none (), []);
      var = x;
      gen = [];
      def = v;
      body = t;
    }
  in
  make_term ~t:t.t (Let l)

let make_field ?t ?opt r x =
  let t =
    match t with
      | Some _ -> t
      | None ->
        match (T.deref r.t).T.descr with
          | T.Record r -> Some (snd (fst (T.Fields.find x r.T.fields)))
          | _ -> None
  in
  make_term ?t (Field (r, x, opt))

(* Convert values to terms. This is a hack necessary becausse FFI are values and
   not terms (we should change this someday...). *)
let rec term_of_value v =
  (* Printf.printf "term_of_value: %s\n%!" (V.V.print_value v); *)
  let term =
    match v.V.V.value with
      | V.V.Record r ->
        let r =
          let ans = ref T.Fields.empty in
          T.Fields.iter
            (fun x v ->
              try
                ans := T.Fields.add x { V.rgen = v.V.V.v_gen; V.rval = term_of_value v.V.V.v_value } !ans
              with
                | _ -> (* TODO: yes, this is a hack... *) ()
            ) r;
          !ans
        in
        Record r
      | V.V.FFI ffi ->
        (
          match ffi.V.V.ffi_external with
            | Some x -> Var (builtin_prefix^x)
            | None -> failwith "TODO: don't know how to emit code for this operation"
        )
      | V.V.Fun (params, applied, venv, t) ->
        let params = List.map (fun (l,x,v) -> l,x,T.fresh_evar ~level:(-1) ~pos:None,Utils.may term_of_value v) params in
        let applied = List.map (fun (x,(_,v)) -> x,v) applied in
        let venv = List.map (fun (x,(_,v)) -> x,v) venv in
        let venv = applied@venv in
        let t = reduce ~venv t in
        Fun (V.Vars.empty, params, t)
  in
  make_term term

(** Reduce a term. [venv] is an environment of values. When [toplevel] is
    [true], the let should not be reduced. *)
and reduce ?(toplevel=false) ?(venv=[]) ?(env=[]) tm =
  (* Printf.printf "reduce: %s\n%!" (V.print_term tm); *)
  let reduce ?(venv=venv) ?(env=env) = reduce ~venv ~env in
  let term =
    match tm.term with
      | Var "period" -> tm.term
      | Var x ->
        (
          try
            (List.assoc x env).term
          with
            | Not_found ->
              try
                (term_of_value (List.assoc x venv)).term
              with
                | Not_found -> tm.term
        )
      | Unit | Bool _ | Int _ | String _ | Float _ | Encoder _ -> tm.term
      | Seq (a,b) ->
        let a = reduce a in
        let b = reduce b in
        (
          match a.term with
            | Unit -> b.term
            | _ -> Seq (a, b)
        )
      | Ref r -> Ref (reduce r)
      | Get r -> Get (reduce r)
      | Set (r,v) -> Set (reduce r, reduce v)
      | Record r ->
        let r = T.Fields.map (fun v -> { v with rval = reduce v.rval }) r in
        Record r
      | Field (r,x,d) ->
        (* TODO: alpha-conversion on d *)
        let r = reduce r in
        (
          match r.term with
            | Record r -> (T.Fields.find x r).rval.term
            | Seq (a, b) ->
              let b = make_term (Field (b,x,d)) in
              Seq (a, reduce b)
            | Let l ->
              let body = make_term (Field (l.body,x,d)) in
              let body = reduce body in
              Let { l with body = body }
            | _ ->
              Printf.printf "instead of record: %s\n%!" (V.print_term r);
              assert false
        )
      | Replace_field _ -> failwith "reduce: Replace_field"
      | Open _ -> failwith "reduce: Open"
      | Let l ->
        (* TODO: don't reduce when used multiple times *)
        let reducible = not toplevel &&
          match (T.deref l.def.t).T.descr with
            | T.Constr { T.name = "ref" } -> false
            | _ -> true
        in
        if reducible then
          (* TODO: alpha-conversion!!! *)
          let env = (l.var,l.def)::env in
          (reduce ~env l.body).term
        else
          let l = { l with def = reduce ~env l.def; body = reduce ~toplevel ~env l.body } in
          Let l
      | Fun (vars,p,v) ->
        let env =
          let env = ref env in
          List.iter (fun (l,_,_,_) -> env := List.remove_assoc l !env) p;
          !env
        in
        Fun (vars,p,reduce ~env v)
      | App (a,l) ->
        let a = reduce a in
        let l = List.map (fun (l,v) -> l, reduce v) l in
        (
          match a.term with
            | Fun (vars, args, body) ->
              let args = List.map (fun (l,x,t,v) -> l,(x,t,v)) args in
              let args = ref args in
              let find_arg l =
                let (x,_,_) = List.assoc l !args in
                args := List.remove_assoc l !args;
                x
              in
              let l = List.map (fun (l,v) -> find_arg l, v) l in
              (* TODO: alpha-conversion!!! *)
              let env = l@env in
              let body = reduce ~env body in
              (* TODO: reduce optional args if no non-optional is present *)
              if !args = [] then
                body.term
              else
                let args = List.map (fun (l,(x,t,v)) -> l,x,t,v) !args in
                Fun (vars, args, body)
            | _ ->
              App (a,l)
        )
  in
  { tm with term = term }

let subst x v tm = reduce ~env:[x,v] tm

let substs s tm = reduce ~env:s tm

let fresh_ref =
  let n = ref 0 in
  fun () ->
    incr n;
    Printf.sprintf "saml_ref%d" !n

(** Extract the state from a term. *)
(* TODO: in x = ref r, check that r does not have free variables other than
   previously defined refs *)
(* TODO: this could be merged with reduce? *)
let rec extract_state tm =
  (* Printf.printf "extract_state: %s\n%!" (V.print_term tm); *)
  let mk tm' = { term = tm'; t = tm.t } in
  let merge_state p a b =
    { prog = p; refs = b.refs@a.refs }
  in
  match tm.term with
    | Var _ | Unit | Bool _ | Int _ | String _ | Float _ -> { prog = tm; refs = [] }
    | Let ({ def = { term = Ref r } } as l) ->
      let x = l.var in
      let x' = fresh_ref () in
      let body = subst x (make_term (Var x')) l.body in
      let state = extract_state body in
      { state with refs = (x', r)::state.refs }
    | Let l ->
      let def = extract_state l.def in
      let body = extract_state l.body in
      let l = { l with def = def.prog; body = body.prog } in
      merge_state (mk (Let l)) def body
    | Ref v ->
      let v = extract_state v in
      { v with prog = mk (Ref (v.prog)) }
    | Get r ->
      let r = extract_state r in
      { r with prog = mk (Get (r.prog)) }
    | Set (r,v) ->
      let r = extract_state r in
      let v = extract_state v in
      merge_state (mk (Set (r.prog, v.prog))) r v
    | Seq (a, b) ->
      let a = extract_state a in
      let b = extract_state b in
      merge_state (mk (Seq (a.prog, b.prog))) a b
    | Fun (vars, args, v) ->
      let v = extract_state v in
      { v with prog = mk (Fun (vars, args, v.prog)) }
    | App (f,a) ->
      let ans = ref (extract_state f) in
      let a =
        List.map
          (fun (l,v) ->
            let v = extract_state v in
            ans := merge_state !ans.prog !ans v;
            l, v.prog
          ) a
      in
      let ans = !ans in
      { ans with prog = mk (App (ans.prog, a)) }

let rec emit_type t =
  (* Printf.printf "emit_type: %s\n%!" (T.print t); *)
  match (T.deref t).T.descr with
    | T.Ground T.Unit -> B.T.Void
    | T.Ground T.Float -> B.T.Float
    | T.Constr { T.name = "ref"; params = [_,t] } -> B.T.Ptr (emit_type t)
    | T.Arrow (args, t) ->
      let args = List.map (fun (o,l,t) -> assert (not o); assert (l = ""); emit_type t) args in
      B.T.Arr (args, emit_type t)
    | T.EVar _ -> assert false; failwith "Cannot emit programs with universal types"

let rec emit_prog tm =
  (* Printf.printf "emit_prog: %s\n%!" (V.print_term tm); *)
  let rec focalize_app tm =
    match tm.term with
      | App (x,l2) ->
        let x, l1 = focalize_app x in
        x, l1@l2
      | x -> x,[]
  in
  match tm.term with
    | Float f -> [B.Float f]
    | Var x -> [B.Ident x]
    | Ref r ->
      let tmp = fresh_ref () in
      [B.Let (tmp, [B.Alloc (emit_type r.t)]); B.Store ([B.Ident tmp], emit_prog r); B.Ident tmp]
    | Get r -> [B.Load (emit_prog r)]
    | Set (r,v) -> [B.Store (emit_prog r, emit_prog v)]
    | Seq (a,b) -> (emit_prog a)@(emit_prog b)
    | App _ ->
      let x, l = focalize_app tm in
      (
        match x with
          | Var x when Str.string_match builtin_prefix_re x 0 ->
            let x =
              let bpl = String.length builtin_prefix in
              String.sub x bpl (String.length x - bpl)
            in
            let l = List.map (fun (l,v) -> assert (l = ""); emit_prog v) l in
            let l = Array.of_list l in
            let op =
              match x with
                (* TODO: handle integer operations *)
                | "add" -> B.FAdd
                | "sub" -> B.FSub
                | "mul" -> B.FMul
                | "div" -> B.FDiv
                | _ -> B.Call x
            in
            [B.Op (op, l)]
          | _ -> assert false
      )
    | Field (r,x,_) ->
      (* Records are always passed by reference. *)
      [B.Field ([B.Load (emit_prog r)], x)]
    | Unit -> assert false
    | Int _ -> assert false
    | Fun _ -> assert false
    | Record _ -> assert false
    | Replace_field _ | Open _ | Let _ -> assert false

(** Emit a prog which might start by decls (toplevel lets). *)
let rec emit_decl_prog tm =
  (* Printf.printf "emit_decl_prog: %s\n%!" (print_term tm); *)
  match tm.term with
    | Let l ->
      Printf.printf "def: %s : %s\n%!" (print_term l.def) (T.print l.def.t);
      let t = emit_type l.def.t in
      (
        match t with
          | B.T.Arr (args, t) ->
            let args =
              let n = ref 0 in
              List.map (fun t -> incr n; Printf.sprintf "x%d" !n, t) args
            in
            let proto = l.var, args, t in
            let d = B.Decl (proto, emit_prog l.def) in
            let body =
              let args = List.map (fun (x, _) -> "", make_term (Var x)) args in
              make_term (App (l.body, args))
            in
            let dd, p = emit_decl_prog body in
            d::dd, p
          | _ ->
            let dd, p = emit_decl_prog l.body in
            let e =
              match emit_prog l.def with
                | [e] -> e
                | _ -> assert false
            in
            (B.Decl_cst (l.var, e))::dd, p
      )
    | _ -> [], emit_prog tm

let emit name ~env ~venv tm =
  Printf.printf "emit: %s : %s\n%!" (V.print_term tm) (T.print tm.t);
  let prog = reduce ~toplevel:true ~venv ~env tm in
  Printf.printf "reduced: %s\n%!" (V.print_term prog);
  let prog = extract_state prog in
  Printf.printf "extracted: %s\n%!" (V.print_term prog.prog);

  (* Compute the state. *)
  let refs = List.rev prog.refs in
  let refs_t = List.map (fun (x,v) -> x, emit_type v.V.t) refs in
  let refs = List.map (fun (x,v) -> x, emit_prog v) refs in
  let state_t = B.T.Struct refs_t in

  (* Emit the program. *)
  let prog = prog.prog in
  let decls, prog = emit_decl_prog prog in
  let prog = B.Decl ((name, ["period", B.T.Float], emit_type tm.t), prog) in
  let decls = decls@[prog] in

  (* Add state to emitted functions. *)
  let decls =
    let alias_state =
      let f x =
        let s = [B.Load [B.Ident "state"]] in
        let r = [B.Field(s,x)] in
        let r = [B.Address_of r] in
        B.Let (x, r)
      in
      List.map (fun (x,_) -> f x) refs
    in
    List.map
      (function
        | B.Decl ((name, args, t), prog) ->
          B.Decl ((name, ("state", B.T.Ptr state_t)::args, t), alias_state@prog)
      ) decls
  in

  (* Declare generic functions for manipulating state. *)
  let reset =
    List.map
      (fun (x,p) ->
        let s = [B.Load [B.Ident "state"]] in
        let r = [B.Field (s, x)] in
        let r = [B.Address_of r] in
        B.Store (r, p)
      ) refs
  in
  let reset = B.Decl ((name^"_reset", ["state", B.T.Ptr state_t], B.T.Void), reset) in
  let alloc =
    [
      B.Let ("state", [B.Alloc state_t]);
      B.Op (B.Call (name^"_reset"), [|[B.Ident "state"]|]);
      B.Ident "state"
    ]
  in
  let alloc = B.Decl ((name^"_alloc", [], B.T.Ptr state_t), alloc) in
  let free = [B.Free [B.Ident "state"]] in
  let free = B.Decl ((name^"_free", ["state", B.T.Ptr state_t], B.T.Void), free) in

  reset::alloc::free::decls
