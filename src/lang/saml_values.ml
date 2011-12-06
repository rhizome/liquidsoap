(** "Values", as manipulated by SAML. *)

open Utils.Stdlib
open Lang_values

module B = Saml_backend
module V = Lang_values
module T = Lang_types

type t = V.term

let builtin_prefix = "#saml_"
let builtin_prefix_re = Str.regexp ("^"^builtin_prefix)

let default_meta_vars = ["period"]

let meta_vars = ref default_meta_vars

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

let make_var ?t x =
  make_term ?t (Var x)

(** Generate a fresh reference name. *)
let fresh_ref =
  let n = ref 0 in
  fun () ->
    incr n;
    Printf.sprintf "saml_ref%d" !n

let fresh_var =
  let n = ref 0 in
  fun () ->
    incr n;
    Printf.sprintf "saml_x%d" !n

let rec free_vars tm =
  (* Printf.printf "free_vars: %s\n%!" (print_term tm); *)
  let fv = free_vars in
  let u v1 v2 = v1@v2 in
  let r xx v = List.filter (fun y -> not (List.mem y xx)) v in
  match tm.term with
    | Var x -> [x]
    | Unit | Bool _ | Int _ | String _ | Float _ -> []
    | Seq (a,b) -> u (fv a) (fv b)
    | Ref r | Get r -> fv r
    | Set (r,v) -> u (fv r) (fv v)
    | Record r -> T.Fields.fold (fun _ v f -> u (fv v.rval) f) r []
    | Field (r,x,o) ->
      let o = match o with Some o -> fv o | None -> [] in
      u (fv r) o
    | Let l -> u (fv l.def) (r [l.var] (fv l.body))
    | Fun (_, p, v) ->
      let o = List.fold_left (fun f (_,_,_,o) -> match o with None -> f | Some o -> u (fv o) f) [] p in
      let p = List.map (fun (_,x,_,_) -> x) p in
      u o (r p (fv v))
    | App (f,a) ->
      let a = List.fold_left (fun f (_,v) -> u f (fv v)) [] a in
      u (fv f) a

let occurences x tm =
  let ans = ref 0 in
  List.iter (fun y -> if y = x then incr ans) (free_vars tm);
  !ans

(** Apply a list of substitutions to a term. *)
let rec substs ss tm =
  (* Printf.printf "substs: %s\n%!" (print_term t); *)
  let s ?(ss=ss) = substs ss in
  let term =
    match tm.term with
      | Var x ->
        let rec aux = function
          | (x',v)::ss when x' = x -> (substs ss v).term
          | _::ss -> aux ss
          | [] -> tm.term
        in
        aux ss
      | Unit | Bool _ | Int _ | String _ | Float _ -> tm.term
      | Seq (a,b) -> Seq (s a, s b)
      | Ref r -> Ref (s r)
      | Get r -> Get (s r)
      | Set (r,v) -> Set (s r, s v)
      | Record r ->
        let r = T.Fields.map (fun v -> { v with rval = s v.rval }) r in
        Record r
      | Field (r,x,d) -> Field (s r, x, Utils.may s d)
      | Replace_field (r,x,v) ->
        let v = { v with rval = s v.rval } in
        Replace_field (s r, x, v)
      | Let l ->
        let def = s l.def in
        let ss = List.remove_all_assoc l.var ss in
        let s = s ~ss in
        let var = if List.mem l.var !meta_vars then l.var else fresh_var () in
        let body = subst l.var (make_term (Var var)) l.body in
        let body = s body in
        let l = { l with var = var; def = def; body = body } in
        Let l
      | Fun (vars,p,v) ->
        let ss = ref ss in
        let sp = ref [] in
        let p =
          List.map
            (fun (l,x,t,v) ->
              let x' = fresh_var () in
              ss := List.remove_all_assoc l !ss;
              sp := (x, make_term (Var x')) :: !sp;
              l,x',t,Utils.may s v
            ) p
        in
        let v = substs !sp v in
        let ss = !ss in
        let v = s ~ss v in
        (* TODO: alpha-convert vars too? *)
        Fun (vars,p,v)
      | App (a,l) ->
        let a = s a in
        let l = List.map (fun (l,v) -> l, s v) l in
        App (a,l)
  in
  make_term ~t:tm.t term

and subst x v tm = substs [x,v] tm

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
        let applied = List.may_map (fun (x,(_,v)) -> try Some (x,term_of_value v) with _ -> None) applied in
        let venv = List.may_map (fun (x,(_,v)) -> try Some (x,term_of_value v) with _ -> None) venv in
        let venv = applied@venv in
        let t = substs venv t in
        (* TODO: fill vars? *)
        Fun (V.Vars.empty, params, t)
      | V.V.Float f -> Float f
  in
  make_term term

(* TODO: shall we beta-convert when we reduce under lets? *)
let rec reduce tm =
  (* Printf.printf "reduce: %s\n%!" (V.print_term tm); *)
  let merge s1 s2 = s1@s2 in
  let mk tm' = { term = tm'; t = tm.t } in
  match tm.term with
    | Var _ | Unit | Bool _ | Int _ | String _ | Float _ -> [], tm
    | Let l ->
      if
        (
          (match (T.deref l.def.t).T.descr with T.Arrow _ | T.Record _ -> true | _ -> false)
          || occurences l.var l.body <= 1
        ) && not (List.mem l.var !meta_vars)
      then
        let sdef, def = reduce l.def in
        let body = subst l.var def l.body in
        let sbody, body = reduce body in
        merge sdef sbody, body
      else
        let sdef, def = reduce l.def in
        let sbody, body = reduce l.body in
        let l = { l with def = def; body = body } in
        merge sdef sbody, mk (Let l)
    | Ref v ->
      let sv, v = reduce v in
      let x = fresh_ref () in
      merge [x,v] sv, mk (Var x)
    | Get r ->
      let sr, r = reduce r in
      sr, mk (Get r)
    | Set (r,v) ->
      let sr, r = reduce r in
      let sv, v = reduce v in
      merge sr sv, mk (Set (r, v))
    | Seq (a, b) ->
      let sa, a = reduce a in
      let sb, b = reduce b in
      let tm =
        let rec aux a =
          match a.term with
            | Unit -> b
            | Let l -> mk (Let { l with body = aux l.body })
            | _ -> mk (Seq (a, b))
        in
        aux a
      in
      merge sa sb, tm
    | Record r ->
      (* Records get lazily evaluated in order not to generate variables for
         the whole standard library. *)
      [], tm
    (*
      let sr = ref [] in
      let r =
      T.Fields.map
      (fun v ->
      let s, v' = reduce v.rval in
      sr := merge !sr s;
      { v with rval = v' }
      ) r
      in
      !sr, Record r
    *)
    | Field (r,x,o) ->
      let sr, r = reduce r in
      let sr = ref sr in
      let tm =
        let rec aux r =
          (* Printf.printf "aux field (%s): %s\n%!" x (print_term r); *)
          match r.term with
            | Record r ->
              (* TODO: use o *)
              let s, v = reduce (T.Fields.find x r).rval in
              sr := merge s !sr;
              v
            | Let l ->
              mk (Let { l with body = aux l.body })
        in
        aux r
      in
      !sr, tm
    | Fun (vars, args, v) ->
      let sv, v = reduce v in
      sv, mk (Fun (vars, args, v))
    | App (f,a) ->
      let sf, f = reduce f in
      let sa, a =
        let sa = ref [] in
        let ans = ref [] in
        List.iter
          (fun (l,v) ->
            let sv, v = reduce v in
            sa := merge !sa sv;
            ans := (l,v) :: !ans
          ) a;
        !sa, List.rev !ans
      in
      let tm =
        let rec aux f =
          (* Printf.printf "aux app: %s\n%!" (print_term f); *)
          match f.term with
            | Fun (vars, args, v) ->
              let args = List.map (fun (l,x,t,v) -> l,(x,t,v)) args in
              let args = ref args in
              let v = ref v in
              let reduce_args a =
                List.iter
                  (fun (l,va) ->
                    let x,_,_ = List.assoc l !args in
                    args := List.remove_assoc l !args;
                    v := subst x va !v
                  ) a
              in
              reduce_args a;
              let args = List.map (fun (l,(x,t,v)) -> l,x,t,v) !args in
              if args = [] then
                beta_reduce !v
              else if List.for_all (fun (_,_,_,v) -> v <> None) args then
                let a = List.map (fun (l,_,_,v) -> l, Utils.get_some v) args in
                reduce_args a;
                beta_reduce !v
              else
                mk (Fun (vars, args, !v))
            | Let l ->
              mk (Let { l with body = aux l.body })
            | Var _ ->
              mk (App (f, a))
        in
        aux f
      in
      merge sf sa, tm

and beta_reduce tm =
  let r, tm = reduce tm in
  assert (r = []);
  tm

let rec emit_type t =
  (* Printf.printf "emit_type: %s\n%!" (T.print t); *)
  match (T.deref t).T.descr with
    | T.Ground T.Unit -> B.T.Void
    | T.Ground T.Bool -> B.T.Bool
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
    | Bool b -> [B.Bool b]
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
        (* Printf.printf "emit_prog app: %s\n%!" (print_term (make_term x)); *)
        match x with
          | Var x when Str.string_match builtin_prefix_re x 0 ->
            let x =
              let bpl = String.length builtin_prefix in
              String.sub x bpl (String.length x - bpl)
            in
            (
              match x with
                | "if_then_else" ->
                  let br v = beta_reduce (make_term (App (v, []))) in
                  let p = List.assoc "" l in
                  let p1 = br (List.assoc "then" l) in
                  let p2 = br (List.assoc "else" l) in
                  let p, p1, p2 = emit_prog p, emit_prog p1, emit_prog p2 in
                  [ B.If (p, p1, p2)]
                | _ ->
                  let l = List.map (fun (l,v) -> assert (l = ""); emit_prog v) l in
                  let l = Array.of_list l in
                  let op =
                    match x with
                      (* TODO: handle integer operations *)
                      | "add" -> B.FAdd
                      | "sub" -> B.FSub
                      | "mul" -> B.FMul
                      | "div" -> B.FDiv
                      | "mod" -> B.FRem
                      | "lt" -> B.FLt
                      | _ -> B.Call x
                  in
                  [B.Op (op, l)]
            )
          | _ -> Printf.printf "app: %s(...)" (print_term (make_term x)); assert false
      )
    | Field (r,x,_) ->
      (* Records are always passed by reference. *)
      [B.Field ([B.Load (emit_prog r)], x)]
    | Let l -> (B.Let (l.var, emit_prog l.def))::(emit_prog l.body)
    | Unit -> []
    | Int n -> [B.Int n]
    | Fun _ -> assert false
    | Record _ ->
      (* We should not emit records since they are lazily evaluated (or
         evaluation should be forced somehow). *)
      assert false
    | Replace_field _ | Open _ -> assert false

(** Emit a prog which might start by decls (toplevel lets). *)
let rec emit_decl_prog tm =
  (* Printf.printf "emit_decl_prog: %s\n%!" (print_term tm); *)
  match tm.term with
    | Let l when (match (T.deref l.def.t).T.descr with T.Arrow _ -> true | _ -> false) ->
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
            let def =
              let args = List.map (fun (x, _) -> "", make_term (Var x)) args in
              let def = make_term (App (l.def, args)) in
              let _, def = reduce def in
              def
            in
            let d = B.Decl (proto, emit_prog def) in
            let dd, p = emit_decl_prog l.body in
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

let emit name ?(keep_let=[]) ~env ~venv tm =
  meta_vars := keep_let @ default_meta_vars;
  Printf.printf "emit: %s : %s\n\n%!" (V.print_term tm) (T.print tm.t);
  let venv = List.may_map (fun (x,v) -> try Some (x, term_of_value v) with _ -> None) venv in
  let env = env@venv in
  (* Printf.printf "env: %s\n%!" (String.concat " " (List.map fst env)); *)
  let prog = substs env tm in
  Printf.printf "closed term: %s\n\n%!" (V.print_term prog);
  let refs, prog = reduce prog in
  Printf.printf "reduced: %s\n\n%!" (V.print_term prog);

  (* Compute the state. *)
  let refs_t = List.map (fun (x,v) -> x, emit_type v.V.t) refs in
  let refs = List.map (fun (x,v) -> x, emit_prog v) refs in
  let state_t = B.T.Struct refs_t in
  let state_decl = B.Decl_type ("saml_state", state_t) in

  (* Emit the program. *)
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
        | decl -> decl
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

  let ans = state_decl::reset::alloc::free::decls in
  Printf.printf "emitted:\n%s\n\n%!" (B.print_decls ans);
  ans
