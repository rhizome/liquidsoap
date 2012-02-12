(** "Values", as manipulated by SAML. *)

open Utils.Stdlib
open Lang_values

module B = Saml_backend

module List = struct
  include List

  let rec assoc4 x = function
    | (y,a,b,c)::_ when x = y -> a,b,c
    | _::l -> assoc4 x l
    | [] -> raise Not_found

  let rec remove_first_assoc4 x = function
    | (y,_,_,_)::l when x = y -> l
    | u::l -> u::(remove_first_assoc4 x l)
    | [] -> []

  let rec remove_first_assoc23 x = function
    | (_,y,_)::l when x = y -> l
    | u::l -> u::(remove_first_assoc23 x l)
    | [] -> []
end

(* Builtins are handled as variables, a special prefix is added to recognize
   them. *)
let builtin_prefix = "#saml_"
let builtin_prefix_re = Str.regexp ("^"^builtin_prefix)
let is_builtin_var x = Str.string_match builtin_prefix_re x 0
let remove_builtin_prefix x =
  let bpl = String.length builtin_prefix in
  String.sub x bpl (String.length x - bpl)
let event_builtins = ["event.channel"; "event.channeled"; "event.emit"; "event.handle"]

(* We add some helper functions. *)
module Lang_types = struct
  include Lang_types

  let fresh_evar () = fresh_evar ~level:(-1) ~pos:None

  let unit = make (Ground Unit)

  let bool = make (Ground Bool)

  let float = make (Ground Float)

  let event t = make (Constr { name = "event" ; params = [Invariant,t] })

  let event_type t =
    match (T.deref t).descr with
      | Constr { name = "event" ; params = [_, t] } -> t
      | _ -> assert false

  let ref t = Lang_values.ref_t ~pos:None ~level:(-1) t

  let is_unit t =
    match (T.deref t).T.descr with
      | Ground Unit -> true
      | _ -> false

  let is_evar t =
    match (T.deref t).T.descr with
      | EVar _ -> true
      | _ -> false

  let is_ref t =
    match (T.deref t).T.descr with
      | Constr { name = "ref" ; params = [_, t] } -> true
      | _ -> false

  let is_event t =
    match (T.deref t).T.descr with
      | Constr { name = "event" ; params = [_, t] } -> true
      | _ -> false
end

module T = Lang_types

module V = struct
  include Lang_values

  let make ~t term = { term = term ; t = t }

  let print ?(no_records=true) = print_term ~no_records
  let to_string = print

  let unit = make ~t:Lang_types.unit Unit

  let bool b = make ~t:Lang_types.bool (Bool b)

  let var ~t x = make ~t (Var x)

  let seq ?t a b =
    let t =
      match t with
        | None -> b.t
        | Some t -> t
    in
    make ~t (Seq (a, b))

  let make_let ?t var def body =
    let l =
      {
        doc = (Doc.none (), []);
        var = var;
        gen = [];
        def = def;
        body = body;
      }
    in
    let t =
      match t with
        | None -> body.t
        | Some t -> t
    in
    make ~t (Let l)

  (** Conditional branching. *)
  let ite b t e =
    let tret =
      match (T.deref t.t).T.descr with
        | T.Arrow (_, t) -> t
        | _ -> assert false
    in
    let ite =
      let t_branch = T.make (T.Arrow ([], tret)) in
      let t = T.make (T.Arrow ([false,"",Lang_types.bool;false,"then",t_branch;false,"else",t_branch], tret)) in
      make ~t (Var (builtin_prefix ^ "if"))
    in
    make ~t:tret (App (ite, ["",b;"then",t;"else",e]))

  let ref v = make ~t:(Lang_types.ref v.t) (Ref v)

  let field ?t ?opt r x =
    let t =
      match t with
        | Some t -> t
        | None ->
          match (T.deref r.t).T.descr with
            | T.Record r -> snd (fst (T.Fields.find x r.T.fields))
            | _ -> assert false

    in
    make ~t (Field (r, x, opt))
end

type t = V.term

(** Variables that should not be alpha-converted. *)
let meta_vars = ["period"]

(** Variables that should be kept as declarations with unchanged name. *)
let keep_vars = ref []

let make_term ?t tm =
  let t =
    match t with
      | Some t -> t
      | None -> T.fresh_evar ()
  in
  V.make ~t tm

let make_var ?t x =
  make_term ?t (Var x)

(** Generate a fresh reference name. *)
let fresh_ref =
  let n = ref 0 in
  fun () ->
    incr n;
    Printf.sprintf "saml_ref%d" !n

(** Generate a fresh variable name. *)
let fresh_var =
  let n = ref 0 in
  fun () ->
    incr n;
    Printf.sprintf "saml_x%d" !n

(** Free variables of a term. *)
(* TODO: don't use lists (but we cannot use a set because we want to have the
   number of occurences too). *)
let rec free_vars tm =
  (* Printf.printf "free_vars: %s\n%!" (print_term tm); *)
  let fv = free_vars in
  let u v1 v2 = v1@v2 in
  let r xx v = List.diff v xx in
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

let rec is_simple tm =
  match tm.term with
    | Var _ | Unit | Bool _ | Int _ | String _ | Float _ -> true
    | _ -> false

let rec fresh_let fv l =
  let reserved = ["main"] in
  if List.mem l.var fv || List.mem l.var reserved then
    let var = fresh_var () in
    var, subst l.var (V.var ~t:l.def.t var) l.body
  else
    l.var, l.body

(** Apply a list of substitutions to a term. *)
(* TODO: improve this *)
and substs ss tm =
  (* Printf.printf "substs: %s\n%!" (V.print tm); *)
  let fv ss = List.fold_left (fun fv (_,v) -> (free_vars v)@fv) [] ss in
  let s = substs ss in
  let term =
    match tm.term with
      | Var x ->
        let rec aux = function
          | (x',v)::ss when x' = x ->
            let tm = if List.for_all (fun x -> not (List.mem_assoc x ss)) (free_vars v) then v else substs ss v in
            tm.term
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
        let var = l.var in
        let def = s l.def in
        let ss = List.remove_all_assoc var ss in
        (* TODO: precompute this *)
        let fv = fv ss in
        let var, ss =
          (* TODO: is this correct for keep_vars? *)
          if List.mem var (meta_vars @ !keep_vars) || not (List.mem var fv) then
            var, ss
          else
            let x = fresh_var () in
            x, (var, V.var ~t:def.t x)::ss
        in
        let body = substs ss l.body in
        let l = { l with var = var; def = def; body = body } in
        Let l
      | Fun (_,p,v) ->
        let ss = ref ss in
        let sp = ref [] in
        let p =
          List.map
            (fun (l,x,t,v) ->
              let x' = if List.mem x (fv !ss) then fresh_var () else x in
              ss := List.remove_all_assoc x !ss;
              if x <> x' then sp := (x, make_term (Var x')) :: !sp;
              l,x',t,Utils.may s v
            ) p
        in
        let v = substs !sp v in
        let ss = !ss in
        let v = substs ss v in
        Fun (Vars.empty,p,v)
      | App (a,l) ->
        let a = s a in
        let l = List.map (fun (l,v) -> l, s v) l in
        App (a,l)
  in
  V.make ~t:tm.t term

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
                | Failure _ -> ()
                | e ->
                  Printf.printf "term_of_value: ignoring %s = %s (%s).\n" x (V.V.print_value v.V.V.v_value) (Printexc.to_string e);
                  ()
            ) r;
          !ans
        in
        Record r
      | V.V.FFI ffi ->
        (
          match ffi.V.V.ffi_external with
            | Some x ->
              (* TODO: regexp *)
              if List.mem x event_builtins then
                Var x
              else
                Var (builtin_prefix^x)
            | None -> failwith "TODO: don't know how to emit code for this operation"
        )
      | V.V.Fun (params, applied, venv, t) ->
        let params = List.map (fun (l,x,v) -> l,x,T.fresh_evar (),Utils.may term_of_value v) params in
        let applied = List.may_map (fun (x,(_,v)) -> try Some (x,term_of_value v) with _ -> None) applied in
        let venv = List.may_map (fun (x,(_,v)) -> try Some (x,term_of_value v) with _ -> None) venv in
        let venv = applied@venv in
        let t = substs venv t in
        (* TODO: fill vars? *)
        Fun (V.Vars.empty, params, t)
      | V.V.Unit -> Unit
      | V.V.Product (a, b) -> Product (term_of_value a, term_of_value b)
      | V.V.Ref a -> Ref (term_of_value !a)
      | V.V.Int n -> Int n
      | V.V.Float f -> Float f
      | V.V.Bool b -> Bool b
      | V.V.String s -> String s
  in
  V.make ~t:v.V.V.t term

let rec is_value ~env tm =
  (* Printf.printf "is_value: %s\n%!" (print_term tm); *)
  let is_value ?(env=env) = is_value ~env in
  match tm.term with
    | Var _ | Unit | Bool _ | Int _ | String _ | Float _ -> true
    (* TODO: handle more cases, for instance: let x = ... in 3 *)
    | _ ->  false

type state =
    {
      (** References together with their initial value. *)
      refs : (string * term) list;
      (** List of event variables together with the currently known
          handlers. These have to be reset after each round. *)
      events : (string * term list) list;
    }

let empty_state = { refs = []; events = [] }

(** Raised by "Liquidsoap" implementations of functions when no reduction is
    possible. *)
exception Cannot_reduce

(** Functions to reduce some builtins. *)
let builtin_reducers = ref
  [
    "add",
    (fun args ->
      match args.(0).term, args.(1).term with
        | Float x, Float y -> V.make ~t:T.float (Float (x+.y))
        | Float 0., _ -> args.(1)
        | _, Float 0. -> args.(0)
        | _ -> raise Cannot_reduce
    );
    "sub",
    (fun args ->
      match args.(0).term, args.(1).term with
        | Float x, Float y -> V.make ~t:T.float (Float (x-.y))
        | _, Float 0. -> args.(0)
        | _ -> raise Cannot_reduce
    );
    "mul",
    (fun args ->
      match args.(0).term, args.(1).term with
        | Float x, Float y -> V.make ~t:T.float (Float (x*.y))
        | Float 1., _ -> args.(1)
        | _, Float 1. -> args.(0)
        | _ -> raise Cannot_reduce
    );
    "and",
    (fun args ->
      match args.(0).term, args.(1).term with
        | Bool x, Bool y -> V.make ~t:T.bool (Bool (x && y))
        | Bool true, _ -> args.(1)
        | _, Bool true -> args.(0)
        | Bool false, _ -> V.make ~t:T.bool (Bool false)
        | _, Bool false -> V.make ~t:T.bool (Bool false)
        | _ -> raise Cannot_reduce
    );
    "if",
      (fun args ->
      match args.(0).term, args.(1).term, args.(2).term with
        | Bool true, _, _ -> make_term (App(args.(1), []))
        | Bool false, _, _ -> make_term (App(args.(2), []))
        | _, a, b when a = b -> make_term (App(args.(1), []))
        | _ -> raise Cannot_reduce
    );
  ]

(* TODO: compute references which are read and/or written to optimize them +
   propagate their value when we can *)
let rec reduce ?(events=false) ?(state=empty_state) tm =
  (* Printf.printf "reduce: %s\n%!" (V.print tm); *)
  (* Printf.printf "reduce: %s : %s\n%!" (V.print tm) (T.print tm.t); *)
  let reduce ~state tm = reduce ~events ~state tm in
  let add_handlers s e h =
    if List.mem_assoc e s.events then
      let h' = List.assoc e s.events in
      let events = List.remove_assoc e s.events in
      { s with events = (e,h@h')::events }
    else
      { s with events = (e,h)::s.events }
  in
  let mk ?(t=tm.t) = V.make ~t in
  let reduce_list ~state l =
    let state = ref state in
    let l = List.map (fun v -> let s, v = reduce ~state:!state v in state := s; v) l in
    !state, l
  in
  let s, term =
    match tm.term with
      | Var "event.channel" when events ->
        let t =
          match (T.deref tm.t).T.descr with
            | T.Arrow (_, t) -> T.event_type t
            | _ -> Printf.printf "Unexpected type: %s\n%!" (T.print tm.t); assert false
        in
        (* We impose that channels with unknown types carry unit values. *)
        if T.is_evar t then (T.deref t).T.descr <- T.Ground (T.Unit);
        (* TODO: otherwise have another ref for the value *)
        assert (T.is_unit t);
        let s, e = reduce ~state:empty_state (V.ref (V.bool false)) in
        let state =
          match s.refs with
            | [x,v] -> { state with refs = (x,v)::state.refs; events = (x,[])::state.events }
            | _ -> assert false
        in
        state, mk (Fun (Vars.empty, [], e))
      (* Hack in order for Liquidsoap reduction to work. *)
      | Var "event.channeled" when events ->
        let t = tm.t in
        let t = T.make (T.Arrow([],t)) in
        reduce ~state (mk ~t:T.unit (App (mk ~t (Var "event.channel"), [])))
      | Var _ | Unit | Bool _ | Int _ | String _ | Float _ -> state, tm
      | Let l ->
        let state, def = reduce ~state l.def in
        if T.is_ref l.def.t || (events && T.is_event l.def.t) || (
          (match (T.deref l.def.t).T.descr with
            | T.Arrow _ | T.Record _ -> true
            | _ -> (* is_value ~env l.def *) false
          ) || (
            let o = occurences l.var l.body in
            o = 0
           ) || is_simple l.def
        )
          (* We can rename meta-variables here because we are in weak-head
             reduction, so we know that any value using the meta-variable below
             will already be substituted. However, we have to keep the variables
             defined by lets that we want to keep. *)
          && not (List.mem l.var !keep_vars)
        then
          let var = l.var in
          let body = l.body in
          let rec aux ~state def =
            (* Printf.printf "aux let: %s\n%!" (V.to_string def); *)
            match def.term with
              | Seq (a,b) ->
                let state, b = aux ~state b in
                state, mk (Seq (a, b))
              | Let l ->
                (* M[let x = A in B/y] -> let x = A in M[B/y] *)
                let var, body = fresh_let (free_vars body) l in
                let state, body = aux ~state body in
                state, V.make_let var l.def body
              | _ ->
                let body = subst var def body in
                reduce ~state body
          in
          aux ~state def
        (* let body = subst l.var def l.body in *)
        (* let state, body = reduce ~state body in *)
        (* state, body.term *)
        else
          let state, body = reduce ~state l.body in
          state, (V.make_let l.var def body)
      | Ref v ->
        let state, v = reduce ~state v in
        let x = fresh_ref () in
        { state with refs = (x,v)::state.refs }, mk (Var x)
      | Get r ->
        let state, r = reduce ~state r in
        state, mk (Get r)
      | Set (r,v) ->
        let state, r = reduce ~state r in
        let state, v = reduce ~state v in
        state, mk (Set (r, v))
      | Seq (a, b) ->
        let state, b = reduce ~state b in
        let state, a = reduce ~state a in
        let rec aux ~state a =
          match a.term with
            | Unit -> state, b
            | _ -> state, mk (Seq (a, b))
        in
        aux ~state a
      (*
        let tm =
        let rec aux a =
        match a.term with
        | Unit -> b
        | Let l ->
        let var, body = fresh_let (free_vars b) l in
        mk (Let { l with var = var; body = aux body })
        | _ -> mk (Seq (a, b))
        in
        (aux a).term
        in
        state, tm
      *)
      | Record r ->
        (* Records get lazily evaluated in order not to generate variables for
           the whole standard library. *)
        state, tm
      | Field (r,x,o) ->
        let state, r = reduce ~state r in
        let rec aux ~state r =
          (* Printf.printf "aux field (%s): %s\n%!" x (print_term r); *)
          match r.term with
            | Record r ->
              (* TODO: use o *)
              reduce ~state (try T.Fields.find x r with Not_found -> failwith (Printf.sprintf "Field %s not found" x)).rval
            | Let l ->
              let fv = match o with Some o -> free_vars o | None -> [] in
              let var, body = fresh_let fv l in
              let state, body = aux ~state body in
              state, mk (Let { l with var = var ; body = body })
            | Seq (a, b) ->
              let state, b = aux ~state b in
              state, mk (Seq (a, b))
        in
        aux ~state r
      | Fun (vars, args, v) ->
        if events then
          let state, v = reduce ~state v in
          state, mk (Fun (vars, args, v))
        else
          (* We have to use weak head reduction because some refs might use the
             arguments, e.g. fun (x) -> ref x. However, we need to reduce toplevel
             declarations... *)
          state, tm
      | App (f,a) ->
        let state, f = reduce ~state f in
        let state, a =
          List.fold_map
            (fun state (l,v) ->
              let state, v = reduce ~state v in
              state, (l, v)
            ) state a
        in
        let rec aux ~state f =
          (* Printf.printf "aux app: %s\n%!" (print_term f); *)
          (* Printf.printf "aux app args: %s\n\n%!" (String.concat "," (List.map (fun (l,a) -> Printf.sprintf "%s:%s" l (V.to_string a)) a)); *)
          match f.term with
            | Fun (vars, args, v) ->
              (
                match a with
                  | (l,va)::a ->
                    let x,_,_ = List.assoc4 l args in
                    let args = List.remove_first_assoc4 l args in
                    let body_t =
                      let f_t = T.deref (f.t) in
                      match f_t.T.descr with
                        | T.Arrow (a,t) -> { f_t with T.descr = T.Arrow (List.remove_first_assoc23 l a,t) }
                        | _ -> assert false
                    in
                    let body = mk (App (V.make ~t:body_t (Fun (vars, args, v)), a)) in
                    let v = V.make_let x va body in
                    (* TODO: one reduce should be enough for multiple arguments... *)
                    reduce ~state v
                  | [] ->
                    if args = [] then
                      (* We had all the arguments. *)
                      reduce ~state v
                    else if List.for_all (fun (_,_,_,v) -> v <> None) args then
                      (* We only have optional arguments left. *)
                      let state, a =
                        List.fold_map
                          (fun state (l,_,_,v) ->
                            let v = Utils.get_some v in
                            (* Printf.printf "optional arg: %s\n%!" (print_term v); *)
                            let state, v = reduce ~state v in
                            state, (l, v)
                          ) state args
                      in
                      reduce ~state (mk (App (f, a)))
                    else
                      state, f
              )
            (*
              | Let l ->
              let fv = List.fold_left (fun fv (_,v) -> (free_vars v)@fv) [] a in
              let var, body = fresh_let fv l in
              let state, body = aux ~state body in
              state, mk (Let { l with var = var ; body = body })
              | Seq (a, b) ->
              let state, b = aux ~state b in
              state, mk (Seq (a, b))
            *)
            | Var "event.handle" when events ->
              let e, h =
                match a with
                  | ["", e; "", h] -> e, h
                  | _ -> (* TODO *) assert false
              in
              let h = beta_reduce h in
              let ex =
                match e.term with
                  | Var x -> x
                  | _ -> assert false
              in
              let state = add_handlers state ex [h] in
              let te, th =
                match (T.deref f.t).T.descr with
                  | T.Arrow ([_,_,te;_,_,th], _) -> te, th
                  | _ -> assert false
              in
              let te' = T.event_type te in
              if T.is_evar te' then (T.deref te').T.descr <- T.Ground (T.Unit);
              if not (T.is_unit te') then (Printf.printf "TODO: handle %s events\n%!" (T.print te'); assert false);
              let b = V.make ~t:T.bool (Get e) in
              let t_branch = T.make (T.Arrow ([], T.unit)) in
              let t =
                V.make ~t:t_branch
                  (Fun (Vars.empty, [], V.make ~t:T.unit (App (h, ["",V.unit]))))
              in
              let e = V.make ~t:t_branch (Fun (Vars.empty, [], V.unit)) in
              reduce ~state (V.ite b t e)
            | Var "event.emit" when events ->
              let e, v =
                match a with
                  | ["", e; "", v] -> e, v
                  | _ -> assert false
              in
              let ex =
                match e.term with
                  | Var x -> x
                  | _ -> assert false
              in
              let t =
                match (T.deref f.t).T.descr with
                  | T.Arrow ([_;_,_,t], _) -> t
                  | _ -> assert false
              in
              assert (T.is_unit t); (* TODO *)
              (* TODO: we should use a let for v and not evaluate it for each
                 handler. *)
              (* Printf.printf "se %s: %s\n%!" ex (String.concat " " (List.map fst state.events)); *)
              let handlers = List.assoc ex state.events in
              (* Printf.printf "emit %s: %d handlers\n\n%!" (V.print e) (List.length handlers); *)
              let handlers = List.rev handlers in
              let handlers = List.map (fun h -> V.make ~t:T.unit (App(h,["",v]))) handlers in
              let set = V.make ~t:T.unit (Set (e, V.bool true)) in
              let ans =
                let rec aux = function
                  | [] -> V.unit
                  | [v] -> v
                  | v::vv -> V.make ~t:T.unit (Seq (v, aux vv))
                in
                aux (handlers@[set])
              in
              reduce ~state ans
            | Var x ->
              (* TODO: extrude *)
              let state, a =
                List.fold_map
                  (fun state (l,v) ->
                    let state, v = reduce ~state v in
                    state, (l, v)
                  ) state a
              in
              (
                try
                  if is_builtin_var x then
                    let x = remove_builtin_prefix x in
                    let r = List.assoc x !builtin_reducers in
                    let state, a =
                      if x = "if" then
                        let b = List.assoc "" a in
                        let t = List.assoc "then" a in
                        let e =  List.assoc "else" a in
                        (* We have to reduce inside the then and the else so
                           that we can extrude references, which we can do since
                           we know that it won't be reduced further. *)
                        let inner_reduce ~state e =
                          match e.term with
                            | Fun (vars, [], v) ->
                              let state, v = reduce ~state v in
                              state, V.make ~t:e.t (Fun(vars, [], v))
                            | _ -> assert false
                        in
                        let state, t = inner_reduce ~state t in
                        let state, e = inner_reduce ~state e in
                        state, [|b; t; e|]
                      else
                        let a = List.map (fun (l,v) -> assert (l = ""); v) a in
                        state, Array.of_list a
                    in
                    reduce ~state (r a)
                  else
                    raise Cannot_reduce
                with
                  | Not_found
                  | Cannot_reduce ->
                    state, mk (App (f, a))
              )
        in
        aux ~state f
  in
  (* Printf.printf "reduce: %s => %s\n%!" (V.print tm) (V.print (mk term)); *)
  (* We have to preserve types (this is needed because some types might be
     instanciated e.g. id 3). *)
  s, { term with t = tm.t }

and beta_reduce tm =
  (* Printf.printf "beta_reduce: %s\n%!" (V.print tm); *)
  let r, tm = reduce tm in
  assert (r = empty_state);
  tm

(* Ensure that kept lets are at toplevel: this handles situations such as let x
   = ... in let set_velocity = ... in .... *)
let rec top_let tm =
  let rec has_kept tm =
    match tm.term with
      | Let l -> List.mem l.var !keep_vars || has_kept l.body
      | _ -> false
  in
  match tm.term with
    | Let l when T.is_event l.def.t ->
      (* We don't want to substitute let x = event.create () in ... *)
      V.make ~t:tm.t (Let { l with body = top_let l.body })
    | Let l when not (List.mem l.var !keep_vars) && has_kept l.body ->
      let v = subst l.var l.def l.body in
      top_let v
    | _ ->
      beta_reduce tm

let rec emit_type t =
  (* Printf.printf "emit_type: %s\n%!" (T.print t); *)
  match (T.deref t).T.descr with
    | T.Ground T.Unit -> B.T.Void
    | T.Ground T.Bool -> B.T.Bool
    | T.Ground T.Float -> B.T.Float
    | T.Ground T.Int -> B.T.Int
    | T.Constr { T.name = "ref"; params = [_,t] }
    | T.Constr { T.name = "event"; params = [_,t] } -> B.T.Ptr (emit_type t)
    | T.Arrow (args, t) ->
      let args = List.map (fun (o,l,t) -> assert (not o); assert (l = ""); emit_type t) args in
      B.T.Arr (args, emit_type t)
    | T.EVar _ -> assert false; failwith "Cannot emit programs with universal types"

let rec emit_prog tm =
  (* Printf.printf "emit_prog: %s\n%!" (V.print tm); *)
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
      (* let tmp = fresh_ref () in *)
      (* [B.Let (tmp, [B.Alloc (emit_type r.t)]); B.Store ([B.Ident tmp], emit_prog r); B.Ident tmp] *)
      assert false
    | Get r -> [B.Load (emit_prog r)]
    | Set (r,v) -> [B.Store (emit_prog r, emit_prog v)]
    | Seq (a,b) -> (emit_prog a)@(emit_prog b)
    | App _ ->
      let x, l = focalize_app tm in
      (
        (* Printf.printf "emit_prog app: %s\n%!" (print_term (make_term x)); *)
        match x with
          | Var x when is_builtin_var x ->
            let x = remove_builtin_prefix x in
            (
              match x with
                | "if" ->
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
                      | "mod" -> B.FMod
                      | "eq" -> B.FEq
                      | "lt" -> B.FLt
                      | "ge" -> B.FGe
                      | "and" -> B.BAnd
                      | "or" -> B.BOr
                      | _ -> B.Call x
                  in
                  [B.Op (op, l)]
            )
          | _ -> Printf.printf "unhandled app: %s(...)\n%!" (V.print (make_term x)); assert false
      )
    | Field (r,x,_) ->
      (* Records are always passed by reference. *)
      [B.Field ([B.Load (emit_prog r)], x)]
    | Let l ->
      (B.Let (l.var, emit_prog l.def))::(emit_prog l.body)
    | Unit -> []
    | Int n -> [B.Int n]
    | Fun _ -> failwith "Trying to emit a function, this should not happen."
    | Record _ ->
      (* We should not emit records since they are lazily evaluated (or
         evaluation should be forced somehow). *)
      assert false
    | Replace_field _ | Open _ -> assert false

(** Emit a prog which might start by decls (toplevel lets). *)
let rec emit_decl_prog tm =
  (* Printf.printf "emit_decl_prog: %s\n%!" (print_term tm); *)
  match tm.term with
    (* Hack to keep top-level declarations that we might need. We should
       explicitly flag them instead of keeping them all... *)
    | Let l when (match (T.deref l.def.t).T.descr with T.Arrow _ -> true | _ -> false) ->
      Printf.printf "def: %s = %s : %s\n%!" l.var (print_term l.def) (T.print l.def.t);
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
              beta_reduce def
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
    | _ ->
      Printf.printf "prg: %s\n%!" (print_term tm);
      [], emit_prog tm

let emit name ?(keep_let=[]) ~env ~venv tm =
  keep_vars := keep_let;
  Printf.printf "emit: %s : %s\n\n%!" (V.print_term ~no_records:true tm) (T.print tm.t);
  (* Inline the environment. *)
  let venv =
    List.may_map
      (fun (x,v) ->
        try
          Some (x, term_of_value v)
        with
          | e ->
            (* Printf.printf "venv: ignoring %s = %s (%s).\n" x (V.V.print_value v) (Printexc.to_string e); *)
            None
      ) venv
  in
  let env = env@venv in
  (* Printf.printf "env: %s\n%!" (String.concat " " (List.map fst env)); *)
  let prog = tm in
  let prog = substs env prog in
  Printf.printf "closed term: %s\n\n%!" (V.print prog);
  (* Reduce the term and compute references. *)
  let state, prog = reduce prog in
  Printf.printf "reduced: %s\n\n%!" (V.print prog);
  (* Put definitions at toplevel. *)
  let prog = top_let prog in
  Printf.printf "top lets: %s\n\n%!" (V.to_string prog);
  (* Reduce events. *)
  let state = { empty_state with refs = state.refs } in (* TODO: is this useful? *)
  let state, prog = reduce ~events:true ~state prog in
  Printf.printf "evented: %s\n\n%!" (V.print prog);

  (* Compute the state. *)
  let refs = List.rev state.refs in
  let refs = refs in
  let refs_t = List.map (fun (x,v) -> x, emit_type v.V.t) refs in
  let refs_t = ("period", B.T.Float)::refs_t in
  let refs = List.map (fun (x,v) -> x, emit_prog v) refs in
  let state_t = B.T.Struct refs_t in
  let state_decl = B.Decl_type ("saml_state", state_t) in

  (* Emit the program. *)
  let decls, prog = emit_decl_prog prog in
  Printf.printf "\n\n";
  let prog =
    (* Reset the events. *)
    let e = List.map (fun (x,_) -> B.Store ([B.Ident x], [B.Bool false])) state.events in
    let rec aux = function
      | [x] -> e@[x]
      | x::xx -> x::(aux xx)
      | [] -> assert false
    in
    aux prog
  in
  let prog = B.Decl ((name, [], emit_type tm.t), prog) in
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
    let alias_period =
      let s = [B.Load [B.Ident "state"]] in
      let r = [B.Field(s,"period")] in
      B.Let ("period", r)
    in
    let alias_state = alias_period::alias_state in
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
