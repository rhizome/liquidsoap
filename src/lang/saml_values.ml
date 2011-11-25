(** "Values", as manipulated by SAML. *)

open Lang_values

module B = Saml_backend
module V = Lang_values
module T = Lang_types

type t = V.term

type stateful =
    {
      prog : term;
      refs : (string * term) list;
    }

let builtin_prefix = "#saml_"
let builtin_prefix_re = Str.regexp ("^"^builtin_prefix)

let meta_vars = ["now"; "period"]

let rec term_of_value v =
  let term =
    match v.V.V.value with
      | V.V.Record r ->
        let r = T.Fields.map (fun v -> { V.rgen = v.V.V.v_gen; V.rval = term_of_value v.V.V.v_value }) r in
        Record r
      | V.V.FFI ffi ->
        (
          match ffi.V.V.ffi_external with
            | Some x -> Var (builtin_prefix^x)
            | None -> failwith "TODO: don't know how to emit code for this operation"
        )
      | _ -> failwith (Printf.sprintf "term_of_value: %s\n%!" (V.V.print_value v))
  in
  { term = term; t = T.fresh_evar ~level:(-1) ~pos:None }

(** Reduce a term. *)
(* venv is an environment of values *)
let rec reduce ?(venv=[]) env tm =
  let reduce ?(venv=venv) = reduce ~venv in
  let term =
    match tm.term with
      | Var "now" | Var "period" -> tm.term
      | Var x ->
        (* TODO: have a look in venv if not found *)
        (
          try
            (List.assoc x env).term
          with
            | Not_found -> (term_of_value (List.assoc x venv)).term
        )
      | Unit | Bool _ | Int _ | String _ | Float _ | Encoder _ -> tm.term
      | Seq (a,b) ->
        let a = reduce env a in
        let b = reduce env b in
        (
          match a.term with
            | Unit -> b.term
            | _ -> Seq (a, b)
        )
      | Ref r -> Ref (reduce env r)
      | Get r -> Ref (reduce env r)
      | Set (r,v) -> Set (reduce env r, reduce env v)
      | Field (r,x,_) ->
        let r = reduce env r in
        let r =
          match r.term with
            | Record r -> r
            | _ -> assert false
        in
        (T.Fields.find x r).rval.term
      | App (a,l) ->
        let a = reduce env a in
        let l = List.map (fun (l,v) -> l, reduce env v) l in
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
              let env = l@env in
              let body = reduce env body in
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

(** Extract the state from a term. *)
(* TODO: this could be merged with reduce *)
let rec extract_state tm =
  let es = extract_state in
  match tm.term with
    | Var _ | Unit | Bool _ | Int _ | String _ | Float _ -> { prog = tm; refs = [] }

let rec emit_type t =
  (* Printf.printf "emit_type: %s\n%!" (T.print t); *)
  match (T.deref t).T.descr with
    | T.Ground T.Float -> B.T.Float

let rec emit_prog tm =
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
                | "mul" -> B.FMul
                | _ -> B.Call x
            in
            [B.Op (op, l)]
          | _ -> assert false
      )

let emit name tm =
  let prog = emit_prog tm in
  let state_t = B.T.Ptr (B.T.Struct ["x", B.T.Float]) in (* TODO *)
  [
    B.Decl ((name, ["state", state_t; "now",B.T.Float; "period",B.T.Float], emit_type tm.t), prog)
  ]
