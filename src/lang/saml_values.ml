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

let meta_vars = ["now"; "period"]

(** Reduce a term. *)
(* venv is an environment of values *)
let rec reduce ?(venv=[]) env tm =
  let reduce ?(venv=venv) = reduce ~venv in
  let term =
    match tm.term with
      | Var "now" | Var "period" -> tm.term
      | Var x ->
        (* TODO: have a look in venv if not found *)
        (try (List.assoc x env).term with Not_found -> assert false)
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
  in
  { tm with term = term }

(** Extract the state from a term. *)
(* TODO: this could be merged with reduce *)
let rec extract_state tm =
  let es = extract_state in
  let mk t = { tm with term = t } in
  match tm.term with
    | Var _ | Unit | Bool _ | Int _ | String _ | Float _ -> { prog = tm; refs = [] }

let rec emit_type t =
  (* Printf.printf "emit_type: %s\n%!" (T.print t); *)
  match (T.deref t).T.descr with
    | T.Ground T.Float -> B.T.Float

let rec emit_prog tm =
  match tm.term with
    | Float f -> [B.Float f]
    | Var x -> [B.Ident x]

let emit name tm =
  let prog = emit_prog tm in
  let state_t = B.T.Ptr (B.T.Struct ["x", B.T.Float]) in (* TODO *)
  [
    B.Decl ((name, ["state", state_t; "now",B.T.Float; "period",B.T.Float], emit_type tm.t), prog)
  ]
