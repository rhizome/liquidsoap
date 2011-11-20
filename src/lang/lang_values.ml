(****************************************************************************

  Liquidsoap, a programmable audio stream generator.
  Copyright 2003-2011 Savonet team

  This program is free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details, fully stated in the COPYING
  file at the root of the liquidsoap distribution.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

 *****************************************************************************)

let debug =
  try
    ignore (Sys.getenv "LIQUIDSOAP_DEBUG_LANG") ;
    true
  with
    | Not_found -> false

let errors_as_warnings = ref false

(** {1 Kinds}
  *
  * In a sense this could move to Lang_types, but I like to keep that
  * part free of some specificities of liquidsoap, as much as possible. *)

module T = Lang_types

let ref_t ~pos ~level t =
  T.make ~pos ~level
    (T.Constr { T.name = "ref" ; T.params = [T.Invariant,t] })

let zero_t = T.make T.Zero
let succ_t t = T.make (T.Succ t)
let variable_t = T.make T.Variable
let record_t ~level ~row fields = T.record ~level ~row ~opt_row:true fields

let rec type_of_int n = if n=0 then zero_t else succ_t (type_of_int (n-1))

(** A frame kind type is a purely abstract type representing a frame kind.
  * The parameters [audio,video,midi] are intended to be multiplicity types,
  * i.e. types of the form Succ*(Zero|Variable). *)
let frame_kind_t ?pos ?level audio video midi =
  T.make ?pos ?level
    (T.Constr { T.name = "stream_kind" ;
                T.params = [T.Covariant,audio;
                            T.Covariant,video;
                            T.Covariant,midi ] })
let of_frame_kind_t t = match (T.deref t).T.descr with
  | T.Constr { T.name="stream_kind" ; T.params=[_,audio;_,video;_,midi] } ->
      { Frame. audio=audio; video=video; midi=midi }
  | T.EVar (j,c) ->
      let audio = type_of_int (Lazy.force Frame.audio_channels) in
      let video = type_of_int (Lazy.force Frame.video_channels) in
      let midi = type_of_int (Lazy.force Frame.midi_channels) in
        T.bind t (frame_kind_t audio video midi) ;
        { Frame. audio=audio; video=video; midi=midi }
  | _ -> assert false

(** Type of audio formats that can encode frame of a given kind. *)
let format_t ?pos ?level k =
  T.make ?pos ?level
    (T.Constr { T.name = "format" ; T.params = [T.Covariant,k] })

(** Type of sources carrying frames of a given kind. *)
let source_t ?(active=false) ?pos ?level k =
  let name = if active then "active_source" else "source" in
    T.make ?pos ?level
      (T.Constr { T.name = name ; T.params = [T.Invariant,k] })
let of_source_t t = match (T.deref t).T.descr with
  | T.Constr { T.name = "source" ; T.params = [_,t] } -> t
  | T.Constr { T.name = "active_source" ; T.params = [_,t] } -> t
  | _ -> assert false

let request_t ?pos ?level k =
  T.make ?pos ?level
    (T.Constr { T.name = "request" ; T.params = [T.Invariant,k] })
let of_request_t t = match (T.deref t).T.descr with
  | T.Constr { T.name = "request" ; T.params = [_,t] } -> t
  | _ -> assert false

let rec type_of_mul ~pos ~level m =
  T.make ~pos ~level
    (match m with
       | Frame.Variable -> T.Variable
       | Frame.Zero -> T.Zero
       | Frame.Succ m -> T.Succ (type_of_mul ~pos ~level m))

let type_of_format ~pos ~level f =
  let kind = Encoder.kind_of_format f in
  let audio = type_of_mul ~pos ~level kind.Frame.audio in
  let video = type_of_mul ~pos ~level kind.Frame.video in
  let midi  = type_of_mul ~pos ~level kind.Frame.midi in
    format_t ~pos ~level (frame_kind_t ~pos ~level audio video midi)

(** {1 Terms}
  * The way we implement this mini-language is not very efficient.
  * It should not matter, since very little computation is done here.
  * It is mostly used for a single run on startup to build the sources,
  * and then sometimes for building transitions. Terms are small, no recursion
  * is possible.
  * In order to report informative errors, including runtime errors (invalid
  * values of a valid type given to a FF) we need to keep a complete AST
  * all the way long.
  * We actually don't need the types anymore after the static checking,
  * but I don't want to bother with stripping down to another datatype. *)

module Vars = Set.Make(String)

type term = { mutable t : T.t ; term : in_term }
and let_t = {
  doc : Doc.item * (string*string) list ;
  var : string ;
  mutable gen : (int*T.constraints) list ;
  def : term ;
  body : term
}
and field_t = {
  mutable rgen : (int*T.constraints) list ;
  rval : term
}
and in_term =
  | Unit
  | Bool    of bool
  | Int     of int
  | String  of string
  | Float   of float
  | Encoder of Encoder.format
  | List    of term list
  | Record  of field_t T.Fields.t
  | Field   of term * string * (term option)
  (* [Replace_field (r,x,v)] does the same thing as { r with x = v } in OCaml,
     excepting that [r] is set to the empty record if it was not previously
     defined. *)
  | Replace_field of term * string * field_t
  | Is_field of term * string
  | Product of term * term
  | Ref     of term
  | Get     of term
  | Set     of term * term
  | Let     of let_t
  | Var     of string
  | Seq     of term * term
  | App     of term * (string * term) list
  | Fun     of Vars.t *
      (string*string*T.t*term option) list *
      term
(* [fun ~l1:x1 .. ?li:(xi=defi) .. -> body] =
 * [Fun (V, [(l1,x1,None)..(li,xi,Some defi)..], body)]
 * The first component [V] is the list containing all
 * variables occurring in the function. It is used to
 * restrict the environment captured when a closure is
 * formed. *)

(* Only used for printing very simple functions. *)
let rec is_ground x = match x.term with
  | Unit | Bool _ | Int _ | Float _ | String _
  | Encoder _ -> true
  | Ref x -> is_ground x
  | _ -> false

(** Print terms, (almost) assuming they are in normal form. *)
let rec print_term v = match v.term with
  | Unit     -> "()"
  | Bool i   -> string_of_bool i
  | Int i    -> string_of_int i
  | Float f  -> string_of_float f
  | String s -> Printf.sprintf "%S" s
  | Encoder e -> Encoder.string_of_format e
  | List l ->
      "["^(String.concat ", " (List.map print_term l))^"]"
  | Record r ->
    "["^String.concat ", " 
        (T.Fields.fold 
          (fun _ t l -> print_term t.rval :: l) r [])^"]"
  | Product (a,b) ->
      Printf.sprintf "(%s,%s)" (print_term a) (print_term b)
  | Ref a ->
      Printf.sprintf "ref(%s)" (print_term a)
  | Fun (_,[],v) when is_ground v -> "{"^(print_term v)^"}"
  | Fun _ -> "<fun>"
  | Var s -> s
  | App (hd,tl) ->
      let tl =
        List.map
          (fun (lbl,v) -> (if lbl="" then "" else lbl^"=")^(print_term v))
          tl
      in
        (print_term hd)^"("^(String.concat "," tl)^")"
  | Let _ | Seq _ | Get _ | Set _ 
  | Field _ | Replace_field _ | Is_field _ -> assert false

let rec free_vars tm = match tm.term with
  | Unit | Bool _ | Int _ | String _ | Float _ | Encoder _ ->
      Vars.empty
  | Var x -> Vars.singleton x
  | Ref r | Get r | Field (r,_,_) -> free_vars r
  | Replace_field (r,_,v) -> Vars.union (free_vars r) (free_vars v.rval)
  | Is_field (r,_) -> free_vars r
  | Product (a,b) | Seq (a,b) | Set (a,b) ->
      Vars.union (free_vars a) (free_vars b)
  | List l ->
      List.fold_left (fun v t -> Vars.union v (free_vars t)) Vars.empty l
  | Record r ->
      T.Fields.fold (fun _ t v -> Vars.union v (free_vars t.rval)) r Vars.empty
  | App (hd,l) ->
      List.fold_left
        (fun v (_,t) -> Vars.union v (free_vars t))
        (free_vars hd)
        l
  | Fun (fv,_,_) ->
      fv
  | Let l ->
      Vars.union
        (free_vars l.def)
        (Vars.remove l.var (free_vars l.body))

let free_vars ?bound body =
  match bound with
    | None -> free_vars body
    | Some s ->
        List.fold_left (fun v x -> Vars.remove x v) (free_vars body) s

let can_ignore t =
  match (T.deref t).T.descr with
    | T.Ground T.Unit | T.Constr {T.name="active_source"} -> true
    | T.EVar _ -> true
    | _ -> false

let is_fun t =
  match (T.deref t).T.descr with
    | T.Arrow _ -> true | _ -> false

let is_source t =
  match (T.deref t).T.descr with
    | T.Constr {T.name="source"} -> true | _ -> false

(** Check that all let-bound variables are used.
  * No check is performed for variable arguments.
  * This cannot be done at parse-time (as for the computatin of the
  * free variables of functions) because we need types, as well as
  * the ability to distinguish toplevel and inner let-in terms. *)

exception Unused_variable of (string*Lexing.position)

let rec check_unused ~lib tm =
  let rec check ?(toplevel=false) v tm = match tm.term with
    | Var s -> Vars.remove s v
    | Unit | Bool _ | Int _ | String _ | Float _ | Encoder _ -> v
    | Ref r | Get r | Is_field (r,_) -> check v r
    | Field (r,_,o) -> 
       if o <> None then
         check (check v (Utils.get_some o)) r
       else
         check v r
    | Product (a,b) | Set (a,b) -> check (check v a) b
    | Seq (a,b) -> check ~toplevel (check v a) b
    | List l -> List.fold_left check v l
    | Record r -> T.Fields.fold (fun _ t v -> check v t.rval) r v
    | Replace_field (r,_,e) ->
        let v = check v r in
          check v e.rval
    | App (hd,l) ->
        let v = check v hd in
          List.fold_left (fun v (lbl,t) -> check v t) v l
    | Fun (fv,p,body) ->
        let v =
          List.fold_left
            (fun v -> function
               | (_,_,_,Some default) -> check v default
               | _ -> v)
            v p
        in
        let masked,v =
          let v0 = v in
            List.fold_left
              (fun (masked,v) (_,var,_,_) ->
                 if Vars.mem var v0 then
                   Vars.add var masked, v
                 else
                   masked, Vars.add var v)
              (Vars.empty, v) p
        in
        let v = check v body in
          (* Restore masked variables
           * The masking variables have been used but it does not count
           * for the ones they masked. *)
          Vars.union masked v
    | Let { var = s ; def = def ; body = body } ->
        let v = check v def in
        let mask = Vars.mem s v in
        let v = Vars.add s v in
        let v = check ~toplevel v body in
          begin
            (* Do not check for anything at toplevel in libraries *)
            if not (toplevel && lib) then
            (* Do we have an unused definition? *)
            if Vars.mem s v then
            (* There are exceptions: unit, active_source
             * and functions when at toplevel (sort of a lib situation...) *)
            if not (can_ignore def.t || (toplevel && is_fun def.t)) then
              let start_pos = fst (Utils.get_some tm.t.T.pos) in
                if !errors_as_warnings then
                  Printf.printf
                    "Warning: unused variable %s at %s.\n%!"
                    s (T.print_single_pos start_pos)
                else
                  raise (Unused_variable (s,start_pos))
          end ;
          if mask then Vars.add s v else v
  in
    (* Unused free variables may remain *)
    ignore (check ~toplevel:true Vars.empty tm)

(** Maps a function on all types occurring in a term.
  * Ignores variable generalizations. *)
let rec map_types f (gen:'a list) tm = match tm.term with
  | Unit | Bool _ | Int _ | String _ | Float _ | Encoder _ | Var _ ->
      { tm with t = f gen tm.t }
  | Ref r ->
      { t = f gen tm.t ;
        term = Ref (map_types f gen r) }
  | Get r ->
      { t = f gen tm.t ;
        term = Get (map_types f gen r) }
  | Product (a,b) ->
      { t = f gen tm.t ;
        term = Product (map_types f gen a, map_types f gen b) }
  | Seq (a,b) ->
      { t = f gen tm.t ;
        term = Seq (map_types f gen a, map_types f gen b) }
  | Set (a,b) ->
      { t = f gen tm.t ;
        term = Set (map_types f gen a, map_types f gen b) }
  | List l ->
      { t = f gen tm.t ;
        term = List (List.map (map_types f gen) l) }
  | Record r ->
      { t = f gen tm.t ;
        term = Record (T.Fields.map
                         (fun t ->
                            { t with rval = map_types f (t.rgen@gen) t.rval })
                         r) }
  | Field (r,x,o) ->
      { t = f gen tm.t ;
        term = Field (map_types f gen r, x, 
                      Utils.may (map_types f gen) o) }
  | Is_field (r,x) ->
      { t = f gen tm.t; 
        term = Is_field (map_types f gen r,x) }
  | Replace_field (r,x,v) ->
      { t = f gen tm.t ;
        term = Replace_field (map_types f gen r, x,
                              { v with rval = map_types f (v.rgen@gen) v.rval }) }
  | App (hd,l) ->
      { t = f gen tm.t ;
        term = App (map_types f gen hd,
                    List.map (fun (lbl,v) -> lbl, map_types f gen v) l) }
  | Fun (fv,p,v) ->
      let aux = 
        fun (lbl,var,t,tm) -> lbl, var, f gen t, Utils.may (map_types f gen) tm
      in
        { t = f gen tm.t ;
          term = Fun (fv, List.map aux p, map_types f gen v) }
  | Let l ->
      let gen' = l.gen@gen in
        { t = f gen tm.t ;
          term = Let { l with def = map_types f gen' l.def ;
                              body = map_types f gen l.body } }

(** Folds [f] over almost all types occurring in a term,
  * skipping as much as possible while still
  * guaranteeing that [f] will see all variables. *)
let rec fold_types f gen x tm = match tm.term with
  | Unit | Bool _ | Int _ | String _ | Float _ | Encoder _ | Var _ ->
      f gen x tm.t
  | List l ->
      List.fold_left (fun x tm -> fold_types f gen x tm) (f gen x tm.t) l
  | Record r ->
      T.Fields.fold
        (fun _ tm x -> fold_types f (tm.rgen@gen) x tm.rval)
        r
        (f gen x tm.t)
  (* In the next cases, don't care about tm.t, nothing "new" in it. *)
  | Ref r | Get r | Is_field (r,_) ->
      fold_types f gen x r
  | Field (r,_,o) ->
      if o <> None then
       fold_types f gen (fold_types f gen x (Utils.get_some o)) r
      else
       fold_types f gen x r
  | Replace_field (r,_,v) ->
      let x = fold_types f gen x r in
        fold_types f (v.rgen@gen) x (v.rval)
  | Product (a,b) | Seq (a,b) | Set (a,b) ->
      fold_types f gen (fold_types f gen x a) b
  | App (tm,l) ->
      let x = fold_types f gen x tm in
        List.fold_left (fun x (_,tm) -> fold_types f gen x tm) x l
  | Fun (_,p,v) ->
      fold_types f gen
        (List.fold_left
           (fun x -> function
              | (_,_,t,Some tm) ->
                  fold_types f gen (f gen x t) tm
              | (_,_,t,None) ->
                  f gen x t)
           x
           p)
        v
  | Let {gen=gen';def=def;body=body} ->
      let x = fold_types f (gen'@gen) x def in
        fold_types f gen x body

(** Values are normal forms of terms. *)
module V =
struct
  type value = { mutable t : T.t ; value : in_value }
  and full_env = (string * ((int*T.constraints)list*value)) list
  and in_value =
    | Unit
    | Bool    of bool
    | Int     of int
    | String  of string
    | Float   of float
    | Source  of Source.source
    | Request of Request.t
    | Encoder of Encoder.format
    | List    of value list
    | Record  of value T.Fields.t
    | Product of value * value
    | Ref     of value ref
    (** The first environment contains the parameters already passed
      * to the function. Next parameters will be inserted between that
      * and the second env which is part of the closure. *)
    | Fun     of (string * string * value option) list *
                 full_env * full_env * term
    (** For a foreign function only the arguments are visible,
      * the closure doesn't capture anything in the environment. *)
    | FFI     of (string * string * value option) list *
                 full_env * (full_env -> T.t -> value)

  type env = (string*value) list

  let rec print_value v = match v.value with
    | Unit     -> "()"
    | Bool i   -> string_of_bool i
    | Int i    -> string_of_int i
    | Float f  -> string_of_float f
    | String s -> Printf.sprintf "%S" s
    | Source s -> "<source>"
    | Request s -> "<request>"
    | Encoder e -> Encoder.string_of_format e
    | List l ->
        "["^(String.concat ", " (List.map print_value l))^"]"
    | Record r ->
        "["^(String.concat 
               ", " 
               (T.Fields.fold (fun x v l -> (x ^ " = " ^ print_value v) :: l) 
               r []))^"]"
    | Ref a ->
        Printf.sprintf "ref(%s)" (print_value !a)
    | Product (a,b) ->
        Printf.sprintf "(%s,%s)" (print_value a) (print_value b)
    | Fun ([],_,_,x) when is_ground x -> "{"^print_term x^"}"
    | Fun (l,_,_,x) when is_ground x -> 
        let f (label,_,value) =
          match label, value with
            | "",    None -> "_"
            | "",    Some v -> Printf.sprintf "_=%s" (print_value v)
            | label, Some v -> 
                Printf.sprintf "~%s=%s" label (print_value v)
            | label, None ->
                Printf.sprintf "~%s" label
        in
        let args = List.map f l in
        Printf.sprintf "fun (%s) -> %s" (String.concat "," args) (print_term x)
    | Fun _ | FFI _ -> "<fun>"

  let map_env f env = List.map (fun (s,(g,v)) -> s, (g, f v)) env

  let tm_map_types = map_types

  (** Map a function on all types occurring in a value. *)
  let rec map_types f gen v = match v.value with
    | Unit | Bool _ | Int _ | String _ | Float _ | Encoder _ ->
        { v with t = f gen v.t }
    | Product (a,b) ->
        { t = f gen v.t ;
          value = Product (map_types f gen a, map_types f gen b) }
    | List l ->
        { t = f gen v.t ;
          value = List (List.map (map_types f gen) l) }
    | Record r ->
        { t = f gen v.t ;
          value = Record (T.Fields.map (fun v -> map_types f gen v) r) }
    | Fun (p,applied,env,tm) ->
        let aux = function
          | lbl, var, None -> lbl, var, None
          | lbl, var, Some v -> lbl, var, Some (map_types f gen v)
        in
          { t = f gen v.t ;
            value = 
              Fun (List.map aux p,
                   map_env (map_types f gen) applied,
                   map_env (map_types f gen) env,
                   tm_map_types f gen tm) }
    | FFI (p,applied,ffi) ->
        let aux = function
          | lbl, var, None -> lbl, var, None
          | lbl, var, Some v -> lbl, var, Some (map_types f gen v)
        in
          { t = f gen v.t ;
            value = FFI (List.map aux p,
                         map_env (map_types f gen) applied,
                         ffi) }
    (* In the case on instantiate (currently the only use of map_types)
     * no type instantiation should occur in the following cases (f should
     * be the identity): one cannot change the type of such objects once
     * they are created. *)
    | Source s ->
        assert (f gen v.t = v.t) ;
        v
    | Request s ->
        assert (f gen v.t = v.t) ;
        v
    | Ref r ->
        assert (f gen v.t = v.t) ;
        r := map_types f gen !r ;
        v
end

(** {1 Built-in values and toplevel definitions} *)

let builtins : (T.cvar list * V.value) Plug.plug
  = Plug.create ~duplicates:false ~doc:"scripting values" "scripting values"

(** {1 Generalization}
  *
  * We perform ML-style generalization: when a value is pure enough, we
  * generalize (universally quantify) variables that have been introduced
  * during the typing of that variable (do not generalize variables that
  * belong to an outer term).
  *
  * Because we maintain types during evaluation, it does not suffice to
  * generalize the type of the whole term, but inner types need to be considered
  * as well, so that their variables are taken fresh in each run. *)

let rec value_restriction t = match t.term with
  | Var _ | Fun _ | Bool _ 
  | Float _ | Int _ | Is_field _ -> true
  | Record r -> 
      let r = Lang_types.list_of_fields r in
      List.for_all (fun (_,v) -> value_restriction v.rval) r
  | List l -> List.for_all value_restriction l
  | Product (a,b) -> value_restriction a && value_restriction b
  | _ -> false

let generalize ~level v =
  if value_restriction v then
    let f gen x t =
      let x' =
        T.filter_vars
          (function
             | { T.descr = T.EVar (i,c) ; level = l } ->
                 not (List.mem_assoc i x) &&
                 not (List.mem_assoc i gen) &&
                 l >= level
             | _ -> assert false)
          t
      in
        x'@x
    in
      fold_types f [] [] v, v.t
  else
    [], v.t

(* {1 Type checking/inference} *)

let (<:) = T.(<:)
let (>:) = T.(>:)

exception Unbound of T.pos option * string
exception Ignored of term

let raise_ignored e =
  if !errors_as_warnings then
    Printf.printf
      "Warning: ignored expression at %s.\n%!"
      (T.print_pos ~prefix:"" (Utils.get_some e.t.T.pos))
  else
    raise (Ignored e)

(** [No_label (f,lbl,first,x)] indicates that the parameter [x] could not be
  * passed to the function [f] because the latter has no label [lbl].
  * The [first] information tells whether [lbl=x] is the first parameter with
  * label [lbl] in the considered application, which makes the message a bit
  * more helpful. *)
exception No_label of term * string * bool * term

(** A simple mechanism for delaying printing toplevel tasks
  * as late as possible, to avoid seeing too many unknown variables. *)
let add_task, pop_tasks =
  let q = Queue.create () in
    (fun f -> Queue.add f q),
    (fun () ->
       try while true do (Queue.take q) () done with Queue.Empty -> ())

(** Type-check an expression.
  * [level] should be the sum of the lengths of [env] and [builtins],
  * that is the size of the typing context, that is the number of surrounding
  * abstractions. *)
let rec check ?(print_toplevel=false) ~level ~env e =
  (** The role of this function is not only to type-check but also to assign
    * meaningful levels to type variables, and unify the types of
    * all occurrences of the same variable, since the parser does not do it. *)
  assert (e.t.T.level = -1) ;
  e.t.T.level <- level ;
  (** The toplevel position of the (un-dereferenced) type
    * is the actual parsing position of the value.
    * When we synthesize a type against which the type of the term is unified,
    * we have to set the position information in order not to loose it. *)
  let pos = e.t.T.pos in
  let mk t = T.make ~level ~pos t in
  let mkg t = mk (T.Ground t) in
  match e.term with
  | Unit      -> e.t >: mkg T.Unit
  | Bool    _ -> e.t >: mkg T.Bool
  | Int     _ -> e.t >: mkg T.Int
  | String  _ -> e.t >: mkg T.String
  | Float   _ -> e.t >: mkg T.Float
  | Encoder f -> e.t >: type_of_format ~pos:e.t.T.pos ~level f
  | List l ->
      List.iter (check ~level ~env) l ;
      let pos =
        (* Attach the position of the first item in the list
         * to the type of the list items. It gives more info with type errors
         * when the items in the list are not compatible.
         * WARNING This will become weird with real subtyping in the inference,
         * because the type of elements will only be _a supertype_ of the type
         * of the first item. *)
        match l with e::_ -> e.t.T.pos | [] -> e.t.T.pos
      in
      let v = T.fresh_evar ~level ~pos in
        e.t >: mk (T.List v) ;
        List.iter (fun item -> item.t <: v) l
  | Record r ->
      let fields_t =
        T.Fields.mapi
          (fun field field ->
             check ~level ~env field.rval ;
             let scheme = generalize ~level field.rval in
               field.rgen <- fst scheme ;
               scheme, false)
          r
      in
        e.t >: record_t ~level ~row:false fields_t
  | Is_field (r,x) -> 
      check ~level ~env r ;
      let v = T.fresh_evar ~level ~pos in
      let fields = T.Fields.add x (([],v),true) T.Fields.empty in
      r.t <: record_t ~level ~row:true fields;
      e.t >: mkg T.Bool
  | Field (r,x,o) ->
      check ~level ~env r ;
      begin
        match o with
          | Some v ->
              check ~level ~env v;
              let fields = T.Fields.add x (([],v.t),true) T.Fields.empty in
              r.t <: record_t ~level ~row:true fields;
              e.t >: v.t
          | None ->
              let v = T.fresh_evar ~level ~pos in
              let fields = 
                T.Fields.add x (([],v),false) T.Fields.empty 
              in
              r.t <: record_t ~level ~row:true fields;
              let (g,_),_ =
                match (T.deref r.t).T.descr with
                  | T.Record r -> T.Fields.find x r.T.fields
                  | _ -> assert false
              in
              let v = T.instantiate ~level ~generalized:g v in
              e.t >: v
      end
  | Replace_field (r,x,v) ->
      check ~level ~env v.rval;
      check ~level ~env r;
      r.t <: record_t ~level ~row:true T.Fields.empty;
      let r =
        match (T.deref r.t).T.descr with
          | T.Record r -> r
          | _ -> assert false
      in
      let fields =
        let scheme = generalize ~level v.rval in
          v.rgen <- fst scheme ;
          T.Fields.add x (scheme, false) r.T.fields
      in
      let rt = mk (T.Record {T.fields  = fields;
                               row     = r.T.row;
                               opt_row = r.T.opt_row})
      in
      e.t >: rt
  | Product (a,b) ->
      check ~level ~env a ; check ~level ~env b ;
      e.t >: mk (T.Product (a.t,b.t))
  | Ref a ->
      check ~level ~env a ;
      e.t >: ref_t ~pos ~level a.t
  | Get a ->
      check ~level ~env a ;
      a.t <: ref_t ~pos ~level e.t
  | Set (a,b) ->
      check ~level ~env a ;
      check ~level ~env b ;
      a.t <: ref_t ~pos ~level b.t ;
      e.t >: mkg T.Unit
  | Seq (a,b) ->
      check ~env ~level a ;
      if not (can_ignore a.t) then raise_ignored a ;
      check ~print_toplevel ~level ~env b ;
      e.t >: b.t
  | App (a,l) ->
      check ~level ~env a ;
      List.iter (fun (_,b) -> check ~env ~level b) l ;
      (* If [a] is known to have a function type, manually dig through
       * it for better error messages. Otherwise generate its type
       * and unify -- in that case the optionality can't be guessed
       * and mandatory is the default. *)
      begin match (T.deref a.t).T.descr with
        | T.Arrow (ap,t) ->
            (* Find in l the first arg labeled lbl,
             * return it together with the remaining of the list. *)
            let rec get_arg lbl l =
              let rec aux acc = function
                | [] -> None
                | (o,lbl',t)::l ->
                    if lbl=lbl' then
                      Some (o, t, List.rev_append acc l)
                    else
                      aux ((o,lbl',t)::acc) l
              in
                aux [] l
            in
            let _,ap =
              (* Remove the applied parameters,
               * check their types on the fly. *)
              List.fold_left
                (fun (already,ap) (lbl,v) ->
                   match get_arg lbl ap with
                     | None ->
                         let first = not (List.mem lbl already) in
                           raise (No_label (a,lbl,first,v))
                     | Some (o,t,ap') ->
                         v.t <: t ;
                         (lbl::already,ap'))
                ([],ap)
                l
            in
              (* See if any mandatory argument remains,
               * check the return type. *)
              if List.for_all (fun (o,_,_) -> o) ap then
                e.t >: t
              else
                e.t >: T.make ~level ~pos:None (T.Arrow (ap,t))
        | _ ->
            let p = List.map (fun (lbl,b) -> false,lbl,b.t) l in
              a.t <: T.make ~level ~pos:None (T.Arrow (p,e.t))
      end
  | Fun (_,proto,body) ->
      let base_check = check ~level ~env in
      let proto_t,env,level =
        List.fold_left
          (fun (p,env,level) -> function
             | lbl,var,kind,None   ->
                 if debug then
                   Printf.eprintf "Assigning level %d to %s (%s).\n%!"
                     level var (T.print kind) ;
                 kind.T.level <- level ;
                 (false,lbl,kind)::p, (var,([],kind))::env, level+1
             | lbl,var,kind,Some v ->
                 if debug then
                   Printf.eprintf "Assigning level %d to %s (%s).\n%!"
                     level var (T.print kind) ;
                 kind.T.level <- level ;
                 base_check v ;
                 v.t <: kind ;
                 (true,lbl,kind)::p, (var,([],kind))::env, level+1)
          ([],env,level)
          proto
      in
      let proto_t = List.rev proto_t in
        check ~level ~env body ;
        e.t >: mk (T.Arrow (proto_t,body.t))
  | Var var ->
      let generalized,orig =
        try
          List.assoc var env
        with
          | Not_found ->
              begin match builtins#get var with
                | Some (g,v) -> g,v.V.t
                | None -> raise (Unbound (e.t.T.pos,var))
              end
      in
        e.t >: T.instantiate ~level ~generalized orig ;
        if debug then
          Printf.eprintf "Instantiate %s[%d] : %s becomes %s\n%!"
            var (T.deref e.t).T.level (T.print orig) (T.print e.t)
  | Let ({gen=gen; var=name; def=def; body=body} as l) ->
      check ~level:level ~env def ;
      let scheme = generalize ~level def in
      let env = (name,scheme)::env in
        l.gen <- fst scheme ;
        if print_toplevel then
          (add_task (fun () ->
             Format.printf "@[<2>%s :@ %a@]@."
               (let l = String.length name and max = 5 in
                  if l >= max then name else name ^ String.make (max-l) ' ')
               T.pp_scheme scheme)) ;
        check ~print_toplevel ~level:(level+1) ~env body ;
        e.t >: body.t

(* The simple definition for external use. *)
let check ?(ignored=false) e =
  let print_toplevel = !Configure.display_types in
    try
      check ~print_toplevel ~level:(List.length builtins#get_all) ~env:[] e ;
      if ignored && not (can_ignore e.t) then raise_ignored e ;
      pop_tasks ()
    with
      | e -> pop_tasks () ; raise e


(** {1 Computations} *)

(** For internal use. I want to give an ID to sources built by FFI application
  * based on the name under which the FFI is registered.
  * [get_name f] returns the name under which the FFI f is registered. *)
exception F of string
let get_name f =
  try
    builtins#iter
      (fun name (_,v) -> match v.V.value with
         | V.FFI (_,_,ff) when f == ff -> raise (F name)
         | _ -> ()) ;
    "<ff>"
  with
    | F s -> s

(** [remove_first f l] removes the first element [e] of [l] such that [f e],
  * and returns [e,l'] where [l'] is the list without [e].
  * Asserts that there is such an element. *)
let remove_first filter =
  let rec aux acc = function
    | [] -> assert false
    | hd::tl ->
         if filter hd then
           (hd,List.rev_append acc tl)
         else
           aux (hd::acc) tl
  in aux []

(** Evaluation has to be typed, because some FFI's have a behavior
  * that depends on their return type (for example, source and request
  * creations). This is annoying but we really need a type inference kind
  * of mechanism to obtain the information that such functions need,
  * so this seems like the right thing to do.
  *
  * So, when we evaluate a variable of type T, we have to lookup
  * a let-definition, whose type has T as an instance, instantiate it
  * and unify it with T. But this is not enough: we need the types
  * inside the definition to get instantiated properly too.
  * This also requires to duplicate the definition before
  * instantiation, to avoid sharing the instantiation with
  * the definition itself and its future/past instantiations. *)

let instantiate ~generalized def =
  let subst =
    (* Levels don't matter since we're never going to generalize. *)
    List.map
      (fun (i,c) -> (i,c), T.fresh ~level:0 ~constraints:c ~pos:None)
      generalized
  in
  if generalized=[] then def else
    V.map_types
      (fun bound t ->
         let subst =
           List.filter (fun (x,_) -> not (List.mem x bound)) subst
         in
           T.copy_with subst t)
      []
      def

let lookup env var ty =
  let generalized,def = List.assoc var env in
  let v = instantiate ~generalized def in
    if debug then
      Printf.eprintf
        "Runtime instantiation of %s: %s targets %s.\n%!"
        var
        (T.print ~generalized def.V.t)
        (T.print ty) ;
    v.V.t <: ty ;
    if debug then
      Printf.eprintf
        "Runtime instantiation of %s: %s becomes %s.\n%!"
        var
        (T.print ~generalized def.V.t)
        (T.print v.V.t) ;
    v

let rec eval ~env tm =
  let mk v = { V.t = tm.t ; V.value = v } in
    match tm.term with
      | Unit -> mk (V.Unit)
      | Bool    x -> mk (V.Bool x)
      | Int     x -> mk (V.Int x)
      | String  x -> mk (V.String x)
      | Float   x -> mk (V.Float x)
      | Encoder x -> mk (V.Encoder x)
      | List l -> mk (V.List (List.map (eval ~env) l))
      | Product (a,b) -> mk (V.Product (eval ~env a, eval ~env b))
      | Record r -> 
          mk (V.Record (T.Fields.map (fun v -> eval ~env v.rval) r))
      | Field (r,x,o) ->
        let v =
          match (eval ~env r).V.value with
            | V.Record r -> 
                begin
                 try
                  T.Fields.find x r
                 with
                   | _ -> eval ~env (Utils.get_some o)
                end
            | _ -> assert false
        in
        let (g,t),o =
          match (T.deref r.t).T.descr with
            | T.Record r ->
                begin 
                 try
                   T.Fields.find x r.T.fields
                 with _ -> ([],(Utils.get_some o).t),true
                end
            | _ -> assert false
        in
        instantiate ~generalized:g v
      | Is_field (r,x) ->
          let r =
            match (eval ~env r).V.value with
              | V.Record r -> r
              | _ -> assert false
          in
          begin
           try
             ignore(T.Fields.find x r);
             mk (V.Bool true)
           with
             | Not_found -> mk (V.Bool false)
          end
      | Replace_field (r,x,v) ->
        let r = eval ~env r in
        let r =
          match r.V.value with
            | V.Record r -> r
            | _ -> assert false
        in
        let r = 
          T.Fields.add x (eval ~env v.rval) r
        in
        mk (V.Record r)
      | Ref v -> mk (V.Ref (ref (eval ~env v)))
      | Get r ->
          begin match (eval ~env r).V.value with
            | V.Ref r -> !r
            | _ -> assert false
          end
      | Set (r,v) ->
          begin match (eval ~env r).V.value with
            | V.Ref r ->
                r := eval ~env v ;
                mk V.Unit
            | _ -> assert false
          end
      | Let {gen=generalized;var=x;def=v;body=b} ->
          (* It should be the case that generalizable variables don't
           * get instantiated in any way when evaluating the definition.
           * But we don't double-check it. *)
          let v = eval ~env v in
          eval ~env:((x,(generalized,v))::env) b
      | Fun (fv,p,body) ->
          (* Unlike OCaml we always evaluate default values,
           * and we do that early.
           * I think the only reason is homogeneity with FFI,
           * which are declared with values as defaults. *)
          let p =
            List.map
              (fun (lbl,var,_,v) -> lbl,var,Utils.may (eval ~env) v)
              p
          in
          let env = List.filter (fun (x,_) -> Vars.mem x fv) env in
            mk (V.Fun (p,[],env,body))
      | Var var ->
          lookup env var tm.t
      | Seq (a,b) ->
          ignore (eval ~env a) ;
          eval ~env b
      | App (f,l) ->
          apply ~t:tm.t
            (eval ~env f)
            (List.map (fun (l,t) -> l, eval ~env t) l)

and apply ~t f l =
  let mk v = { V.t = t ; V.value = v } in
  (* Extract the components of the function, whether it's explicit
   * or foreign, together with a rewrapping function for creating
   * a closure in case of partial application. *)
  let p,pe,f,rewrap =
    match f.V.value with
      | V.Fun (p,pe,e,body) ->
          p,pe,
          (fun pe _ -> eval ~env:(List.rev_append pe e) body),
          (fun p pe -> mk (V.Fun (p,pe,e,body)))
      | V.FFI (p,pe,f) ->
          p,pe,
          (fun pe t -> f (List.rev pe) t),
          (fun p pe -> mk (V.FFI (p,pe,f)))
      | _ -> assert false
  in
  let pe,p =
    List.fold_left
      (fun (pe,p) (lbl,v) ->
         let (_,var,_),p =
           remove_first (fun (l,_,_) -> l=lbl) p
         in
           (var,([],v))::pe, p)
      (pe,p) l
  in
    if List.exists (fun (_,_,x) -> x=None) p then
      (* Partial application. *)
      rewrap p pe
    else
      (* XXX Contrary to older implementation of eval,
       * we do not assign location-based IDs to sources
       * (e.g. add@L13C4). *)
      let pe =
        List.fold_left
          (fun pe (_,var,v) ->
             (var,
              (* Set the position information on FFI's default values.
               * Cf. r5008: if an Invalid_value is raised on a default value,
               * which happens with the mount/name params of output.icecast.*,
               * the printing of the error should succeed at getting a position
               * information. *)
              let v = Utils.get_some v in
                [],
                { v with V.t = T.make ~pos:t.T.pos (T.Link v.V.t) })::pe)
          pe p
      in
      let v = f pe t in
        (* Similarly here, the result of an FFI call should have some position
         * information. For example, if we build a fallible source and pass
         * it to an operator that expects an infallible one, an error
         * is issued about that FFI-made value and a position is needed. *)
        { v with V.t = T.make ~pos:t.T.pos (T.Link v.V.t) }

(** Add toplevel definitions to [builtins] so they can be looked
  * during the evaluation of the next scripts.
  * Also try to generate a structured documentation from the source code. *)
let toplevel_add (doc,params) x ~generalized v =
  let ptypes =
    match (T.deref v.V.t).T.descr with
      | T.Arrow (p,_) -> p
      | _ -> []
  in
  let pvalues =
    match v.V.value with
      | V.Fun (p,_,_,_) -> List.map (fun (l,_,o) -> l,o) p
      | _ -> []
  in
  let params,pvalues =
    List.fold_left
      (fun (params,pvalues) (opt,label,t) ->
         let descr,params =
           try
             List.assoc label params,
             List.remove_assoc label params
           with
             | Not_found -> "",params
         in
         let default,pvalues =
           try
             `Known (List.assoc label pvalues),
             List.remove_assoc label pvalues
           with
             | Not_found -> `Unknown, pvalues
         in
         let item = Doc.trivial (if descr="" then "(no doc)" else descr) in
           item#add_subsection "type" (T.doc_of_type ~generalized t) ;
           item#add_subsection "default"
             (Doc.trivial (match default with
                             | `Unknown -> "???"
                             | `Known (Some v) -> V.print_value v
                             | `Known None -> "None")) ;
           doc#add_subsection
             (if label="" then "(unlabeled)" else label)
             item ;
           params,pvalues)
      (params,pvalues)
      ptypes
  in
    List.iter
      (fun (s,_) ->
         Printf.eprintf "WARNING: Unused @param %S for %s!\n" s x)
      params ;
    doc#add_subsection "_type" (T.doc_of_type ~generalized v.V.t) ;
    builtins#register ~doc x (generalized,v)

let rec eval_toplevel ?(interactive=false) t =
  match t.term with
    | Let {doc=comment;
           gen=generalized;
           var=name;def=def;body=body} ->
        let env = builtins#get_all in
        let def = eval ~env def in
          toplevel_add comment name ~generalized def ;
          if debug then
            Printf.eprintf "Added toplevel %s : %s\n%!"
              name (T.print ~generalized def.V.t) ;
          if interactive then
            Format.printf "@[<2>%s :@ %a =@ %s@]@."
              name
              (T.pp_type_generalized generalized) def.V.t
              (V.print_value def) ;
          eval_toplevel ~interactive body
    | Seq (a,b) ->
        ignore
          (let v = eval_toplevel a in
             if v.V.t.T.pos = None then { v with V.t = a.t } else v) ;
        eval_toplevel ~interactive b
    | _ ->
        let v = eval ~env:builtins#get_all t in
          if interactive && t.term <> Unit then
           begin
            (* TODO level 0 may be abusive because of previous let-in
             *   also the level argument of generalize may just be
             *   t.level *)
            let scheme = generalize ~level:0 t in
            Format.printf "- : %a = %s@."
              T.pp_scheme scheme
              (V.print_value v) 
           end ;
          v
