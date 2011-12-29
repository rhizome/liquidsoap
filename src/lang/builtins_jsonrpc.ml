(*****************************************************************************

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

let log = Dtools.Log.make ["lang";"json-rpc"]

let counter = ref 0
let get_fresh () =
  incr counter;
  Lang.univ_t !counter

let rec type_of_json = function
  | `Assoc a      ->
      let opt_row = get_fresh () in
      let a = 
        List.map 
          (fun (l,v) -> (l, (([], type_of_json v), false))) 
          a
      in
      Lang.record_t ~opt_row (Lang_types.fields_of_list a)
  | `Bool b       -> Lang.bool_t
  | `Float f      -> Lang.float_t
  | `Int i        -> Lang.int_t
  | `Intlit s     -> Lang.string_t (* ?? *)
  | `List []      -> Lang.list_t (get_fresh ())
  | `List (x::l)  -> 
      let ret = type_of_json x in
      assert (ret == type_of_json (`List l));
      ret
  | `Null         -> Lang.unit_t
  | `String s     -> Lang.string_t
  | `Tuple _
  | `Variant _    -> assert false (* Non-standard extension provided by yojson.. *) 

let rec of_json = function
  | `Assoc a      -> 
      let a = List.map (fun (l,v) -> (l, of_json v)) a in 
      Lang.record ~opt_row:(get_fresh()) (Lang_types.fields_of_list a)
  | `Bool b       -> Lang.bool b
  | `Float f      -> Lang.float f
  | `Int i        -> Lang.int i
  | `Intlit s     -> Lang.string s (* ?? *)
  | `List   l     -> 
       Lang.list ~t:(type_of_json (`List l)) (List.map of_json l)
  | `Null         -> Lang.unit
  | `String s     -> Lang.string s
  | `Tuple  _
  | `Variant _ -> assert false (* Don't need this.. *)

let rec to_json v =
  match v.Lang.value with
    | Lang.Unit     -> `Null
    | Lang.Bool b   -> `Bool b
    | Lang.Int  i   -> `Int i
    | Lang.String s -> `String s
    | Lang.Float  f -> `Float f
    | Lang.List l   -> `List (List.map to_json l)
    | Lang.Record r ->
        let l = Lang_types.list_of_fields r in
        let l = List.map (fun (l, gvalue) -> (l, gvalue.Lang.v_value)) l in
        `Assoc (List.map (fun (l, v) -> (l, to_json v)) l)
    | Lang.Product (p,q) -> `List [to_json p; to_json q]
    | Lang.Source _ -> `String "\"<source>\""
    | Lang.Ref v -> `Assoc ["reference", to_json !v]
    | Lang.Encoder e -> `String (Encoder.string_of_format e)
    | Lang.Request _ -> `String "\"<request>\""
    | Lang.FFI _
    | Lang.Fun _ -> `String "\"<fun>\""

let callback_of_value v =
  let callback_of_arrow args ret f =
    (fun params ->
       let params =
         (* Transform params into arguments. *)
         match params with
           | `Null | `None -> []
           | `Some (`List l) ->
               List.map (fun v -> "", of_json v) l
           | `Some (`Assoc l) ->
               (* Convention: because of mixed named/unamed arguments in liquidsoap,
                * `Assoc should used numbers for unnamed arguments, e.g: { 1: "foo", bla: "bar", 2: 10 }. *)
               let named, unnamed = 
                 List.fold_left 
                   (fun (named, unnamed) (l, v) ->
                      let v = of_json v in
                      try 
                        named, ((int_of_string l, v) :: unnamed)
                      with
                        | Failure "int_of_string" ->
                            ((l, v) :: named), unnamed) ([],[]) l
               in
               let unnamed = List.sort (fun (x,_) (y,_) -> compare x y) unnamed in
               let unnamed = List.map (fun (_,x) -> ("",x)) unnamed in
               unnamed @ named
       in
       let ret = Lang.apply v params ~t:ret in
       to_json ret) 
  in
  (* Special case not in JSON-RPC specs. *)
  let callback_of_value v =  
    (fun params -> to_json v)
  in
  match (Lang_types.deref v.Lang.t).Lang_types.descr with
    | Lang_types.Arrow (args, ret) -> 
        callback_of_arrow args ret v
    | _ -> callback_of_value v 

let callbacks = Hashtbl.create 10

let json_rpc req =
  try 
    let fn = Hashtbl.find callbacks req.Jsonrpc.request_method in
    `Result 
      { Jsonrpc.
         result_content = fn req.Jsonrpc.request_params;
         result_id      = req.Jsonrpc.request_id }
  with 
    | Not_found -> raise (Jsonrpc.Method_not_found req.Jsonrpc.request_id)

let () =
  let t = Lang.univ_t 1 in
  Lang_builtins.add_builtin
   ~cat:Lang_builtins.Liq
   ~descr:"Register any value as a json-rpc callback."
   "json.rpc.register"
   ["method", Lang.string_t, None, Some "Method name";
    "", t, None, None ] Lang.unit_t
   (fun p ->
      let v = List.assoc "" p in
      let l = Lang.to_string (List.assoc "method" p) in
      Hashtbl.add callbacks l (callback_of_value v);
      Lang.unit)

let () =
  Lang_builtins.add_builtin
   ~cat:Lang_builtins.Liq
   ~descr:"Execute a JSON-RPC request."
   "json.rpc.execute"
   ["", Lang.string_t, None, None ] Lang.string_t
   (fun p ->
      let v = Lang.to_string (List.assoc "" p) in
      Lang.string ((Jsonrpc.wrap json_rpc) v))

