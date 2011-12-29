(** Builtin operations for SAML. *)

module T = Lang_types
module B = Saml_backend

(** Operations necessary to define a builtin. *)
type t = {
  b_name : string;
  b_type : B.T.t;
  b_emit_c : string array -> string;
}

let builtins =
  let b name =
    let default_emit_c args =
      let args = Array.to_list args in
      let args = String.concat ", " args in
      Printf.sprintf "%s(%s)" name args
    in
    fun ?(c=default_emit_c) typ ->
      {
        b_name = name;
        b_type = typ;
        b_emit_c = c;
      }
  in
  let f_f = B.T.Arr ([B.T.Float], B.T.Float) in
  let ff_f = B.T.Arr ([B.T.Float; B.T.Float], B.T.Float) in
  let f_u = B.T.Arr ([B.T.Float], B.T.Void) in
  let c_bop op args = Printf.sprintf "(%s %s %s)" args.(0) op args.(1) in
  [
    b "sin" f_f;
    b "pow" ff_f;
    b "fadd" ff_f ~c:(c_bop "+");
    b "fmax" ff_f;
    b "fmin" ff_f;
    b "print_float" f_u ~c:(fun args -> Printf.sprintf "printf(\"%%f\\n\",%s)" args.(0));
    b "frand" f_f ~c:(fun args -> Printf.sprintf "((float)rand()/(float)RAND_MAX*%s)" args.(0));
  ]

let () =
  List.iter
    (fun b ->
      B.builtin_ops := (b.b_name, b.b_type) :: !B.builtin_ops;
      B.Emitter_C.builtin_ops_emitters := (b.b_name, b.b_emit_c) :: !B.Emitter_C.builtin_ops_emitters
    ) builtins

open Lang_builtins

let register_math () =
  add_builtin "math.sin" ~cat:Math ~descr:"Sin function." ~extern:"sin"
    [ "",Lang.float_t,None,None ] Lang.float_t
    (fun p ->
      match (snd (List.hd p)).Lang.value with
        | Lang.Float i -> Lang.float (sin i)
        | _ -> assert false);
  add_builtin "math.max" ~cat:Math ~descr:"Max." ~extern:"fmax"
    [
      "",Lang.float_t,None,None;
      "",Lang.float_t,None,None;
    ]
    Lang.float_t
    (fun p ->
      let x = Lang.assoc "" 1 p in
      let y = Lang.assoc "" 2 p in
      let x = Lang.to_float x in
      let y = Lang.to_float y in
      Lang.float (max x y));
  add_builtin "math.min" ~cat:Math ~descr:"Min." ~extern:"fmin"
    [
      "",Lang.float_t,None,None;
      "",Lang.float_t,None,None;
    ]
    Lang.float_t
    (fun p ->
      let x = Lang.assoc "" 1 p in
      let y = Lang.assoc "" 2 p in
      let x = Lang.to_float x in
      let y = Lang.to_float y in
      Lang.float (min x y));
  add_builtin "math.pow" ~cat:Math ~descr:"Pow." ~extern:"pow"
    [
      "",Lang.float_t,None,None;
      "",Lang.float_t,None,None;
    ]
    Lang.float_t
    (fun p ->
      let x = Lang.assoc "" 1 p in
      let y = Lang.assoc "" 2 p in
      let x = Lang.to_float x in
      let y = Lang.to_float y in
      Lang.float (x ** y));
  add_builtin "math.random.float" ~cat:Math ~descr:"Random float." ~extern:"frand"
    [ "",Lang.float_t,None,None ] Lang.float_t
    (fun p ->
      match (snd (List.hd p)).Lang.value with
        | Lang.Float i -> Lang.float (Random.float i)
        | _ -> assert false)

let register_event () =
  Lang.add_builtin "event.channel" ~category:(string_of_category Control)
    ~descr:"Create an event channel."
    ~extern:"event_channel"
    [] (Lang.event_t (Lang.univ_t 1))
    (fun p t ->
      { Lang.t = t; value = Lang.Event_channel [] }
    );
  add_builtin "event.handle" ~cat:Control ~descr:"Handle an event on a channel."
    ~extern:"event_handle"
    [
      "", Lang.event_t (Lang.univ_t 1), None, Some "Event channel.";
      "", Lang.fun_t [false, "", Lang.univ_t 1] Lang.unit_t, None, Some "Handler function.";
    ] (Lang.unit_t)
    (fun p ->
      let c = Lang.assoc "" 1 p in
      let h = Lang.assoc "" 2 p in
      { Lang.t = Lang.unit_t; value = Lang.Event_handle(c,h) }
    );
  add_builtin "event.emit" ~cat:Control ~descr:"Emit an event on a channel."
    ~extern:"event_emit"
    [
      "", Lang.event_t (Lang.univ_t 1), None, Some "Event channel.";
      "", Lang.univ_t 1, None, Some "Event data.";
    ] (Lang.unit_t)
    (fun p ->
      let c = Lang.assoc "" 1 p in
      let v = Lang.assoc "" 2 p in
      { Lang.t = Lang.unit_t; value = Lang.Event_emit(c,v) }
    )

let register_other () =
  add_builtin "print_int" ~cat:Control ~descr:"Print an integer." ~extern:"print_int"
    ["", Lang.int_t, None, None] Lang.unit_t
    (fun p ->
      let n = Lang.to_int (List.assoc "" p) in
      Printf.printf "%d" n;
      Lang.unit
    );
  add_builtin "print_float" ~cat:Control ~descr:"Print an integer." ~extern:"print_float"
    ["", Lang.float_t, None, None] Lang.unit_t
    (fun p ->
      let x = Lang.to_float (List.assoc "" p) in
      Printf.printf "%f" x;
      Lang.unit
    )

let register () =
  Printf.printf "Registered SAML builtins.\n%!";
  register_math ();
  register_event ();
  register_other ()
