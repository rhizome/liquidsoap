(** Builtin operations for SAML. *)

module T = Lang_types

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
      Lang.float (max x y))

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
    )

let register () =
  Printf.printf "Registered SAML builtins.\n%!";
  register_math ();
  register_event ();
  register_other ()
