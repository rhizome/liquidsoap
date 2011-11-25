(** Builtin operations for SAML. *)

open Lang_builtins

let register () =
  add_builtin "math.sin" ~cat:Math ~descr:"Sin function." ~extern:"sin"
    [ "",Lang.float_t,None,None ] Lang.float_t
    (fun p ->
      match (snd (List.hd p)).Lang.value with
        | Lang.Float i -> Lang.float (sin i)
        | _ -> assert false)
