(** SAML extensions of the language. *)

module T = Lang_types
module V = Lang_values
module SB = Saml_backend
module SV = Saml_values

let enabled = ref false

(** Types for meta-constants defined by SAML. *)
let typing_env =
  let float_t = T.make (T.Ground T.Float) in
  [
    "now",([],float_t);
    "period",([],float_t);
  ]

(** Register a meta-operator in Liquidsoap. *)
let add_builtin ?flags name =
  Lang.add_builtin ("saml."^name) ?flags ~category:"SAML" ~meta:true

let register_builtins () =
  add_builtin "emit.generator.c"
    [
      "file", Lang.string_t, Some (Lang.string "/tmp/saml_out.c"), Some "Output file name.";
      "", Lang.float_t, None, Some "";
    ]
    Lang.unit_t
    ~descr:"Emit C code for a generator."
    ~flags:[Lang.Experimental]
    (fun args t ->
      let fname = Lang.to_string (List.assoc "file" args) in
      let v = List.assoc "" args in
      let env,venv,v =
        match v.Lang.value with
          | Lang.Quote (env,venv,v) -> env,venv,v
          | _ -> assert false
      in
      (* let venv = List.map (fun (x,(c,v)) -> x,v) V.builtins#get_all in *)
      let v = SV.emit "saml_synth" ~venv ~env v in
      let v = SB.Emitter_C.emit_decls v in
      Printf.printf "EMIT: %s\n\n%!" fname;
      Printf.printf "BEGIN\n%s\nEND\n%!" v;
      let fname = fname in
      let oc = open_out fname in
      output_string oc v;
      close_out oc;
      Lang.unit
    );
  let arr t1 t2 = T.make (T.Arrow([false,"",t1], t2)) in
  let zarr t = T.make (T.Arrow([], t)) in
  let f_u () = arr Lang.float_t Lang.unit_t in
  let voice_t =
    let r = ["main", Lang.float_t] in
    let r = List.map (fun (x,t) -> x, (([],t),false)) r in
    Lang.record_t ~row:true (T.Fields.of_list r)
  in
  add_builtin "emit.generator.dssi.c"
    [
      "file", Lang.string_t, Some (Lang.string "/tmp/saml_out"), Some "Output file name.";
      "name", Lang.string_t, Some (Lang.string "saml_synth"), Some "Name of the synthesizer.";
      "", voice_t, None, Some "";
    ]
    Lang.unit_t
    ~descr:"Emit C code as a DSSI plugin for a generator."
    ~flags:[Lang.Experimental]
    (fun args t ->
      let fname = Lang.to_string (List.assoc "file" args) in
      let name = Lang.to_string (List.assoc "name" args) in
      let v = List.assoc "" args in
      let env,venv,v =
        match v.Lang.value with
          | Lang.Quote (env,venv,v) -> env,venv,v
          | _ -> assert false
      in
      let v =
        let synth = "#synth" in
        let prog = SV.make_field ~t:Lang.float_t (SV.make_var synth) "main" in
        let prog =
          SV.make_let
            (name^"_set_freq")
            (SV.make_field ~t:(f_u ()) (SV.make_var synth) "set_freq")
            prog
        in
        let prog =
          SV.make_let
            (name^"_set_velocity")
            (SV.make_field ~t:(f_u ()) (SV.make_var synth) "set_velocity")
            prog
        in
        let prog =
          SV.make_let
            (name^"_note_off")
            (SV.make_field ~t:(zarr Lang.unit_t) (SV.make_var synth) "note_off")
            prog
        in
        let prog =
          SV.make_let
            (name^"_is_active")
            (SV.make_field ~t:(zarr Lang.bool_t) (SV.make_var synth) "is_active")
            prog
        in
        let prog =
          SV.make_let
            (name^"_activate")
            (SV.make_field ~t:(zarr Lang.bool_t) (SV.make_var synth) "activate")
            prog
        in
        SV.make_let synth v prog
      in
      let keep_let = [name^"_set_freq"; name^"_set_velocity";name^"_note_off";name^"_is_active";name^"_activate"] in
      let v = SV.emit name ~keep_let ~venv ~env v in
      let v = SB.Emitter_C.emit_dssi ~name v in
      Printf.printf "EMIT: %s\n\n%!" fname;
      Printf.printf "BEGIN\n%s\nEND\n%!" v;
      let oc = open_out (fname ^ ".c") in
      output_string oc v;
      close_out oc;
      ignore (Sys.command (Printf.sprintf "gcc -fPIC -O3 -g -shared -Wall %s.c -o %s.so" fname fname));
      Lang.unit
    );
  Saml_builtins.register ()

(** Enable SAML extensions. *)
let enable () =
  assert (not !enabled);
  V.default_typing_env := typing_env @ !V.default_typing_env;
  register_builtins ();
  enabled := true
