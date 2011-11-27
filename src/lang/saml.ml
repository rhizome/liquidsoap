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
  add_builtin "emit.c.generator"
    [
      "file", Lang.string_t, Some (Lang.string "saml_out.c"), Some "Output file name.";
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
      let v = SV.emit "out" ~venv ~env v in
      let v =
        let env = SB.Emitter_C.Env.create () in
        SB.Emitter_C.emit_decls ~env v
      in
      Printf.printf "EMIT: %s\n\n%!" fname;
      Printf.printf "BEGIN\n%s\nEND\n%!" v;
      let fname = "/tmp/"^fname in
      let oc = open_out fname in
      output_string oc v;
      close_out oc;
      assert false
    );
  Saml_builtins.register ()

(** Enable SAML extensions. *)
let enable () =
  assert (not !enabled);
  register_builtins ();
  enabled := true
