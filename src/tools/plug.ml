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

(** A [plug] is something where plug-ins plug.
  We build [plug] on the top of [Doc.item]. *)

class ['a] plug name ?(register_hook=fun _ -> ()) ?split_name doc insensitive =
object (self)
  inherit Doc.item doc

  val mutable plugins : (string * 'a) list = []

  method register plugin ?doc ?sdoc v =
    let splugin = if insensitive then String.uppercase plugin else plugin in
    let plugin_name, plugin_fields =
      if split_name = None then
        splugin, []
      else
        let plugin = Pcre.split ~pat:"\\." splugin in
        List.hd plugin, List.tl plugin
    in
    let doc = match doc,sdoc with
      | (Some d), _ -> d
      | _, None -> Doc.trivial "(no doc)"
      | _, (Some s) -> Doc.trivial s
    in
    let v =
      match split_name with
        | None -> v
        | Some f ->
          (* We use f to merge with the previous value. *)
          let old =
            try
              Some (List.assoc plugin_name plugins)
            with
              | Not_found -> None
          in
          f old plugin_fields v
    in
    let _subsections, _plugins =
      if split_name = None then
        subsections, plugins
      else
        List.filter (fun (k,_) -> k<>splugin) subsections,
        List.filter (fun (k,_) -> k<>plugin_name) plugins
    in
    subsections <- (splugin,doc)::_subsections;
    plugins <- (plugin_name,v)::_plugins;
    register_hook (splugin,v)

  method is_registered a = List.mem_assoc a plugins
  method keys = List.fold_left (fun l (k,v) -> k::l) [] plugins
  method iter ?(rev=false) f =
    let plugins =
      if rev then
        List.rev plugins
      else
        plugins
    in
    List.iter (fun (k,v) -> f k v) plugins
  method get_all = plugins
  method get plugin =
    let plugin = if insensitive then String.uppercase plugin else plugin in
      try
        Some (List.assoc plugin plugins)
      with
        | Not_found -> None
end

(** Every [plug] plugs in [plugs] *)

let plugs = new Doc.item "All the plugs"

let create ?split_name ?register_hook ?insensitive ?doc plugname =
  let insensitive = match insensitive with Some true -> true | _ -> false in
  let doc = match doc with None -> "(no doc)" | Some d -> d in
  let plug = new plug ?register_hook ?split_name plugname doc insensitive in
    plugs#add_subsection plugname (plug:>Doc.item) ;
    plug

let list () =
  plugs#list_subsections
