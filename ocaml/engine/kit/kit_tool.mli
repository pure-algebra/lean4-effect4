(* Kit_tool — the authoring tool's native shell: JSON lines over the generated wire core.
   Its behaviours (T1–T5) are listed in kit_tool.ml and tested by test/kit/test_tool.ml. *)

(** One native workspace: the generated `Tool.Native.Workspace`, abstract. *)
type t

(** A workspace where no action is accepted, with an empty checker memo. *)
val create : unit -> t

(** One request's JSON tree through the workspace (`Tool.Native.serveTree`): the reply envelope's
    tree, or the wire's refusal; a refused request leaves the workspace as it was. *)
val serve_tree
  :  t
  -> Kit.Json.t
  -> (Kit.Json.t, Effect4_gen.Api_gen.effect4_tool_wire_refusal) result

(** A wire refusal as the line protocol writes it: [{"refused": <the refusal's JSON>}]. *)
val wire_refused : Effect4_gen.Api_gen.effect4_tool_wire_refusal -> Kit.Json.t

(** One request line in, one reply line out; a refused line leaves the workspace as it was. *)
val serve_line : t -> string -> string
