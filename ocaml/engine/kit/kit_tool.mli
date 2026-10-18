(* Kit_tool — the authoring tool's native shell: JSON lines over the generated wire core.
   Its behaviours (T1–T5) are listed in kit_tool.ml and tested by test/kit/test_tool.ml. *)

(** One native session: the generated `Tool.Native.Session`, abstract. *)
type t

(** A session where no action is accepted, with an empty checker memo. *)
val create : unit -> t

(** One request line in, one reply line out; a refused line leaves the session as it was. *)
val serve_line : t -> string -> string
