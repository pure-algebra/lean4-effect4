(* Kit_mcp — the authoring tool as a Model Context Protocol server (`eff mcp`).
   Its behaviours (M1–M5) are listed in kit_mcp.ml and tested by test/kit/test_mcp.ml. *)

(** One server: one tool session, held from call to call. *)
type t

(** A server whose session has accepted no action. *)
val create : unit -> t

(** One JSON-RPC message line in; its reply line out, or none for a notification. *)
val line : t -> string -> string option
