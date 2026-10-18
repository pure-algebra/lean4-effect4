(* Kit_mcp — the authoring tool as a stdio MCP 2025-06-18 server (`eff mcp`).
   Its behaviours (M1–M4) are listed in kit_mcp.ml and tested by test/kit/test_mcp.ml. *)

(** One server: one tool session, held from call to call. *)
type t

(** A server whose session has accepted no action. *)
val create : unit -> t

(** One UTF-8 JSON-RPC message line. Initialize and acknowledge before tool calls.
    A notification has no reply. Tool replies contain both structured data and JSON text. *)
val line : t -> string -> string option
