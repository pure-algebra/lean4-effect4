(* Kit_tool — the authoring tool's native shell (seams S6): JSON lines over the generated Tool.serve.

   What it is: tools/Drivers/Session.lean's loop, in OCaml. A line is one request envelope
   (`Tool.Wire.Envelope Request`: the method, version 1, the request) in the Tool group's generated
   JSON. The text is parsed here (Kit.Json), read under the envelope's shape into a value tree
   (Kit_json), and handed to the generated `Tool.Native.serve` (src/Effect4/Tool/Native.lean,
   lowered into ../../gen/api_gen.ml): the exact codec, the connection check, `Tool.serve` through
   the checker memo, and the reply's framing are Lean's wire core (`Tool.Wire.serveEnvelope`). The
   session is abstract, so this shell cannot forge a state or a memo. The reply envelope prints
   under its shape. Nothing here interprets a request.
   Depends on: Effect4_gen.Api_gen, Kit, Kit_json.

   Behaviours:
   T1 A line that does not parse prints {"refused": "<why>"}; a line that parses but does not read
      under the envelope's shape prints the wire refusal Lean's driver prints for it (`codec
      unreadable`). Neither changes anything.                         tested (test_tool)
   T2 A wire refusal prints {"refused": <the refusal's JSON>} and changes nothing.
                                                                       tested (test_tool)
   T3 A served request prints its reply envelope, and the next line is served at the next session,
      whose memo learned the reply's checks.                           tested (test_tool)
   T4 The memo changes cost, never a reply: Lean's `serve_transparent`; the cached and uncached
      transcripts are compared.                                        tested (test_tool)
   T5 The replies equal tools/Drivers/Session.lean's on the pinned session fixture.
                                                                       tested (test_tool) *)

module G = Effect4_gen.Api_gen
module J = Eff_json_text

type t = { mutable session : G.session }

let create () = { session = G.tool_native_start }

let refused (why : J.t) = J.render (J.Object [ ("refused", why) ])

let wire_refused (why : G.effect4_tool_wire_refusal) =
  refused (Kit_json.print G.tool_native_refusal_shape (G.tool_native_refusal_to_val why))

let serve_line (t : t) (line : string) : string =
  match Kit.Json.parse line with
  | Error why -> refused (J.String why)
  | Ok json -> (
    match Kit_json.read G.tool_native_envelope_shape json with
    | None ->
      wire_refused (G.Effect4_tool_wire_refusal_codec G.Effect4_tool_codec_profile_refusal_unreadable)
    | Some v -> (
      match G.tool_native_serve t.session v with
      | Error why -> wire_refused why
      | Ok (reply, session) ->
        t.session <- session;
        J.render (Kit_json.print G.tool_native_reply_envelope_shape reply)))
