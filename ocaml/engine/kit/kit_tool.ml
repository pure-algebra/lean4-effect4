(* Kit_tool — the authoring tool's native shell (seams S6): JSON lines over the generated Tool.serve.

   What it is: tools/Drivers/Session.lean's loop, in OCaml. A line is one request envelope
   (`Tool.Wire.Envelope Request`: the method, version 1, the request) in the Tool group's generated
   JSON. Lean's text grammar reads the line into the profile's tree (Kit.Json.parse, lowered
   `NatJson.parse`, the one tools/Drivers/Session.lean reads with), and the generated
   `Tool.Native.serveTree` (src/Effect4/Tool/Native.lean, lowered into ../../gen/api_gen.ml) does
   the rest: Lean's located reader under the envelope's shape, the connection check, `Tool.serve`
   through the checker memo, the reply's framing, and the reply envelope's print as the tools
   print it, which Lean's renderer writes as text (Kit.Json.render). The session is abstract, so
   this shell cannot forge a state or a memo. Nothing here interprets a request.
   Depends on: Effect4_gen.Api_gen, Kit (Kit.Json).

   Behaviours:
   T1 A line that does not parse prints {"refused": "<why>"}, Lean's sentence for where the text
      stops fitting the grammar; a line that parses but does not read
      under the envelope's shape prints the wire refusal Lean's driver prints for it (`codec
      unreadable`, with the site and the reason Lean's reader names). Neither changes anything.
                                                                       tested (test_tool)
   T2 A wire refusal prints {"refused": <the refusal's JSON>} and changes nothing.
                                                                       tested (test_tool)
   T3 A served request prints its reply envelope, and the next line is served at the next session,
      whose memo learned the reply's checks.                           tested (test_tool)
   T4 The memo changes cost, never a reply: Lean's `serve_transparent`; the cached and uncached
      transcripts are compared.                                        tested (test_tool)
   T5 The replies equal tools/Drivers/Session.lean's on the pinned session fixture.
                                                                       tested (test_tool) *)

module G = Effect4_gen.Api_gen
module J = Kit.Json

type t = { mutable session : G.session }

let create () = { session = G.tool_native_start }
let refused (why : J.t) = J.NatJson_obj [ "refused", why ]

let wire_refused (why : G.effect4_tool_wire_refusal) =
  refused (G.tool_native_refusal_tree why)
;;

let serve_tree (t : t) (request : J.t) =
  match G.tool_native_serve_tree t.session request with
  | Error why -> Error why
  | Ok (reply, session) ->
    t.session <- session;
    Ok reply
;;

let serve_line (t : t) (line : string) : string =
  J.render
    (match J.parse line with
     | Error why -> refused (J.NatJson_str why)
     | Ok request ->
       (match serve_tree t request with
        | Ok reply -> reply
        | Error why -> wire_refused why))
;;
