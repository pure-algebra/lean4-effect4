(* Kit_mcp — the authoring tool as a Model Context Protocol server (`eff mcp`).

   What it is: JSON-RPC 2.0 over stdio, one message a line, for an agent. The tool table is Lean's
   (`Tool.Methods.entries`, src/Effect4/Tool/Methods.lean, lowered into ../../gen/api_gen.ml as
   `tool_native_methods`): one tool per method of the protocol, with what it does and the JSON
   Schema of its arguments, derived from the request's shape document. A `tools/call` builds the
   method's request envelope from its arguments and serves it through one Kit_tool session, which
   holds the document, the fills, the runs and the checker memo from call to call. Nothing here
   names a method or a field by hand.
   Depends on: Effect4_gen.Api_gen, Kit, Kit_tool.

   Behaviours:
   M1 `initialize` names the server; `ping` answers; a notification gets no reply; any other
      request with an unknown method is a JSON-RPC error (-32601); a line that is not JSON is a
      parse error (-32700).                                             tested (test_mcp)
   M2 `tools/list` lists one tool per method of `Tool.supportedMethods`, in its order, each with
      its description and its argument schema.                          tested (test_mcp)
   M3 `tools/call` of a method answers the tool's reply line as text; `isError` is whether the
      reply is a refusal of the wire or the tool. A name that is no method is a tool error.
                                                                       tested (test_mcp)
   M4 Calls share one session: an `open` then a `doc` reads the opened document, as the same two
      lines through Kit_tool do.                                         tested (test_mcp) *)

module G = Effect4_gen.Api_gen
module J = Eff_json_text

type t = { session : Kit_tool.t; tools : J.t list }

let tool_of (e : G.effect4_tool_methods_entry) : J.t =
  let schema = match Kit.Json.parse e.schema with Ok j -> j | Error _ -> J.Object [] in
  J.Object [ ("name", J.String e.name); ("description", J.String e.description); ("inputSchema", schema) ]

let create () = { session = Kit_tool.create (); tools = List.map tool_of G.tool_native_methods }

(* The request envelope a method's arguments make: the Request case the method builds, holding its
   Action or Query case with the arguments as fields. *)
let envelope (e : G.effect4_tool_methods_entry) (args : (string * J.t) list) : J.t =
  let payload = J.Object [ ("_tag", J.String e.kind); (e.field, J.Object (("_tag", J.String e.case_name) :: args)) ] in
  J.Object [ ("method", J.String e.name); ("version", J.Int 1); ("payload", payload) ]

let is_refusal (reply : string) =
  match Kit.Json.parse reply with
  | Ok (J.Object [ ("refused", _) ]) -> true
  | Ok (J.Object fields) -> (
    match List.assoc_opt "payload" fields with
    | Some (J.Object p) -> (
      match List.assoc_opt "result" p with
      | Some (J.Object r) -> List.assoc_opt "_tag" r = Some (J.String "error")
      | _ -> false)
    | _ -> false)
  | _ -> false

let text_result (text : string) (is_error : bool) : J.t =
  J.Object [ ("content", J.Array [ J.Object [ ("type", J.String "text"); ("text", J.String text) ] ]);
             ("isError", J.Bool is_error) ]

let call (t : t) (name : string) (args : (string * J.t) list) : J.t =
  match List.find_opt (fun (e : G.effect4_tool_methods_entry) -> String.equal e.name name) G.tool_native_methods with
  | None -> text_result ("no tool " ^ name) true
  | Some e ->
    let reply = Kit_tool.serve_line t.session (J.render (envelope e args)) in
    text_result reply (is_refusal reply)

(* One JSON-RPC message to its reply, or none for a notification. *)
let message (t : t) (msg : J.t) : J.t option =
  let reply id result = J.Object [ ("jsonrpc", J.String "2.0"); ("id", id); ("result", result) ] in
  let failure id code text =
    J.Object [ ("jsonrpc", J.String "2.0"); ("id", id);
               ("error", J.Object [ ("code", J.Int code); ("message", J.String text) ]) ] in
  match msg with
  | J.Object fields -> (
    let field k = List.assoc_opt k fields in
    let params = match field "params" with Some (J.Object p) -> p | _ -> [] in
    match field "method", field "id" with
    | Some (J.String "initialize"), Some id ->
      let version = match List.assoc_opt "protocolVersion" params with Some v -> v | None -> J.String "2025-06-18" in
      Some (reply id (J.Object [ ("protocolVersion", version);
                                 ("capabilities", J.Object [ ("tools", J.Object []) ]);
                                 ("serverInfo", J.Object [ ("name", J.String "effect4-tool"); ("version", J.String "1") ]) ]))
    | Some (J.String "ping"), Some id -> Some (reply id (J.Object []))
    | Some (J.String "tools/list"), Some id -> Some (reply id (J.Object [ ("tools", J.Array t.tools) ]))
    | Some (J.String "tools/call"), Some id ->
      let name = match List.assoc_opt "name" params with Some (J.String n) -> n | _ -> "" in
      let args = match List.assoc_opt "arguments" params with Some (J.Object a) -> a | _ -> [] in
      Some (reply id (call t name args))
    | Some (J.String _), None -> None
    | Some (J.String m), Some id -> Some (failure id (-32601) ("unknown method " ^ m))
    | _, Some id -> Some (failure id (-32600) "not a request")
    | _, None -> None)
  | _ -> Some (failure J.Null (-32600) "not a request")

let line (t : t) (text : string) : string option =
  match Kit.Json.parse text with
  | Error why ->
    Some (J.render (J.Object [ ("jsonrpc", J.String "2.0"); ("id", J.Null);
                               ("error", J.Object [ ("code", J.Int (-32700)); ("message", J.String why) ]) ]))
  | Ok msg -> Option.map J.render (message t msg)
