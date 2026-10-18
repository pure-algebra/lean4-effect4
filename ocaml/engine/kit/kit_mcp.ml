(* Kit_mcp — MCP 2025-06-18 over stdio, using the generated authoring tool.

   The MCP transport owns JSON-RPC, initialization and framing. Tool.Methods owns the method
   table and the `describe` tool beside it (the schemas name the program's grammar and leave it to
   `describe`, which answers each definition's schema from Lean's table); Tool.serve owns actions,
   queries and refusals. Yojson.Raw keeps transport numbers
   exact, including request IDs outside OCaml int. Kit_tool admits tool arguments separately.
   Depends on: Effect4_gen.Api_gen, Kit_tool, Yojson.

   Behaviours, tested by engine/test/kit/test_mcp.ml:
   M1 Select the supported version; require initialization before tools; never answer a
      notification or execute it as a tool call. Pings can run during initialization.
   M2 List the generated method table and argument schemas, without a hand method list.
   M3 Return the generated reply as structuredContent and identical JSON text. Domain refusals
      set isError. Unknown tools and invalid arguments are JSON-RPC -32602 errors.
   M4 Retain request IDs, validate message envelopes, and keep protocol errors outside Tool.serve.
      Transport JSON accepts fractional metadata; tool numbers keep CodecProfile's domain.
   M5 List the generated `describe` tool after the methods. A call of it with a definition's name
      returns that definition's schema document, as structuredContent and identical JSON text;
      any other arguments are a -32602 error.

   Scope: stdio, tools, ping and initialization. No HTTP transport or later MCP version is claimed.
   Sources: mcp-spec/docs/specification/2025-06-18/basic/{index,lifecycle,transports}.mdx and
   server/tools.mdx, shelf revision 86f6e0c675afea9a8f233e09b6faf566b126086c. *)

module G = Effect4_gen.Api_gen
module J = Yojson.Raw

let string s = `Stringlit (Yojson.Safe.to_string (`String s))
let text = function
  | `Stringlit s ->
    (match Yojson.Safe.from_string s with
     | `String value when String.is_valid_utf_8 value -> Some value
     | _ -> None
     | exception Yojson.Json_error _ -> None)
  | _ -> None
let field (key : string) = function `Assoc fields -> List.assoc_opt key fields | _ -> None
let string_field key value = Option.bind (field key value) text
let has_string key expected value =
  Option.fold ~none:false ~some:(String.equal expected) (string_field key value)

(* Yojson also admits extensions. The MCP transport accepts JSON alone. *)
let rec standard = function
  | `Null | `Bool _ | `Intlit _ -> true
  | `Stringlit _ as value -> Option.is_some (text value)
  | `Floatlit value -> value <> "NaN" && value <> "Infinity" && value <> "-Infinity"
  | `List values -> List.for_all standard values
  | `Assoc fields -> List.for_all (fun (key, value) -> String.is_valid_utf_8 key && standard value) fields
  | `Tuple _ | `Variant _ -> false

let parse line =
  if not (String.is_valid_utf_8 line) then Error "Expected UTF-8 JSON" else
  match J.from_string line with
  | value when standard value -> Ok value
  | _ -> Error "Expected JSON without extensions"
  | exception Yojson.Json_error why -> Error why

let supported_version = "2025-06-18"
type phase = Initial | Negotiated | Ready
type t = { session : Kit_tool.t; tools : J.t list; mutable phase : phase }

let tool_of (entry : G.effect4_tool_methods_entry) : J.t =
  `Assoc [ ("name", string entry.name); ("description", string entry.description);
           ("inputSchema", J.from_string entry.schema) ]

let describe : G.describe = G.tool_native_describe

let describe_tool : J.t =
  `Assoc [ ("name", string describe.name); ("description", string describe.description);
           ("inputSchema", J.from_string describe.schema) ]

let create () =
  { session = Kit_tool.create (); tools = List.map tool_of G.tool_native_methods @ [ describe_tool ];
    phase = Initial }

let envelope (entry : G.effect4_tool_methods_entry) args : J.t =
  let payload = `Assoc [ ("_tag", string entry.kind);
    (entry.field, `Assoc (("_tag", string entry.case_name) :: args)) ] in
  `Assoc [ ("method", string entry.name); ("version", `Intlit "1"); ("payload", payload) ]

let reply id result = `Assoc [ ("jsonrpc", string "2.0"); ("id", id); ("result", result) ]
let failure ?data id code message =
  let detail = match data with None -> [] | Some value -> [("data", value)] in
  `Assoc [ ("jsonrpc", string "2.0"); ("id", id);
           ("error", `Assoc (("code", `Intlit (string_of_int code)) :: ("message", string message) :: detail)) ]

let is_refusal value =
  match Option.bind (field "payload" value) (field "result") with
  | Some result -> has_string "_tag" "error" result
  | None -> false

(* A definition's schema document, from Lean's answers. *)
let definition id args =
  match args with
  | [ ("name", name) ] ->
    (match Option.bind (text name) (fun n -> List.assoc_opt n describe.answers) with
     | Some schema -> reply id (`Assoc [
         ("content", `List [`Assoc [("type", string "text"); ("text", string schema)]]);
         ("structuredContent", J.from_string schema); ("isError", `Bool false) ])
     | None -> failure id (-32602) "Arguments do not match the tool schema")
  | _ -> failure id (-32602) "Arguments do not match the tool schema"

let call server id name args =
  match List.find_opt (fun (entry : G.effect4_tool_methods_entry) -> String.equal entry.name name)
      G.tool_native_methods with
  | None when String.equal name describe.name -> definition id args
  | None -> failure id (-32602) ("Unknown tool: " ^ name)
  | Some entry ->
    let line = Kit_tool.serve_line server.session (J.to_string (envelope entry args)) in
    match parse line with
    | Ok (`Assoc _ as value) ->
      (match field "refused" value with
       | Some why ->
         let input_fault = Option.is_some (text why)
           || (has_string "_tag" "codec" why && has_string "why" "unreadable" why) in
         let internal = not input_fault in
         failure ~data:value id (if internal then -32603 else -32602)
           (if internal then "Tool reply cannot cross the wire" else "Arguments do not match the tool schema")
       | None -> reply id (`Assoc [
           ("content", `List [`Assoc [("type", string "text"); ("text", string line)]]);
           ("structuredContent", value); ("isError", `Bool (is_refusal value)) ]))
    | _ -> failure id (-32603) "Tool returned an invalid JSON object"

let initialize server id params =
  match server.phase with
  | Negotiated | Ready -> failure id (-32600) "Already initialized"
  | Initial ->
    match string_field "protocolVersion" params, field "capabilities" params, field "clientInfo" params with
    | Some _, Some (`Assoc _), Some info
        when Option.is_some (string_field "name" info) && Option.is_some (string_field "version" info) ->
      server.phase <- Negotiated;
      reply id (`Assoc [ ("protocolVersion", string supported_version);
        ("capabilities", `Assoc [("tools", `Assoc [])]);
        ("serverInfo", `Assoc [("name", string "effect4-tool"); ("version", string "1")]) ])
    | _ -> failure id (-32602) "initialize requires protocolVersion, capabilities and clientInfo"

let request server id method_ params =
  let ready = match server.phase with Ready -> true | Initial | Negotiated -> false in
  match method_ with
  | "initialize" -> initialize server id params
  | "ping" -> reply id (`Assoc [])
  | _ when not ready -> failure id (-32002) "Server is not initialized"
  | "tools/list" ->
    (match field "cursor" params with
     | None -> reply id (`Assoc [("tools", `List server.tools)])
     | Some _ -> failure id (-32602) "No continuation cursor was issued")
  | "tools/call" ->
    (match string_field "name" params, field "arguments" params with
     | Some name, None -> call server id name []
     | Some name, Some (`Assoc args) -> call server id name args
     | _ -> failure id (-32602) "tools/call requires a name and object arguments")
  | method_ -> failure id (-32601) ("Unknown method: " ^ method_)

(* JSON integers include decimal/exponent notation. For nonzero mantissa M,
   the value is integral exactly when exponent >= fraction digits - trailing zeros.
   Saturation avoids exponent overflow without converting the request ID to a float. *)
let integral_number token =
  let length = String.length token in
  let exponent_at = match String.index_opt token 'e' with
    | Some i -> i
    | None -> Option.value (String.index_opt token 'E') ~default:length in
  let fraction = ref 0 and trailing = ref 0 and nonzero = ref false and after_dot = ref false in
  for i = 0 to exponent_at - 1 do
    match token.[i] with
    | '.' -> after_dot := true
    | '-' -> ()
    | digit ->
      if !after_dot then incr fraction;
      if digit = '0' then incr trailing else (nonzero := true; trailing := 0)
  done;
  let position = ref (exponent_at + 1) and negative = ref false in
  if !position < length then (
    if token.[!position] = '-' then (negative := true; incr position)
    else if token.[!position] = '+' then incr position);
  let magnitude = ref 0 and cap = length + 1 in
  while !position < length do
    let digit = Char.code token.[!position] - Char.code '0' in
    magnitude := if !magnitude > cap / 10
      || (!magnitude = cap / 10 && digit > cap mod 10)
      then cap else !magnitude * 10 + digit;
    incr position
  done;
  let exponent = if !negative then - !magnitude else !magnitude in
  not !nonzero || exponent >= !fraction - !trailing

let valid_id = function
  | `Intlit _ | `Stringlit _ -> true
  | `Floatlit token -> integral_number token
  | _ -> false
let valid_meta ?(request = true) params =
  match field "_meta" params with
  | None -> true
  | Some (`Assoc _ as meta) ->
    not request || (match field "progressToken" meta with None -> true | Some token -> valid_id token)
  | Some _ -> false

let message server value =
  match value with
  | `Assoc fields ->
    let id = List.assoc_opt "id" fields in
    let response_id = match id with Some id when valid_id id -> id | _ -> `Null in
    if not (has_string "jsonrpc" "2.0" value) then
      Some (failure response_id (-32600) "Expected JSON-RPC 2.0")
    else
      (match string_field "method" value, id with
       | Some method_, None ->
         (match method_, server.phase, field "params" value with
          | "notifications/initialized", Negotiated, None -> server.phase <- Ready
          | "notifications/initialized", Negotiated, Some (`Assoc _ as params)
              when valid_meta ~request:false params -> server.phase <- Ready
          | _ -> ());
         None
       | Some method_, Some id when valid_id id ->
         (match field "params" value with
          | None -> Some (request server id method_ (`Assoc []))
          | Some (`Assoc _ as params) when valid_meta params -> Some (request server id method_ params)
          | Some (`Assoc _) -> Some (failure id (-32602) "_meta must be an object with a string or integer progressToken")
          | Some _ -> Some (failure id (-32602) "params must be an object"))
       | None, Some _ when Option.is_some (field "result" value) || Option.is_some (field "error" value) -> None
       | _ -> Some (failure response_id (-32600) "Expected a method and a string or integer request ID"))
  | _ -> Some (failure `Null (-32600) "Expected one JSON-RPC object")

let line server input =
  match parse input with
  | Error why -> Some (J.to_string (failure `Null (-32700) why))
  | Ok value -> Option.map J.to_string (message server value)
