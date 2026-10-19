(* Kit_mcp — MCP 2025-06-18 over stdio, using the generated authoring tool.

   The MCP transport owns JSON-RPC, initialization and framing. Tool.Methods owns the method
   table and the `describe` tool beside it: each tool's listing (its argument schema and its
   hints, from Lean's method descriptors), where the argument schemas name the program's grammar
   and leave it to `describe`, which answers each definition's schema from Lean's table, and the
   schema of every method's result under `Result`;
   Tool.serve owns actions, queries and refusals. Yojson.Raw keeps transport numbers
   exact, including request IDs outside OCaml int. A tool's arguments become the profile's tree
   (Kit.Json.of_raw) inside the request this server writes around them, and Lean reads them.
   Depends on: Effect4_gen.Api_gen, Kit (Kit.Json), Kit_tool, Yojson.

   Behaviours, tested by engine/test/kit/test_mcp.ml:
   M1 Select the supported version; require initialization before tools; never answer a
      notification or execute it as a tool call. Pings can run during initialization.
   M2 List the generated method table, without a hand method list: each tool's listing, rendered
      by one function, with its argument schema and its four behaviour hints (`annotations`). A
      method carries no output schema: every call answers one envelope, whose closed schema is
      `describe`'s `Result`, so `tools/list` holds it once, on request.
   M3 Return the generated reply as structuredContent and identical JSON text. Domain refusals
      set isError. Unknown tools and invalid arguments are JSON-RPC -32602 errors; an argument
      the profile's reader refuses is named in the error's data by its site in the arguments and
      its reason (`Tool.Native.relativeRefusal`).
   M4 Retain request IDs, validate message envelopes, and keep protocol errors outside Tool.serve.
      Transport JSON accepts fractional metadata; tool numbers keep CodecProfile's domain.
   M5 List the generated `describe` tool after the methods, by the same function, with its own
      output schema and hints. A call of it with a definition's name returns that definition's
      schema document, as structuredContent and identical JSON text; any other arguments are a
      -32602 error.

   Scope: stdio, tools, ping and initialization. No HTTP transport or later MCP version is claimed.
   Sources: mcp-spec/docs/specification/2025-06-18/basic/{index,lifecycle,transports}.mdx and
   server/tools.mdx, shelf revision 86f6e0c675afea9a8f233e09b6faf566b126086c. *)

module G = Effect4_gen.Api_gen
module J = Yojson.Raw
module K = Kit.Json

let string s = `Stringlit (Yojson.Safe.to_string (`String s))

let text = function
  | `Stringlit s ->
    (match Yojson.Safe.from_string s with
     | `String value when String.is_valid_utf_8 value -> Some value
     | _ -> None
     | exception Yojson.Json_error _ -> None)
  | _ -> None
;;

let field (key : string) = function
  | `Assoc fields -> List.assoc_opt key fields
  | _ -> None
;;

let string_field key value = Option.bind (field key value) text

let has_string key expected value =
  Option.fold ~none:false ~some:(String.equal expected) (string_field key value)
;;

(* Yojson also admits extensions. The MCP transport accepts JSON alone. *)
let rec standard = function
  | `Null | `Bool _ | `Intlit _ -> true
  | `Stringlit _ as value -> Option.is_some (text value)
  | `Floatlit value -> value <> "NaN" && value <> "Infinity" && value <> "-Infinity"
  | `List values -> List.for_all standard values
  | `Assoc fields ->
    List.for_all (fun (key, value) -> String.is_valid_utf_8 key && standard value) fields
  | `Tuple _ | `Variant _ -> false
;;

let parse line =
  if not (String.is_valid_utf_8 line)
  then Error "Expected UTF-8 JSON"
  else (
    match J.from_string line with
    | value when standard value -> Ok value
    | _ -> Error "Expected JSON without extensions"
    | exception Yojson.Json_error why -> Error why)
;;

let supported_version = "2025-06-18"

type phase =
  | Initial
  | Negotiated
  | Ready

type t =
  { session : Kit_tool.t
  ; tools : J.t list
  ; mutable phase : phase
  }

(* One tool's listing as `tools/list` shows it, with every 2025-06-18 `ToolAnnotations` hint set,
   so no client falls back to a default, and its output schema where the listing carries one. *)
let tool_of (l : G.listing) : J.t =
  let output =
    match l.output_schema with
    | Some schema -> [ "outputSchema", J.from_string schema ]
    | None -> []
  in
  `Assoc
    ([ "name", string l.name
     ; "description", string l.description
     ; "inputSchema", J.from_string l.input_schema
     ]
     @ output
     @ [ ( "annotations"
         , `Assoc
             [ "readOnlyHint", `Bool l.read_only
             ; "destructiveHint", `Bool l.destructive
             ; "idempotentHint", `Bool l.idempotent
             ; "openWorldHint", `Bool l.open_world
             ] )
       ])
;;

let describe : G.describe = G.tool_native_describe

let create () =
  { session = Kit_tool.create ()
  ; tools =
      List.map
        (fun (entry : G.effect4_tool_methods_entry) -> tool_of entry.listing)
        G.tool_native_methods
      @ [ tool_of describe.listing ]
  ; phase = Initial
  }
;;

(* The request this server writes around a tool's arguments: the method's case object, holding
   the arguments, at `payload.<field>`, under the method's name and version 1 (Lean's entry). *)
let envelope (entry : G.effect4_tool_methods_entry) (args : (string * K.t) list) : K.t =
  K.NatJson_obj
    [ "method", K.NatJson_str entry.listing.name
    ; "version", K.NatJson_nat 1
    ; ( "payload"
      , K.NatJson_obj
          [ "_tag", K.NatJson_str entry.kind
          ; entry.field, K.NatJson_obj (("_tag", K.NatJson_str entry.case_name) :: args)
          ] )
    ]
;;

let reply id result = `Assoc [ "jsonrpc", string "2.0"; "id", id; "result", result ]

let failure ?data id code message =
  let detail =
    match data with
    | None -> []
    | Some value -> [ "data", value ]
  in
  `Assoc
    [ "jsonrpc", string "2.0"
    ; "id", id
    ; ( "error"
      , `Assoc
          (("code", `Intlit (string_of_int code)) :: ("message", string message) :: detail)
      )
    ]
;;

let is_refusal value =
  match Option.bind (field "payload" value) (field "result") with
  | Some result -> has_string "_tag" "error" result
  | None -> false
;;

(* A definition's schema document, from Lean's answers. *)
let definition id args =
  match args with
  | [ ("name", name) ] ->
    (match Option.bind (text name) (fun n -> List.assoc_opt n describe.answers) with
     | Some schema ->
       reply
         id
         (`Assoc
             [ ( "content"
               , `List [ `Assoc [ "type", string "text"; "text", string schema ] ] )
             ; "structuredContent", J.from_string schema
             ; "isError", `Bool false
             ])
     | None -> failure id (-32602) "Arguments do not match the tool schema")
  | _ -> failure id (-32602) "Arguments do not match the tool schema"
;;

let call server id name args =
  match
    List.find_opt
      (fun (entry : G.effect4_tool_methods_entry) -> String.equal entry.listing.name name)
      G.tool_native_methods
  with
  | None when String.equal name describe.listing.name -> definition id args
  | None -> failure id (-32602) ("Unknown tool: " ^ name)
  | Some entry ->
    (match K.of_raw (`Assoc args) with
     | Error why ->
       failure
         ~data:(`Assoc [ "refused", string why ])
         id
         (-32602)
         "Arguments do not match the tool schema"
     | Ok (K.NatJson_obj args) ->
       (match Kit_tool.serve_tree server.session (envelope entry args) with
        | Ok answer ->
          let line = K.render answer in
          (match parse line with
           | Ok (`Assoc _ as value) ->
             reply
               id
               (`Assoc
                   [ ( "content"
                     , `List [ `Assoc [ "type", string "text"; "text", string line ] ] )
                   ; "structuredContent", value
                   ; "isError", `Bool (is_refusal value)
                   ])
           | _ -> failure id (-32603) "Tool returned an invalid JSON object")
        | Error why ->
          (* The codec's refusal is the arguments': its site is placed in them. Any other wire
             refusal is this server's own. *)
          let why =
            G.tool_native_relative_refusal
              [ G.JsonStep_key "payload"; G.JsonStep_key entry.field ]
              why
          in
          let data = J.from_string (K.render (Kit_tool.wire_refused why)) in
          (match why with
           | G.Effect4_tool_wire_refusal_codec
               (G.Effect4_tool_codec_profile_refusal_unreadable _) ->
             failure ~data id (-32602) "Arguments do not match the tool schema"
           | _ -> failure ~data id (-32603) "Tool reply cannot cross the wire"))
     | Ok _ -> failure id (-32603) "Tool arguments did not become an object")
;;

let initialize server id params =
  match server.phase with
  | Negotiated | Ready -> failure id (-32600) "Already initialized"
  | Initial ->
    (match
       ( string_field "protocolVersion" params
       , field "capabilities" params
       , field "clientInfo" params )
     with
     | Some _, Some (`Assoc _), Some info
       when Option.is_some (string_field "name" info)
            && Option.is_some (string_field "version" info) ->
       server.phase <- Negotiated;
       reply
         id
         (`Assoc
             [ "protocolVersion", string supported_version
             ; "capabilities", `Assoc [ "tools", `Assoc [] ]
             ; ( "serverInfo"
               , `Assoc [ "name", string "effect4-tool"; "version", string "1" ] )
             ])
     | _ ->
       failure
         id
         (-32602)
         "initialize requires protocolVersion, capabilities and clientInfo")
;;

let request server id method_ params =
  let ready =
    match server.phase with
    | Ready -> true
    | Initial | Negotiated -> false
  in
  match method_ with
  | "initialize" -> initialize server id params
  | "ping" -> reply id (`Assoc [])
  | _ when not ready -> failure id (-32002) "Server is not initialized"
  | "tools/list" ->
    (match field "cursor" params with
     | None -> reply id (`Assoc [ "tools", `List server.tools ])
     | Some _ -> failure id (-32602) "No continuation cursor was issued")
  | "tools/call" ->
    (match string_field "name" params, field "arguments" params with
     | Some name, None -> call server id name []
     | Some name, Some (`Assoc args) -> call server id name args
     | _ -> failure id (-32602) "tools/call requires a name and object arguments")
  | method_ -> failure id (-32601) ("Unknown method: " ^ method_)
;;

(* JSON integers include decimal/exponent notation. For nonzero mantissa M,
   the value is integral exactly when exponent >= fraction digits - trailing zeros.
   Saturation avoids exponent overflow without converting the request ID to a float. *)
let integral_number token =
  let length = String.length token in
  let exponent_at =
    match String.index_opt token 'e' with
    | Some i -> i
    | None -> Option.value (String.index_opt token 'E') ~default:length
  in
  let fraction = ref 0
  and trailing = ref 0
  and nonzero = ref false
  and after_dot = ref false in
  for i = 0 to exponent_at - 1 do
    match token.[i] with
    | '.' -> after_dot := true
    | '-' -> ()
    | digit ->
      if !after_dot then incr fraction;
      if digit = '0'
      then incr trailing
      else (
        nonzero := true;
        trailing := 0)
  done;
  let position = ref (exponent_at + 1)
  and negative = ref false in
  if !position < length
  then
    if token.[!position] = '-'
    then (
      negative := true;
      incr position)
    else if token.[!position] = '+'
    then incr position;
  let magnitude = ref 0
  and cap = length + 1 in
  while !position < length do
    let digit = Char.code token.[!position] - Char.code '0' in
    magnitude
    := if !magnitude > cap / 10 || (!magnitude = cap / 10 && digit > cap mod 10)
       then cap
       else (!magnitude * 10) + digit;
    incr position
  done;
  let exponent = if !negative then - !magnitude else !magnitude in
  (not !nonzero) || exponent >= !fraction - !trailing
;;

let valid_id = function
  | `Intlit _ | `Stringlit _ -> true
  | `Floatlit token -> integral_number token
  | _ -> false
;;

let valid_meta ?(request = true) params =
  match field "_meta" params with
  | None -> true
  | Some (`Assoc _ as meta) ->
    (not request)
    ||
      (match field "progressToken" meta with
      | None -> true
      | Some token -> valid_id token)
  | Some _ -> false
;;

let message server value =
  match value with
  | `Assoc fields ->
    let id = List.assoc_opt "id" fields in
    let response_id =
      match id with
      | Some id when valid_id id -> id
      | _ -> `Null
    in
    if not (has_string "jsonrpc" "2.0" value)
    then Some (failure response_id (-32600) "Expected JSON-RPC 2.0")
    else (
      match string_field "method" value, id with
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
         | Some (`Assoc _ as params) when valid_meta params ->
           Some (request server id method_ params)
         | Some (`Assoc _) ->
           Some
             (failure
                id
                (-32602)
                "_meta must be an object with a string or integer progressToken")
         | Some _ -> Some (failure id (-32602) "params must be an object"))
      | None, Some _
        when Option.is_some (field "result" value) || Option.is_some (field "error" value)
        -> None
      | _ ->
        Some
          (failure
             response_id
             (-32600)
             "Expected a method and a string or integer request ID"))
  | _ -> Some (failure `Null (-32600) "Expected one JSON-RPC object")
;;

let line server input =
  match parse input with
  | Error why -> Some (J.to_string (failure `Null (-32700) why))
  | Ok value -> Option.map (fun reply -> J.to_string reply) (message server value)
;;
