(* test_mcp.ml -- the authoring tool's MCP server (Kit_mcp, `eff mcp`).

   What it is: JSON-RPC messages through Kit_mcp.line, checked against Kit_mcp's behaviours and,
   for tool calls, against the same requests through Kit_tool (the JSON lines shell).
   Depends on: Effect4_kit (Kit, Kit_mcp, Kit_tool), Effect4_gen.Api_gen, Eff_json_text.

   Properties:
   C1  `initialize` names the server; `ping` answers; a notification gets no reply; an unknown
       method is error -32601; a line that is not JSON is error -32700.           tested
   C2  `tools/list` lists one tool per supported method, in `Tool.supportedMethods`' order (the
       `discover` reply's), then `describe`, each with a description and an object
       `inputSchema`.                                                              tested
   C3  `tools/call open` then `tools/call doc` answer the replies Kit_tool gives the same two
       envelopes, as text and structured data, with `isError` false; a stale snapshot is a
       tool error. Unknown tools and malformed calls are protocol errors.         tested
   C4  Initialization selects a supported version. Requests validate their JSON-RPC envelope,
       parameters and lifecycle. Notifications never execute tools or answer.     tested
   C5  `describe` answers, for each definition it names, a schema document pointing at that
       definition under its own `$defs`, as structured data and identical text; every definition
       a tool's schema leaves to it is one it answers; other arguments are -32602.  tested

   Run: cd ocaml && opam exec --switch=effect4 -- dune test --force engine/test/kit *)

open Effect4_kit
module J = Eff_json_text

let failures = ref 0
let check name ok =
  Printf.printf "%s  %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let parse s = match Kit.Json.parse s with Ok j -> Some j | Error _ -> None
let field k = function Some (J.Object f) -> List.assoc_opt k f | _ -> None
let rpc ?id meth params =
  J.render (J.Object ([ ("jsonrpc", J.String "2.0"); ("method", J.String meth); ("params", J.Object params) ]
                      @ match id with Some i -> [ ("id", J.Int i) ] | None -> []))

let init_params version =
  [ ("protocolVersion", J.String version); ("capabilities", J.Object []);
    ("clientInfo", J.Object [ ("name", J.String "effect4-test"); ("version", J.String "1") ]) ]

let ready () =
  let s = Kit_mcp.create () in
  ignore (Kit_mcp.line s (rpc ~id:0 "initialize" (init_params "2025-06-18")));
  ignore (Kit_mcp.line s (rpc "notifications/initialized" []));
  s

(* C1 *)
let () =
  let s = Kit_mcp.create () in
  let call m = Option.bind (Kit_mcp.line s m) parse in
  let initialized = call (rpc ~id:1 "initialize" (init_params "2025-06-18")) in
  check "C1 initialize names the server"
    (field "name" (field "serverInfo" (field "result" initialized))
     = Some (J.String "effect4-tool"));
  check "C1 ping answers" (field "result" (call (rpc ~id:2 "ping" [])) = Some (J.Object []));
  check "C1 a notification gets no reply" (Kit_mcp.line s (rpc "notifications/initialized" []) = None);
  check "C1 an unknown method is -32601"
    (field "code" (field "error" (call (rpc ~id:3 "resources/list" []))) = Some (J.Int (-32601)));
  check "C1 a line that is not JSON is -32700"
    (field "code" (field "error" (Option.bind (Kit_mcp.line s "{") parse)) = Some (J.Int (-32700)))

(* C2 *)
let () =
  let s = ready () in
  let tools = match field "tools" (field "result" (Option.bind (Kit_mcp.line s (rpc ~id:1 "tools/list" [])) parse)) with
    | Some (J.Array ts) -> ts | _ -> [] in
  let names = List.filter_map (fun t -> match field "name" (Some t) with Some (J.String n) -> Some n | _ -> None) tools in
  (* the discover reply lists the supported methods, in order *)
  let discover = Kit_tool.serve_line (Kit_tool.create ())
      "{\"method\":\"discover\",\"payload\":{\"_tag\":\"ask\",\"q\":{\"_tag\":\"discover\"}},\"version\":1}" in
  let supported =
    let rec find = function
      | J.Object f -> (match List.assoc_opt "supported" f with
          | Some (J.Array ms) -> Some (List.filter_map (function J.Array (J.String m :: _) -> Some m | _ -> None) ms)
          | _ -> List.find_map (fun (_, v) -> find v) f)
      | J.Array xs -> List.find_map find xs
      | _ -> None in
    Option.bind (parse discover) find in
  check (Printf.sprintf "C2 tools/list lists %d tools" (List.length names)) (List.length names = 20);
  check "C2 the tools are the supported methods, in order, then describe"
    (Option.map (fun ms -> ms @ [ "describe" ]) supported = Some names);
  check "C2 every tool has a description and an object schema"
    (List.for_all (fun t ->
       (match field "description" (Some t) with Some (J.String d) -> d <> "" | _ -> false)
       && field "type" (field "inputSchema" (Some t)) = Some (J.String "object")) tools)

(* C3 *)
let () =
  let first = In_channel.with_open_bin "tool-requests.jsonl" In_channel.input_line |> Option.get in
  let open_args = match field "payload" (parse first) with
    | Some (J.Object p) -> (match List.assoc_opt "a" p with
        | Some (J.Object a) -> List.filter (fun (k, _) -> k <> "_tag") a | _ -> [])
    | _ -> [] in
  let doc_line = "{\"method\":\"doc\",\"payload\":{\"_tag\":\"ask\",\"q\":{\"_tag\":\"doc\",\"at_\":null}},\"version\":1}" in
  let s = ready () and t = Kit_tool.create () in
  let text r = match field "content" (field "result" r) with
    | Some (J.Array [ c ]) -> (match field "text" (Some c) with Some (J.String x) -> parse x | _ -> None)
    | _ -> None in
  let is_error r = field "isError" (field "result" r) in
  let call id name args = Option.bind (Kit_mcp.line s (rpc ~id "tools/call" [ ("name", J.String name); ("arguments", J.Object args) ])) parse in
  let opened = call 1 "open" open_args in
  check "C3 open answers Kit_tool's reply" (text opened = parse (Kit_tool.serve_line t first) && text opened <> None);
  check "C3 open is no error" (is_error opened = Some (J.Bool false));
  check "C3 structured open equals text" (field "structuredContent" (field "result" opened) = text opened);
  let doc = call 2 "doc" [ ("at_", J.Null) ] in
  check "C3 doc reads the opened document, as Kit_tool does" (text doc = parse (Kit_tool.serve_line t doc_line) && text doc <> None);
  let stale = call 3 "publish" [ ("at_", J.Object [ ("doc", J.Object [ ("generation", J.Int 0); ("name", J.String "default") ]); ("revision", J.Int 9) ]) ] in
  check "C3 a call at a stale snapshot is a tool error" (is_error stale = Some (J.Bool true));
  check "C3 structured refusal equals text" (field "structuredContent" (field "result" stale) = text stale);
  check "C3 an unknown tool is -32602"
    (field "code" (field "error" (call 4 "nope" [])) = Some (J.Int (-32602)));
  let notification_args = ("name", J.String "notification") :: List.remove_assoc "name" open_args in
  check "C3 a valid open notification gets no reply"
    (Kit_mcp.line s (rpc "tools/call" [("name", J.String "open"); ("arguments", J.Object notification_args)]) = None);
  check "C3 a valid open notification leaves the document unchanged"
    (text (call 5 "doc" [("at_", J.Null)]) = text doc)

(* C4: protocol errors do not reach Tool.serve. *)
let () =
  let s = Kit_mcp.create () in
  let call line = Option.bind (Kit_mcp.line s line) parse in
  let code r = field "code" (field "error" r) in
  check "C4 tools require initialization"
    (code (call (rpc ~id:1 "tools/list" [])) = Some (J.Int (-32002)));
  check "C4 initialization requires its fields"
    (code (call (rpc ~id:2 "initialize" [])) = Some (J.Int (-32602)));
  check "C4 unsupported version selects 2025-06-18"
    (field "protocolVersion" (field "result" (call (rpc ~id:3 "initialize" (init_params "unknown"))))
     = Some (J.String "2025-06-18"));
  check "C4 tools wait for initialized notification"
    (code (call (rpc ~id:4 "tools/list" [])) = Some (J.Int (-32002)));
  check "C4 malformed initialized notification stays silent"
    (Kit_mcp.line s "{\"jsonrpc\":\"2.0\",\"method\":\"notifications/initialized\",\"params\":7}" = None);
  check "C4 malformed notification does not initialize"
    (code (call (rpc ~id:41 "tools/list" [])) = Some (J.Int (-32002)));
  ignore (Kit_mcp.line s (rpc "notifications/initialized" [("_meta", J.Int 7)]));
  check "C4 malformed notification metadata does not initialize"
    (code (call (rpc ~id:42 "tools/list" [])) = Some (J.Int (-32002)));
  ignore (Kit_mcp.line s "{\"jsonrpc\":\"2.0\",\"method\":\"notifications/initialized\",\"params\":{\"_meta\":{\"progressToken\":0.5}}}");
  check "C4 notification metadata permits arbitrary JSON values"
    (field "result" (call (rpc ~id:43 "tools/list" [])) <> None);
  check "C4 duplicate initialize is -32600"
    (code (call (rpc ~id:5 "initialize" (init_params "2025-06-18"))) = Some (J.Int (-32600)));
  check "C4 wrong JSON-RPC version is -32600"
    (code (call "{\"jsonrpc\":\"1.0\",\"id\":6,\"method\":\"ping\"}") = Some (J.Int (-32600)));
  check "C4 null request id is -32600"
    (code (call "{\"jsonrpc\":\"2.0\",\"id\":null,\"method\":\"ping\"}") = Some (J.Int (-32600)));
  check "C4 string request id is retained"
    (field "id" (call "{\"jsonrpc\":\"2.0\",\"id\":\"request-7\",\"method\":\"ping\"}") = Some (J.String "request-7"));
  check "C4 non-object params are -32602"
    (code (call "{\"jsonrpc\":\"2.0\",\"id\":8,\"method\":\"tools/call\",\"params\":[]}") = Some (J.Int (-32602)));
  check "C4 non-object arguments are -32602"
    (code (call "{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"tools/call\",\"params\":{\"name\":\"open\",\"arguments\":[]}}")
     = Some (J.Int (-32602)));
  check "C4 unreadable arguments are -32602"
    (code (call (rpc ~id:10 "tools/call" [("name", J.String "open"); ("arguments", J.Object [])]))
     = Some (J.Int (-32602)));
  check "C4 arguments outside the tool numeric profile are -32602"
    (code (call "{\"jsonrpc\":\"2.0\",\"id\":101,\"method\":\"tools/call\",\"params\":{\"name\":\"doc\",\"arguments\":{\"at_\":0.5}}}")
     = Some (J.Int (-32602)));
  check "C4 unknown notification gets no reply" (Kit_mcp.line s (rpc "unknown" []) = None);
  check "C4 tool notification does not execute"
    (Kit_mcp.line s (rpc "tools/call" [("name", J.String "reset")]) = None);
  check "C4 valid fractional metadata is JSON"
    (field "result" (call "{\"jsonrpc\":\"2.0\",\"id\":11,\"method\":\"ping\",\"params\":{\"_meta\":{\"x\":0.5}}}")
     = Some (J.Object []));
  check "C4 metadata must be an object"
    (code (call (rpc ~id:12 "ping" [("_meta", J.Int 7)])) = Some (J.Int (-32602)));
  check "C4 invalid leading-zero number is a parse error"
    (code (call "{\"jsonrpc\":\"2.0\",\"id\":01,\"method\":\"ping\"}") = Some (J.Int (-32700)));
  check "C4 invalid UTF-8 is a parse error"
    (code (call "{\"jsonrpc\":\"2.0\",\"id\":\"\255\",\"method\":\"ping\"}") = Some (J.Int (-32700)));
  check "C4 lone high surrogate is refused without throwing"
    (code (call "{\"jsonrpc\":\"2.0\",\"id\":\"\\ud800\",\"method\":\"ping\"}") = Some (J.Int (-32700)));
  check "C4 lone low surrogate is refused without emitting invalid UTF-8"
    (code (call "{\"jsonrpc\":\"2.0\",\"id\":\"\\udc00\",\"method\":\"ping\"}") = Some (J.Int (-32700)));
  let numeric_id token =
    let input = "{\"jsonrpc\":\"2.0\",\"id\":" ^ token ^ ",\"method\":\"ping\"}" in
    match Kit_mcp.line s input with
    | Some output -> (match Yojson.Raw.from_string output with
        | `Assoc fields -> List.assoc_opt "id" fields = Some (Yojson.Raw.from_string token)
            && List.mem_assoc "result" fields
        | _ -> false)
    | None -> false in
  List.iter (fun token -> check ("C4 exact integral ID " ^ token) (numeric_id token))
    ["1.0"; "1e2"; "1200e-2"; "-0.000e-999999999999999999999";
     "1e999999999999999999999"];
  List.iter (fun token -> check ("C4 fractional ID refused " ^ token) (not (numeric_id token)))
    ["1.1"; "1e-2"; "1201e-2"; "1e-999999999999999999999"];
  check "C4 integral progress token is accepted"
    (field "result" (call "{\"jsonrpc\":\"2.0\",\"id\":13,\"method\":\"ping\",\"params\":{\"_meta\":{\"progressToken\":1.0}}}")
     = Some (J.Object []));
  check "C4 a batch is not an MCP request"
    (code (call "[]") = Some (J.Int (-32600)))

(* C5 *)
let () =
  let s = ready () in
  let tools = match field "tools" (field "result" (Option.bind (Kit_mcp.line s (rpc ~id:1 "tools/list" [])) parse)) with
    | Some (J.Array ts) -> ts | _ -> [] in
  let describe = List.find_opt (fun t -> field "name" (Some t) = Some (J.String "describe")) tools in
  let names = match field "enum" (field "name" (field "properties" (Option.bind describe (fun t -> field "inputSchema" (Some t))))) with
    | Some (J.Array ns) -> List.filter_map (function J.String n -> Some n | _ -> None) ns
    | _ -> [] in
  let call id args = Option.bind (Kit_mcp.line s (rpc ~id "tools/call" [ ("name", J.String "describe"); ("arguments", J.Object args) ])) parse in
  let text r = match field "content" (field "result" r) with
    | Some (J.Array [ c ]) -> (match field "text" (Some c) with Some (J.String x) -> parse x | _ -> None)
    | _ -> None in
  let code r = field "code" (field "error" r) in
  check "C5 describe names the definitions it answers" (List.mem "Eff" names);
  check "C5 each answer points at its definition under its own $defs, structured as its text"
    (List.for_all (fun n ->
       let r = call 2 [ ("name", J.String n) ] in
       let a = text r in
       field "$ref" a = Some (J.String ("#/$defs/" ^ n)) && field n (field "$defs" a) <> None
       && field "structuredContent" (field "result" r) = a
       && field "isError" (field "result" r) = Some (J.Bool false)) names);
  (* a definition a schema leaves to describe is a $defs entry that only says so *)
  let left = List.concat_map (fun t -> match field "$defs" (field "inputSchema" (Some t)) with
      | Some (J.Object ds) -> List.filter_map (fun (k, d) ->
          match field "properties" (Some d), field "oneOf" (Some d), field "description" (Some d) with
          | None, None, Some _ -> Some k | _ -> None) ds
      | _ -> []) tools in
  check "C5 every definition a schema leaves to describe is one it answers"
    (left <> [] && List.for_all (fun k -> List.mem k names) left);
  check "C5 another name is -32602" (code (call 3 [ ("name", J.String "Nope") ]) = Some (J.Int (-32602)));
  check "C5 another argument is -32602"
    (code (call 4 [ ("name", J.String "Eff"); ("x", J.Int 1) ]) = Some (J.Int (-32602)))

let () =
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED") !failures;
  exit (if !failures = 0 then 0 else 1)
