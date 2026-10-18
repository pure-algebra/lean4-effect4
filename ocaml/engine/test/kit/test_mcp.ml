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
       envelopes, as text, with `isError` false; a call at a stale snapshot is a tool error
       (`isError` true); a name that is no method is a tool error.                 tested
   C4  `describe` answers, for each definition its schema names, a schema document: an object
       pointing at that definition under its own `$defs`; every definition a tool's schema leaves
       to it is one it answers; another name is a tool error.                      tested

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

(* C1 *)
let () =
  let s = Kit_mcp.create () in
  let call m = Option.bind (Kit_mcp.line s m) parse in
  check "C1 initialize names the server"
    (field "name" (field "serverInfo" (field "result" (call (rpc ~id:1 "initialize" []))))
     = Some (J.String "effect4-tool"));
  check "C1 ping answers" (field "result" (call (rpc ~id:2 "ping" [])) = Some (J.Object []));
  check "C1 a notification gets no reply" (Kit_mcp.line s (rpc "notifications/initialized" []) = None);
  check "C1 an unknown method is -32601"
    (field "code" (field "error" (call (rpc ~id:3 "resources/list" []))) = Some (J.Int (-32601)));
  check "C1 a line that is not JSON is -32700"
    (field "code" (field "error" (Option.bind (Kit_mcp.line s "{") parse)) = Some (J.Int (-32700)))

(* C2 *)
let () =
  let s = Kit_mcp.create () in
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
  let s = Kit_mcp.create () and t = Kit_tool.create () in
  let text r = match field "content" (field "result" r) with
    | Some (J.Array [ c ]) -> (match field "text" (Some c) with Some (J.String x) -> parse x | _ -> None)
    | _ -> None in
  let is_error r = field "isError" (field "result" r) in
  let call id name args = Option.bind (Kit_mcp.line s (rpc ~id "tools/call" [ ("name", J.String name); ("arguments", J.Object args) ])) parse in
  let opened = call 1 "open" open_args in
  check "C3 open answers Kit_tool's reply" (text opened = parse (Kit_tool.serve_line t first) && text opened <> None);
  check "C3 open is no error" (is_error opened = Some (J.Bool false));
  let doc = call 2 "doc" [ ("at_", J.Null) ] in
  check "C3 doc reads the opened document, as Kit_tool does" (text doc = parse (Kit_tool.serve_line t doc_line) && text doc <> None);
  let stale = call 3 "publish" [ ("at_", J.Object [ ("doc", J.Object [ ("generation", J.Int 0); ("name", J.String "default") ]); ("revision", J.Int 9) ]) ] in
  check "C3 a call at a stale snapshot is a tool error" (is_error stale = Some (J.Bool true));
  check "C3 a name that is no method is a tool error" (is_error (call 4 "nope" []) = Some (J.Bool true))

(* C4 *)
let () =
  let s = Kit_mcp.create () in
  let tools = match field "tools" (field "result" (Option.bind (Kit_mcp.line s (rpc ~id:1 "tools/list" [])) parse)) with
    | Some (J.Array ts) -> ts | _ -> [] in
  let names = match field "describe" (Some (J.Object (List.filter_map (fun t ->
      match field "name" (Some t) with Some (J.String n) -> Some (n, t) | _ -> None) tools))) with
    | Some t -> (match field "enum" (field "name" (field "properties" (field "inputSchema" (Some t)))) with
        | Some (J.Array ns) -> List.filter_map (function J.String n -> Some n | _ -> None) ns | _ -> [])
    | None -> [] in
  let call id args = Option.bind (Kit_mcp.line s (rpc ~id "tools/call" [ ("name", J.String "describe"); ("arguments", J.Object args) ])) parse in
  let answer n = match field "content" (field "result" (call 2 [ ("name", J.String n) ])) with
    | Some (J.Array [ c ]) -> (match field "text" (Some c) with Some (J.String x) -> parse x | _ -> None)
    | _ -> None in
  check "C4 describe names the definitions it answers" (List.mem "Eff" names);
  check "C4 each answer points at its definition under its own $defs"
    (List.for_all (fun n ->
       let a = answer n in
       field "$ref" a = Some (J.String ("#/$defs/" ^ n)) && field n (field "$defs" a) <> None) names);
  (* a definition a schema leaves to describe is a $defs entry that only says so *)
  let left = List.concat_map (fun t -> match field "$defs" (field "inputSchema" (Some t)) with
      | Some (J.Object ds) -> List.filter_map (fun (k, d) ->
          match field "properties" (Some d), field "oneOf" (Some d), field "description" (Some d) with
          | None, None, Some _ -> Some k | _ -> None) ds
      | _ -> []) tools in
  check "C4 every definition a schema leaves to describe is one it answers"
    (left <> [] && List.for_all (fun k -> List.mem k names) left);
  check "C4 another name is a tool error"
    (field "isError" (field "result" (call 3 [ ("name", J.String "Nope") ])) = Some (J.Bool true))

let () =
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED") !failures;
  exit (if !failures = 0 then 0 else 1)
