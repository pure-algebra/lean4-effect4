#!/usr/bin/env python3
"""Finite stdio checks against the MCP 2025-06-18 upstream schemas.

Run with jsonschema 4.25.1. The native test_mcp suite remains part of check-ocaml.
This probe exercises the actual executable, including initialization and framing.
It does not certify HTTP, cancellation during computation, or later protocol versions.

Every listed tool carries its four behaviour hints (`annotations`). No method tool carries an
`outputSchema`: every method answers a `Wire.Envelope Reply`, whose closed schema is `describe`'s
answer for `Result`, and only `describe` lists one, for its schema documents. Each method's
structured result validates against `Result`, and each `describe` answer against `describe`'s own
output schema. Red control: the bare `Reply` schema (the envelope's payload, with the same
definitions) refuses the enveloped result it does not describe, and accepts its payload.
"""

import argparse
import json
from pathlib import Path
import subprocess

from jsonschema import Draft7Validator, Draft202012Validator


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", required=True, type=Path)
    parser.add_argument("--schema", required=True, type=Path)
    args = parser.parse_args()
    schema = json.loads(args.schema.read_text())
    definitions = schema["definitions"]
    checks = 0

    def validate(kind, value):
        nonlocal checks
        Draft7Validator({"$ref": f"#/definitions/{kind}", "definitions": definitions}).validate(value)
        checks += 1

    fixture = Path(__file__).resolve().parents[1] / "Test/fixtures/session/requests.jsonl"
    first = json.loads(fixture.read_text().splitlines()[0])
    open_args = {k: v for k, v in first["payload"]["a"].items() if k != "_tag"}
    requests = [
        {"jsonrpc": "2.0", "id": "init", "method": "initialize", "params": {
            "protocolVersion": "unsupported", "capabilities": {},
            "clientInfo": {"name": "effect4-schema-probe", "version": "1"}}},
        {"jsonrpc": "2.0", "method": "notifications/initialized", "params": {"_meta": {"progressToken": 0.5}}},
        {"jsonrpc": "2.0", "id": 1, "method": "tools/list"},
        {"jsonrpc": "2.0", "id": 2, "method": "tools/call", "params": {"name": "open", "arguments": open_args}},
        {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "doc", "arguments": {"at_": None}}},
        {"jsonrpc": "2.0", "id": 4, "method": "tools/call", "params": {"name": "publish", "arguments": {
            "at_": {"doc": {"name": "default", "generation": 0}, "revision": 999}}}},
        {"jsonrpc": "2.0", "id": 5, "method": "tools/call", "params": {"name": "missing"}},
        {"jsonrpc": "2.0", "id": 6, "method": "tools/call", "params": {"name": "open", "arguments": []}},
        {"jsonrpc": "2.0", "id": 7, "method": "tools/call", "params": {"name": "open", "arguments": {}}},
        {"jsonrpc": "2.0", "id": 8, "method": "tools/call", "params": {"name": "doc", "arguments": {"at_": None}}},
        {"jsonrpc": "2.0", "id": 2**64, "method": "ping", "params": {"_meta": {"fraction": 0.5}}},
        {"jsonrpc": "2.0", "method": "tools/call", "params": {"name": "open", "arguments": {**open_args, "name": "notification"}}},
        {"jsonrpc": "2.0", "id": 9, "method": "tools/call", "params": {"name": "doc", "arguments": {"at_": None}}},
        {"jsonrpc": "2.0", "id": 10.0, "method": "ping", "params": {"_meta": {"progressToken": 100.0}}},
        {"jsonrpc": "2.0", "id": 11, "method": "tools/call", "params": {"name": "doc", "arguments": {"at_": 0.5}}},
        {"jsonrpc": "2.0", "id": 12, "method": "tools/call", "params": {"name": "describe", "arguments": {"name": "Eff"}}},
        {"jsonrpc": "2.0", "id": 13, "method": "tools/call", "params": {"name": "describe", "arguments": {"name": "Nope"}}},
        {"jsonrpc": "2.0", "id": 14, "method": "tools/call", "params": {"name": "describe", "arguments": {"name": "Result"}}},
    ]
    for request in requests:
        validate("JSONRPCRequest" if "id" in request else "JSONRPCNotification", request)
    validate("InitializeRequest", requests[0])
    validate("InitializedNotification", requests[1])
    process = subprocess.run([str(args.binary.resolve()), "mcp"],
        input="\n".join(map(json.dumps, requests)) + "\n", text=True, capture_output=True, timeout=60)
    assert process.returncode == 0, process.stderr
    lines = process.stdout.splitlines()
    replies = [json.loads(line) for line in lines]
    expected = [r["id"] for r in requests if "id" in r]
    assert [r["id"] for r in replies] == expected, "stdout framing, notification silence or request IDs differ"
    by_id = {reply["id"]: reply for reply in replies}
    for reply in replies:
        validate("JSONRPCError" if "error" in reply else "JSONRPCResponse", reply)
    validate("InitializeResult", by_id["init"]["result"])
    assert by_id["init"]["result"]["protocolVersion"] == "2025-06-18"
    validate("ListToolsResult", by_id[1]["result"])
    tools = {tool["name"]: tool for tool in by_id[1]["result"]["tools"]}
    assert len(tools) == len(by_id[1]["result"]["tools"]) and tools
    hints = ("readOnlyHint", "destructiveHint", "idempotentHint", "openWorldHint")
    for tool in tools.values():
        Draft202012Validator.check_schema(tool["inputSchema"])
        checks += 1
        annotations = tool.get("annotations")
        assert isinstance(annotations, dict), tool["name"] + " has no annotations"
        assert all(isinstance(annotations.get(h), bool) for h in hints), tool["name"] + " lacks a hint"
        if tool["name"] == "describe":
            Draft202012Validator.check_schema(tool["outputSchema"])
            checks += 1
        else:
            assert "outputSchema" not in tool, tool["name"] + " carries an outputSchema"
    # the classification: a query, `describe` included, is read-only, and an action is not
    assert tools["doc"]["annotations"]["readOnlyHint"] is True
    assert tools["describe"]["annotations"]["readOnlyHint"] is True
    assert tools["open"]["annotations"]["readOnlyHint"] is False
    for request in requests:
        if request.get("id") in (2, 3, 4, 8, 9, 12):
            params = request["params"]
            Draft202012Validator(tools[params["name"]]["inputSchema"]).validate(params["arguments"])
            checks += 1
    names = {r["id"]: r["params"]["name"] for r in requests if "id" in r and r["method"] == "tools/call"}
    result_schema = by_id[14]["result"]["structuredContent"]
    Draft202012Validator.check_schema(result_schema)
    checks += 1
    for request_id in (2, 3, 4, 8, 9, 12, 14):
        result = by_id[request_id]["result"]
        validate("CallToolResult", result)
        assert json.loads(result["content"][0]["text"]) == result["structuredContent"]
        schema = tools["describe"]["outputSchema"] if names[request_id] == "describe" else result_schema
        Draft202012Validator(schema).validate(result["structuredContent"])
        checks += 1
    # red control: the bare Reply schema refuses the enveloped result, and accepts its payload
    defs = result_schema["$defs"]
    bare = {**defs["Result"]["properties"]["payload"], "$defs": defs}
    Draft202012Validator.check_schema(bare)
    for request_id in (2, 3, 4):
        enveloped = by_id[request_id]["result"]["structuredContent"]
        assert not Draft202012Validator(bare).is_valid(enveloped), "a bare Reply schema accepts the envelope"
        assert Draft202012Validator(bare).is_valid(enveloped["payload"]), "the bare Reply schema refuses the payload"
        checks += 2
    assert by_id[2]["result"]["isError"] is False
    assert by_id[4]["result"]["isError"] is True
    assert by_id[12]["result"]["isError"] is False
    Draft202012Validator.check_schema(by_id[12]["result"]["structuredContent"])
    checks += 1
    for request_id in (5, 6, 7, 11, 13):
        assert by_id[request_id]["error"]["code"] == -32602
    assert by_id[3]["result"] == by_id[8]["result"] == by_id[9]["result"], "refusals or notifications changed the document"
    print(json.dumps({"status": "PASS", "protocol": "2025-06-18", "schema_checks": checks,
        "input_messages": len(requests), "output_messages": len(replies), "tools": len(tools),
        "annotated_tools": sum(1 for t in tools.values() if "annotations" in t),
        "output_schema_tools": sum(1 for t in tools.values() if "outputSchema" in t),
        "tools_list_bytes": len(lines[[r["id"] for r in replies].index(1)].encode()),
        "input_schema_bytes": sum(len(json.dumps(t["inputSchema"])) for t in tools.values()),
        "output_schema_bytes": sum(len(json.dumps(t["outputSchema"])) for t in tools.values() if "outputSchema" in t),
        "result_schema_bytes": len(json.dumps(result_schema)),
        "exact_large_id": str(2**64),
        "scope": "finite stdio trace; official schemas, generated argument schemas and describe's answers"}))


if __name__ == "__main__":
    main()
