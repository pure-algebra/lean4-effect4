#!/usr/bin/env python3
"""Finite protocol, edit-preview, and rendering checks against public MCP schemas."""
from pathlib import Path
import hashlib, json, os, selectors, subprocess, sys, time
sys.path.insert(0, os.environ.get("MCP_VALIDATOR_PATH", "/private/tmp/effect4-mcp-jsonschema"))
import jsonschema

packet = Path(__file__).resolve().parent
root = packet.parents[3]
schema_path = Path(os.environ.get("MCP_SCHEMA", "/private/tmp/effect4-mcp-schema-2026-07-28.json"))
schema = json.loads(schema_path.read_text())
schema_source = json.loads((packet / "schema-source.json").read_text())
expected_sha = schema_source["sha256"]
assert hashlib.sha256(schema_path.read_bytes()).hexdigest() == expected_sha
validators = {n: jsonschema.Draft202012Validator({**schema, "$ref": "#/$defs/" + n})
              for n in ["DiscoverResultResponse", "ListToolsResultResponse", "CallToolResultResponse", "JSONRPCErrorResponse", "UnsupportedProtocolVersionError"]}
source = root / "Test/fixtures/session/requests.jsonl"
fixture = [json.loads(line) for line in source.read_text().splitlines()]
base = {"program": fixture[0]["program"], "holes": "040000000000000000", "path": []}
meta = {"io.modelcontextprotocol/protocolVersion": "2026-07-28", "io.modelcontextprotocol/clientCapabilities": {}}
requests, responses, checks = [], [], []
started = time.perf_counter()
errfile = (packet / "driver.stderr.log").open("w")
proc = subprocess.Popen(["lake", "env", "lean", "--run", str(packet / "Preview.lean")],
    cwd=root, env=dict(os.environ, LEAN_NUM_THREADS="3"), stdin=subprocess.PIPE,
    stdout=subprocess.PIPE, stderr=errfile, text=True, bufsize=1)
sel = selectors.DefaultSelector(); sel.register(proc.stdout, selectors.EVENT_READ)

def ask(method, params=None, schema_name=None, **override):
    request = {"jsonrpc": "2.0", "id": len(requests)+1, "method": method,
               "params": {"_meta": dict(meta), **(params or {})}, **override}
    requests.append(request)
    proc.stdin.write(json.dumps(request)+"\n"); proc.stdin.flush()
    if not sel.select(45): raise RuntimeError("driver reply timeout")
    line = proc.stdout.readline()
    if not line: raise RuntimeError("driver stopped: " + (packet / "driver.stderr.log").read_text())
    response = json.loads(line); responses.append(response)
    if schema_name: validators[schema_name].validate(response)
    return response

def tool(name, args):
    return ask("tools/call", {"name": name, "arguments": args}, "CallToolResultResponse")["result"]

def check(name, test):
    assert test, name
    checks.append(name)

try:
    discover = ask("server/discover", schema_name="DiscoverResultResponse")
    check("discovery version", discover["result"]["supportedVersions"] == ["2026-07-28"])
    listing = ask("tools/list", schema_name="ListToolsResultResponse")["result"]
    tools = {t["name"]: t for t in listing["tools"]}
    check("four fixed tools", len(tools) == 4)
    for t in tools.values(): jsonschema.Draft202012Validator.check_schema(t["inputSchema"])
    first = tool("effect4.inspect", base)["structuredContent"]
    check("inspect admitted", first["answer"]["ok"] and not first["published"])
    fillargs = {**base, "path": fixture[2]["path"], "replacement": fixture[2]["replacement"]}
    jsonschema.Draft202012Validator(tools["effect4.fillPreview"]["inputSchema"]).validate(fillargs)
    filled = tool("effect4.fillPreview", fillargs)["structuredContent"]
    check("fill changes preview", filled["snapshot"]["program"] != base["program"] and not filled["published"])
    check("same-type fill splices", filled["answer"]["result"]["delta"]["kind"] == "spliced")
    decimal = ask("tools/call", {"name": "effect4.inspect", "arguments": {**base, "path": [0.0]}},
                  "CallToolResultResponse", id=1.0)
    check("decimal integer request id accepted", decimal["id"] == 1)
    check("decimal integer path accepted", decimal["result"]["structuredContent"]["path"] == [0])
    old = tool("effect4.inspect", base)["structuredContent"]
    check("old snapshot unchanged after preview", first == old)
    changed = tool("effect4.inspect", {**filled["snapshot"], "path": []})["structuredContent"]
    check("explicit new snapshot reads", changed["snapshot"] == filled["snapshot"])
    check("return to earlier snapshot independent", tool("effect4.inspect", base)["structuredContent"] == first)
    omitted = tool("effect4.omitPreview", {**base, "path": fixture[6]["path"], "holeName": "previewHole"})["structuredContent"]
    check("omission carries new hole table", omitted["snapshot"]["holes"] != base["holes"])
    image = tool("effect4.renderPreview", {**omitted["snapshot"], "path": []})["structuredContent"]
    check("render returns SVG", image["svg"].startswith("<svg"))
    (packet / "preview.svg").write_text(image["svg"])
    check("render retains hole context", image["snapshot"] == omitted["snapshot"])
    bad = tool("effect4.inspect", {**base, "program": "00"})
    check("nondecoding snapshot is tool error", bad["isError"])
    check("invalid snapshot leaves cache usable", tool("effect4.inspect", base)["structuredContent"] == first)
    bad_args = [({**base, "path": [-1]}, "negative path"),
                ({**base, "path": [0.5]}, "fractional path"),
                ({**base, "program": "00\n"}, "newline in hex"),
                ({**base, "path": [9007199254740992]}, "unsafe integer path"),
                ({**base, "extra": True}, "extra field"),
                ({**base, "holes": base["holes"].upper()+"Ff"}, "noncanonical hex"),
                ({"path": []}, "missing snapshot")]
    for args, label in bad_args:
        validator = jsonschema.Draft202012Validator(tools["effect4.inspect"]["inputSchema"])
        check(label+" independently refused", not validator.is_valid(args))
        out = ask("tools/call", {"name": "effect4.inspect", "arguments": args}, "JSONRPCErrorResponse")
        check(label+" adapter refused", out["error"]["code"] == -32602)
    for method in ["tools/list", "server/discover"]:
        out = ask(method, {"_meta": {**meta, "io.modelcontextprotocol/protocolVersion": "2025-11-25"}},
                  "UnsupportedProtocolVersionError")
        check(method + " unsupported version refused with data", out["error"]["data"] ==
              {"requested": "2025-11-25", "supported": ["2026-07-28"]})
    out = ask("tools/list", {"_meta": {}}, "JSONRPCErrorResponse")
    check("metadata required each time", out["error"]["code"] == -32602)
    out = ask("not/a/method", schema_name="JSONRPCErrorResponse")
    check("unknown method refused", out["error"]["code"] == -32601)
    out = ask("tools/list", schema_name="JSONRPCErrorResponse", id=None)
    check("null id refused", out["error"]["code"] == -32600)
    for badid in [None, {}, 0.5]:
        out = ask(0, schema_name="JSONRPCErrorResponse", id=badid)
        check("malformed method does not echo invalid id " + repr(badid), "id" not in out)
    # A notification precedes a request: the next line must answer the request.
    notification = {"jsonrpc": "2.0", "method": "notifications/cancelled", "params": {"requestId": 999}}
    requests.append(notification)
    proc.stdin.write(json.dumps(notification)+"\n"); proc.stdin.flush()
    out = ask("tools/list", schema_name="ListToolsResultResponse")
    check("notification has no reply", out["id"] == requests[-1]["id"])
    check("tool list independent of earlier calls", out["result"] == listing)
finally:
    proc.stdin.close()
    proc.wait(timeout=20)
    errfile.close()
    (packet / "requests.jsonl").write_text("".join(json.dumps(x)+"\n" for x in requests))
    (packet / "responses.jsonl").write_text("".join(json.dumps(x)+"\n" for x in responses))
assert proc.returncode == 0
record = {"checked_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
    "schema_url": schema_source["url"],
    "schema_repository_commit": schema_source["repository_commit"],
    "schema_sha256": expected_sha, "validator": "jsonschema 4.25.1 / Draft202012Validator",
    "checks": checks, "requests": len(requests), "elapsed_seconds": time.perf_counter()-started,
    "driver_exit": proc.returncode,
    "sources_sha256": {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in
        [packet / "Preview.lean", root / "tools/Tools/Session/Snapshot.lean"]}}
(packet / "protocol-results.json").write_text(json.dumps(record,indent=2)+"\n")
print(json.dumps(record,indent=2))
