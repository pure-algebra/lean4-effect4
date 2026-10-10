from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, time

packet = Path(__file__).resolve().parent
owner = Path("/Users/pooks/Dev/lean4-effect4-wt/module-layers")
files = [owner / n for n in [
    "harness/truth/generated/pDefsModuleLayer.ts",
    "harness/truth/prelude.ts",
    "harness/truth/tsconfig.json",
    "harness/truth/node_modules/@typescript/native-preview/package.json",
    "harness/truth/node_modules/effect/package.json",
    "Test/Program/DefinitionsControls.lean",
    "src/Effect4/Codegen/Print.lean",
    "src/Effect4/Laws/Codegen/Module.lean",
]]
def hashes():
    return {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
result = {"started_at": datetime.now(timezone.utc).isoformat(),
          "owner_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=owner, text=True).strip(),
          "before": hashes(), "commands": []}
tsgo = str(owner / "harness/truth/node_modules/.bin/tsgo")
commands = [
    ("tsgo-version", [tsgo, "--version"]),
    ("typecheck", [tsgo, "--project", str(packet / "tsconfig.json")]),
    ("bun-version", ["bun", "--version"]),
    ("runtime", ["bun", str(packet / "runtime.ts")]),
]
for name, args in commands:
    started = time.monotonic()
    run = subprocess.run(args, cwd=packet, text=True, capture_output=True, timeout=90)
    output = run.stdout + run.stderr
    (packet / (name + ".out")).write_text(output)
    result["commands"].append({"name": name, "argv": args, "exit": run.returncode,
                               "seconds": time.monotonic() - started, "output": name + ".out"})
    print(name, run.returncode, output, flush=True)
result["after"] = hashes()
result["inputs_unchanged"] = result["before"] == result["after"]
truth = json.loads((owner / "harness/truth/result.json").read_text())
result["owner_reported_case"] = [{k: v for k, v in r.items() if k not in ["host", "hostSync"]}
                                 for r in truth["rows"] if r["program"] == "pDefsModuleLayer"]
result["owner_reported_case_sha256"] = hashlib.sha256((owner / "harness/truth/result.json").read_bytes()).hexdigest()
result["limits"] = ["One generated module and its imports", "Recorded Lean result, not a fresh Lean run",
                    "No schedule or memo count observation", "No full gate run"]
(packet / "result.json").write_text(json.dumps(result, indent=2) + "\n")
assert all(c["exit"] == 0 for c in result["commands"])
assert result["inputs_unchanged"]
