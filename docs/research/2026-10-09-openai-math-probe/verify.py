"""Run the bounded local checks serially and retain their measured results."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REL = HERE.relative_to(ROOT)
ENV = {**os.environ, "LEAN_NUM_THREADS": "3"}
REPORT = HERE / "verification.json"
results = []


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot():
    files = sorted(p for p in HERE.iterdir() if p.suffix in {".lean", ".py", ".sh", ".md"})
    files += [ROOT / p for p in [
        "src/Effect4/Schema/Codec.lean",
        "src/Effect4/Laws/Schema/Codec.lean",
        "src/Effect4/Laws/Program/Typed/AnswerSchema.lean",
        "Test/Codegen/DataCodec.lean",
        "harness/truth/schema-codec/Emit.lean",
    ]]
    return {str(p.relative_to(ROOT)): digest(p) for p in files}


record = {
    "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "build_base": subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
    "lean_num_threads": ENV["LEAN_NUM_THREADS"],
    "source_sha256": snapshot(),
    "checks": results,
    "scope": "Narrow local Lean proofs and finite controls; no upstream build, host run or full sweep.",
}


def save():
    record["all_passed"] = bool(results) and all(r["exit_code"] == 0 for r in results)
    REPORT.write_text(json.dumps(record, indent=2) + "\n")


def run(name, command, log):
    print(f"Checking {name}", flush=True)
    started = time.monotonic()
    with (HERE / log).open("w") as out:
        done = subprocess.run(command, cwd=ROOT, env=ENV, stdout=out, stderr=subprocess.STDOUT)
    results.append({"name": name, "command": command, "log": str(REL / log),
                    "exit_code": done.returncode,
                    "elapsed_seconds": round(time.monotonic() - started, 3),
                    "log_sha256": digest(HERE / log)})
    save()
    if done.returncode:
        print((HERE / log).read_text()[-8000:])
        raise SystemExit(done.returncode)


def lean(name, file, log):
    # The shell has constant text. Paths are positional arguments, never interpolated code.
    run(name, ["lake", "env", "sh", "-c",
        'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" -DwarningAsError=true -o "$2" "$3"',
        "research-check", str(HERE), str(HERE / (file[:-5] + ".olean")), str(HERE / file)], log)


run("research imports and codec laws", ["lake", "build", "Tools.View.FlowLaws",
    "Effect4.Laws.Schema.Codec", "Test.Codegen.DataCodec",
    "Test.Codegen.SchemaGenerationContract", "Test.Program.AnswerSchema"], "narrow-build.log")
lean("cached fold agreement", "TyCache.lean", "ty-cache-check.log")
lean("cyclic dependency summaries", "Reachability.lean", "reachability-check.log")
lean("actual proof collector", "ProofGraphProbe.lean", "proof-graph-check.log")
lean("application flow connector", "FlowReachability.lean", "flow-check.log")
lean("inherited context control", "Controls.lean", "context-check.log")
lean("prepared codec controls", "PreparedCodecControls.lean", "prepared-codec-check.log")
lean("prepared codec compiler inspection", "PreparedCodecReuse.lean", "prepared-codec-reuse.log")
run("independent finite graph controls", [sys.executable, str(HERE / "graph_controls.py")],
    "graph-results.json")
run("existing codec harness", ["lake", "env", "lean", "-DwarningAsError=true", "--run",
    "harness/truth/schema-codec/Emit.lean", str(HERE / "codec-after.ts")], "codec-harness.log")

before = HERE / "codec-before.ts"
after = HERE / "codec-after.ts"
matched = before.read_bytes() == after.read_bytes()
results.append({"name": "codec byte comparison", "exit_code": 0 if matched else 1,
    "baseline_sha256": digest(before), "actual_sha256": digest(after),
    "baseline_bytes": before.stat().st_size, "actual_bytes": after.stat().st_size})
save()
if not matched:
    raise SystemExit("Codec output differs from the retained pre-change baseline")

run("research prose", [sys.executable, "scripts/check-language.py", "--strict",
    str(REL / "README.md"), str(REL / "OPERATIONAL-PLAN.md")], "language-check.log")
if snapshot() != record["source_sha256"]:
    results.append({"name": "source stability", "exit_code": 1})
    save()
    raise SystemExit("Sources changed during verification")
record["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
save()
print("PASS: bounded checks and pre-change byte comparison")
