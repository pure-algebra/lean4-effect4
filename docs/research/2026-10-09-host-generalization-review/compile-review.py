"""Compile frozen review sources without replacing any production source."""
from pathlib import Path
import json
import os
import subprocess
import sys

review = Path(__file__).resolve().parent
root = review.parents[2]
phase = sys.argv[1] if len(sys.argv) > 1 else "co4"
snapshot = review / ({"h9": "snapshot-h9/src", "checker": "snapshot-checker/src"}.get(phase, "snapshot/src"))
overlay = root / ".lake/host-coalgebra-review-overlay"
logs = review / "checks" / phase
logs.mkdir(parents=True, exist_ok=True)
modules = [
    "Effect4.Laws.Program.HostRuns",
    "Effect4.Laws.Program.Agreement.Segment",
    "Effect4.Laws.Program.Agreement.Calls",
    "Effect4.Laws.Program.Agreement.Hosted",
    "Effect4.Laws.Api.SessionMeaning",
]
if phase == "h9":
    modules = modules[-2:]
if phase == "checker":
    modules = modules[-1:]
results = []
for module in modules:
    relative = Path(*module.split("."))
    source = (snapshot / relative).with_suffix(".lean")
    output = (overlay / relative).with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    for suffix in [".olean", ".ilean", ".olean.private", ".olean.server"]:
        old = (overlay / relative).with_suffix(suffix)
        if old.exists():
            old.unlink()
    cmd = ["lake", "env", "bash", "-c",
           'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"',
           "review", str(overlay), "-DwarningAsError=true", "--root=" + str(snapshot),
           "-o", str(output), str(source)]
    print("CHECK " + module, flush=True)
    proc = subprocess.run(cmd, cwd=root, env={**os.environ, "LEAN_NUM_THREADS": "3"},
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (logs / (module + ".log")).write_text(proc.stdout)
    results.append({"module": module, "command": cmd, "exit_code": proc.returncode})
    (logs / "build-results.json").write_text(json.dumps(results, indent=2) + "\n")
    print("RESULT " + str(proc.returncode), flush=True)
    if proc.returncode:
        print(proc.stdout, flush=True)
        sys.exit(proc.returncode)
print("PASS: frozen source modules for " + phase, flush=True)
