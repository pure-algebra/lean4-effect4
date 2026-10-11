#!/usr/bin/env python3
"""Reproduce the pinned loop-meaning review without production edits."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[2]
BASE = "74cc52c5c66d750d5875bb745fd26cdb00d8617a"
ENV = {**os.environ, "LEAN_NUM_THREADS": "3"}
MODULES = ["ReviewMeaning", "ReviewControls", "ReviewBoundaryControls", "FoldProbe", "ReviewAudit"]
BUILD = ["lake", "build", "Effect4.Laws.Program.DenoteRowsB",
         "Effect4.Laws.Program.Agreement.LoopCalls", "Effect4.Laws.Program.Agreement.HostedLoop",
         "Effect4.Laws.Api.SessionMeaningLoop", "ProofGraph.Plan", "ProofGraph.AxiomAudit",
         "Test.Dogfood.Scenario.TodoPaged", "Effect4.Laws.Machine.ScopeMachine"]
results = []

def run(label, command):
    result = subprocess.run(command, cwd=ROOT, env=ENV, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (PACKET / (label + ".log")).write_text(result.stdout + "\nExit: " + str(result.returncode) + "\n")
    results.append({"label": label, "command": command, "exit": result.returncode})
    print(label + ": " + str(result.returncode), flush=True)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    return result.stdout

run("source-diff", ["git", "diff", "--exit-code", BASE, "--", ".",
                    ":(exclude)docs/research/2026-10-10-host-meaning-landing-review/**"])
run("build", BUILD)
for name in MODULES:
    run(name, ["lake", "env", "bash", "-c",
        'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" -DwarningAsError=true -o "$1/$2.olean" "$1/$2.lean"',
        "review", str(PACKET), name])
run("language", ["python3", "scripts/check-language.py", "--strict", str(PACKET / "README.md")])
run("diff-check", ["git", "diff", "--check"])
source = ROOT / "docs/research/2026-10-10-host-meaning-widening"
assert (PACKET / "ReviewControls.lean").read_text() == (source / "Controls.lean").read_text().replace(
    "import Meaning\n", "import ReviewMeaning\n")
assert (PACKET / "ReviewBoundaryControls.lean").read_text() == (source / "BoundaryControls.lean").read_text().replace(
    "import Controls\n", "import ReviewControls\n")
claims = re.findall(r'id := "(rows-loop-[^"]+)"', (ROOT / "tools/ProofGraph/Registry.lean").read_text())
generated = (ROOT / "generated/semantics.md").read_text()
static = {"registered_loop_claims": claims, "claims_absent_from_generated_report": [c for c in claims if c not in generated]}
(PACKET / "integration.json").write_text(json.dumps(static, indent=2) + "\n")
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
files = [p for p in PACKET.iterdir() if p.suffix in (".lean", ".log", ".md", ".py")]
record = {"reviewed_commit": BASE, "commands": results,
          "guard_count": sum((PACKET / (m + ".lean")).read_text().count("#guard ") for m in MODULES),
          "package_pins": [{k: x.get(k) for k in ("name", "rev")} for x in manifest["packages"]],
          "file_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}}
(PACKET / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
print("PASS: " + str(record["guard_count"]) + " production controls; scoped proof and fold audits")
