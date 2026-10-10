#!/usr/bin/env python3
"""Reproduce the isolated CX review at its pinned source commit."""
from pathlib import Path
import hashlib
import json
import os
import subprocess

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[2]
BASE = "71799e477d85ff943b1c0f2f291ace98f92613f2"
ENV = {**os.environ, "LEAN_NUM_THREADS": "3"}
results = []

def run(label, command):
    result = subprocess.run(command, cwd=ROOT, env=ENV, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (PACKET / (label + ".log")).write_text(result.stdout + "\nExit: " + str(result.returncode) + "\n")
    results.append({"label": label, "command": command, "exit": result.returncode})
    print(label + ": " + str(result.returncode), flush=True)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    return result.stdout

run("source-diff", ["git", "diff", "--exit-code", BASE, "--", ".",
                    ":(exclude)docs/research/2026-10-10-cx-lexical-review/**"])
run("build", ["lake", "build", "Effect4.Laws.Program.Typed.AdmittedSource",
              "Test.Program.InvokeControls", "ProofGraph.Why", "ProofGraph.Plan", "ProofGraph.AxiomAudit"])
for name in ["Lexical", "Controls", "Graph", "Audit"]:
    run(name, ["lake", "env", "bash", "-c",
        'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" -DwarningAsError=true -o "$1/$2.olean" "$1/$2.lean"',
        "review", str(PACKET), name])
run("language", ["python3", "scripts/check-language.py", "--strict", str(PACKET / "README.md")])
run("diff-check", ["git", "diff", "--check"])
original = ROOT / "docs/research/2026-10-10-cx-lexical-scope/Lexical.lean"
assert (PACKET / "Lexical.lean").read_bytes() == original.read_bytes()
files = sorted(p for p in PACKET.iterdir() if p.suffix in (".lean", ".md", ".log", ".py", ".diff", ".txt"))
record = {"reviewed_commit": BASE, "commands": results,
          "finite_guard_count": (PACKET / "Controls.lean").read_text().count("#guard "),
          "candidate_example_count": (PACKET / "Controls.lean").read_text().count("\nexample "),
          "original_lexical_probe_exact_copy": True,
          "file_sha256": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
(PACKET / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
print("PASS: " + str(record["finite_guard_count"]) + " finite guards and " +
      str(record["candidate_example_count"]) + " candidate examples")
