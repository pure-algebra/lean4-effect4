#!/usr/bin/env python3
"""Recheck the theory packet, one bounded Lake invocation at a time."""
from __future__ import annotations

import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[2]
BASE = "540ee8ccb279dc8b808487e428e0e9a02d500a3f"
MODULES = ["Meaning", "Goals", "Controls", "BoundaryControls", "Audit"]
ENV = dict(os.environ, LEAN_NUM_THREADS="3")
EVIDENCE = PACKET / "verification.json"
receipt: dict = {"base": BASE, "started_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
                 "evidence_kind": "theory, finite Lean evaluations, and a local axiom gate",
                 "commands": [], "passed": False}


def save() -> None:
    EVIDENCE.write_text(json.dumps(receipt, indent=2) + "\n")


def run(label: str, argv: list[str]) -> None:
    log = PACKET / f"{label}.log"
    start = dt.datetime.now(dt.timezone.utc).isoformat()
    print(f"Checking {label}", flush=True)
    with log.open("w") as output:
        output.write(f"Command: {shlex.join(argv)}\nLEAN_NUM_THREADS=3\nStarted: {start}\n")
        output.flush()
        result = subprocess.run(argv, cwd=ROOT, env=ENV, stdout=output, stderr=subprocess.STDOUT)
    receipt["commands"].append({"label": label, "argv": argv, "exit_code": result.returncode,
                                "log": log.name, "started_utc": start,
                                "finished_utc": dt.datetime.now(dt.timezone.utc).isoformat()})
    save()
    if result.returncode:
        print(log.read_text(), file=sys.stderr)
        raise SystemExit(result.returncode)


if Path.cwd().resolve() != ROOT:
    raise SystemExit(f"Run from the isolated packet worktree: {ROOT}")

# Check the exact source base, including the dependency pin. Never reset or update it here.
run("source-base", ["git", "diff", "--exit-code", BASE, "--", ".",
                    f":(exclude){PACKET.relative_to(ROOT)}/**"])
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
effects = next(p for p in manifest["packages"] if p["name"] == "effects")
pin = subprocess.check_output(["git", "rev-parse", "HEAD"],
                              cwd=ROOT / ".lake/packages/effects", text=True).strip()
receipt["effects_expected"] = effects["rev"]
receipt["effects_actual"] = pin
if pin != effects["rev"]:
    save()
    raise SystemExit("The local Effects checkout does not match the pinned revision.")

# This is the requested narrow cone, not the Test root or an axiom-gate sweep.
run("narrow-build", ["lake", "build", "Effect4.Laws.Api.SessionMeaning",
                     "Effect4.Laws.Api.HostDrive", "Effect4.Laws.Program.Folds.DenoteRows",
                     "Test.Dogfood.Scenario.TodoPaged", "ProofGraph.AxiomAudit", "ProofGraph.Plan",
                     "Effect4.Laws.Machine.ScopeMachine"])

for module in MODULES:
    run(module, ["lake", "env", "sh", "-c",
                 'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" -DwarningAsError=true '
                 '-o "$1/$2.olean" "$1/$2.lean"',
                 "host-meaning-check", str(PACKET), module])

run("language", [sys.executable, "scripts/check-language.py", "--strict",
                 str(PACKET.relative_to(ROOT) / "README.md")])
run("diff-check", ["git", "diff", "--check"])

# Reject forbidden tactics and direct unfinished terms in this isolated source.
probes = [PACKET / f"{name}.lean" for name in MODULES]
for file in probes:
    code = re.sub(r"/-.*?-/|--[^\n]*", "", file.read_text(), flags=re.S)
    if re.search(r"\b(sorry|native_decide|simp_all|partial|unsafe|axiom|extern|implemented_by)\b"
                 r"|\bfirst\s*\||\btry\b", code):
        raise SystemExit(f"Forbidden source construct in {file.name}")
for name in ["Controls", "BoundaryControls"]:
    if re.search(r"^import Goals\b", (PACKET / f"{name}.lean").read_text(), flags=re.M):
        raise SystemExit("A finite control must not import the open goal.")

receipt["finite_guards"] = sum(len(re.findall(r"^#guard\b", f.read_text(), flags=re.M)) for f in probes)
receipt["planned_goals"] = sum(len(re.findall(r"^proof_goal\b", f.read_text(), flags=re.M)) for f in probes)
receipt["source_sha256"] = {f.name: hashlib.sha256(f.read_bytes()).hexdigest()
                             for f in probes + [PACKET / "README.md", Path(__file__).resolve()]}
receipt["log_sha256"] = {c["log"]: hashlib.sha256((PACKET / c["log"]).read_bytes()).hexdigest()
                          for c in receipt["commands"]}
receipt["passed"] = True
receipt["finished_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
save()
print(f"PASS: {receipt['finite_guards']} finite guards; {receipt['planned_goals']} open planned goal; "
      "all recorded commands returned zero.")
