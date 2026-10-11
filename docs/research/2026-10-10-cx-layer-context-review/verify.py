#!/usr/bin/env python3
"""Serialize the pinned source check, narrow build, finite controls, and trust check."""
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
from datetime import datetime, timezone

packet = Path(__file__).resolve().parent
repo = packet.parents[2]
reviewed = "f00008eeaef00b67fe93cfd0327754c9f42694ee"
env = dict(os.environ, LEAN_NUM_THREADS="3")
report = {"reviewed_commit": reviewed, "checks": {}}

def checked(name, args):
    started = datetime.now(timezone.utc).isoformat()
    result = subprocess.run(args, cwd=repo, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = "$ " + shlex.join(args) + "\n" + result.stdout + "\nExit: " + str(result.returncode) + "\n"
    (packet / (name + ".log")).write_text(log)
    report["checks"][name] = {"command": args, "started_utc": started, "exit": result.returncode,
        "log_sha256": hashlib.sha256(log.encode()).hexdigest()}
    print(name + ": " + str(result.returncode), flush=True)
    if result.returncode:
        print(result.stdout, flush=True)
        (packet / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
        raise SystemExit(result.returncode)

checked("source-diff", ["git", "diff", "--exit-code", reviewed, "--", "src", "tools", "Test", "lakefile.toml", "lake-manifest.json"])
checked("build", ["lake", "build", "Effect4.Api", "Effect4.Laws.Program.Typed.Scope", "Effect4.Laws.Program.ReferenceTyping", "ProofGraph.AxiomAudit"])
for name in ("Controls", "Audit"):
    checked(name, ["lake", "env", "sh", "-c",
        'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" -DwarningAsError=true -o "$1/$2.olean" "$1/$2.lean"',
        "cx-layer-context-review", str(packet), name])
report["source_sha256"] = {}
for name in ("src/Effect4/Program/Checker.lean", "src/Effect4/Program/Definitions.lean", "src/Effect4/Program/Fold.lean",
             "src/Effect4/Laws/Program/Signature.lean", "src/Effect4/Laws/Program/ReferenceTyping.lean",
             "src/Effect4/Program/Compile.lean", "src/Effect4/Machine/Stores.lean",
             "src/Effect4/Laws/Program/Typed/Scope.lean", "src/Effect4/Laws/Program/Typed/Admission.lean", "src/Effect4/Laws/Program/Typed/Adequacy.lean"):
    report["source_sha256"][name] = hashlib.sha256((repo / name).read_bytes()).hexdigest()
report["probe_source_sha256"] = {name: hashlib.sha256((packet / name).read_bytes()).hexdigest()
    for name in ("Controls.lean", "Audit.lean")}
report["guard_count"] = (packet / "Controls.lean").read_text().count("#guard ")
report["all_recorded_passed"] = True
(packet / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
