#!/usr/bin/env python3
"""Narrow verification of the L4 review packet; never edits production source."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, os, re, subprocess

packet = Path(__file__).resolve().parent
root = packet.parents[2]
env = dict(os.environ, LEAN_NUM_THREADS="3")
source_paths = [
    "src/Effect4/Laws/Program/DenoteRowsB.lean",
    "src/Effect4/Laws/Program/Agreement/Segment.lean",
    "src/Effect4/Laws/Program/Agreement/Hosted.lean",
    "src/Effect4/Laws/Program/Agreement/LoopCalls.lean",
    "src/Effect4/Laws/Program/Agreement/HostedLoop.lean",
    "src/Effect4/Laws/Api/SessionMeaningLoop.lean",
    "src/Effect4/Program/Edit.lean",
    "src/Effect4/Program/Admit.lean",
    "src/Effect4/Api/HostSession.lean",
    "tools/Tools/View/Run.lean",
    "tools/Tools/View/Flow.lean",
    "tools/Tools/Query.lean",
    "tools/Tools/Session.lean",
    "src/Effect4/Program/Refs.lean",
    "src/Effect4/Program/Compile.lean",
    "src/Effect4/Laws/Program/Typed/Scope.lean",
    "src/Effect4/Laws/Program/Typed/LayerArm.lean",
    "src/Effect4/Laws/Program/Typed/Admission.lean",
    "src/Effect4/Laws/Program/Typed/Assembly.lean",
    "src/Effect4/Codegen/Print.lean",
    "vendor/effect-4.0.0-rc.112/src/Layer.ts",
]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
record = {
    "reviewed_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
    "branch": subprocess.check_output(["git", "branch", "--show-current"], cwd=root, text=True).strip(),
    "sources_sha256": {s: sha(root / s) for s in source_paths},
    "guard_counts": {name: len(re.findall(r"^#guard ", (packet / name).read_text(), re.M)) for name in ["Controls.lean", "LayerContextControls.lean", "CXControls.lean", "CX3Controls.lean"]},
    "probe_sha256": {name: sha(packet / name) for name in ["Controls.lean", "LayerContextControls.lean", "CXControls.lean", "CX3Controls.lean"]},
    "checks": {},
}
steps = [
    ("build", ["lake", "build", "Effect4.Laws.Api.SessionMeaningLoop", "Test.Dogfood.Scenario", "ProofGraph.AxiomAudit", "ProofGraph.Plan", "Effect4.Laws.Program.Typed.Commands.Clauses.All"], root),
    ("controls", ["lake", "env", "lean", "-DwarningAsError=true", "-o", str(packet / "Controls.olean"), str(packet / "Controls.lean")], root),
    ("layer-context-controls", ["lake", "env", "lean", "-DwarningAsError=true", "-o", str(packet / "LayerContextControls.olean"), str(packet / "LayerContextControls.lean")], root),
    ("cx-controls", ["lake", "env", "lean", "-DwarningAsError=true", "-o", str(packet / "CXControls.olean"), str(packet / "CXControls.lean")], root),
    ("cx3-controls", ["lake", "env", "lean", "-DwarningAsError=true", "-o", str(packet / "CX3Controls.olean"), str(packet / "CX3Controls.lean")], root),
    ("cx-audit", ["lake", "env", "lean", "-DwarningAsError=true", str(packet / "CXAudit.lean")], root),
    ("audit", ["lake", "env", "lean", "-DwarningAsError=true", str(packet / "Audit.lean")], root),
]
for name, command, cwd in steps:
    log = packet / (name + ".log")
    started = datetime.now(timezone.utc).isoformat()
    local_env = dict(env)
    if name != "build":
        prior = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"], cwd=root, env=env, text=True).strip()
        local_env["LEAN_PATH"] = str(packet) + os.pathsep + prior
    with log.open("w") as out:
        result = subprocess.run(command, cwd=cwd, env=local_env, stdout=out, stderr=subprocess.STDOUT)
    record["checks"][name] = {"command": command, "started_utc": started, "exit": result.returncode, "log_sha256": sha(log)}
    (packet / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(name, result.returncode, flush=True)
    if result.returncode:
        print(log.read_text()[-6000:])
        raise SystemExit(result.returncode)
print((packet / "audit.log").read_text(), end="")
print((packet / "cx-audit.log").read_text(), end="")
