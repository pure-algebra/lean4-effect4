#!/usr/bin/env python3
"""Replay the bounded run-view checks from this worktree."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import xml.etree.ElementTree as ET

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ENV = dict(os.environ, LEAN_NUM_THREADS="3")
commands = [
    ("narrow-build.log", ["lake", "build", "Tools.View.Run", "Tools.View.Build"], 0),
    ("audit-build.log", ["lake", "build", "ProofGraph.AxiomAudit"], 0),
    ("driver-imports-build.log", ["lake", "build", "Tools.View.Specimen", "Tools.View.FlowSpecimen", "Tools.View.Tokens", "Tools.View.Output"], 0),
    ("baseline-build.log", ["lake", "env", "sh", "-c", 'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" -DwarningAsError=true -o "$1/Baseline.olean" "$1/Baseline.lean"', "run-view", str(HERE)], 0),
    ("comparison.log", ["lake", "env", "sh", "-c", 'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" -DwarningAsError=true -o "$1/Compare.olean" "$1/Compare.lean"', "run-view", str(HERE)], 0),
    ("reuse.log", ["lake", "env", "lean", str(HERE / "Reuse.lean")], 0),
    ("audit-raw.log", ["lake", "env", "lean", str(HERE / "Audit.lean")], 1),
    ("audit-render.log", ["lake", "env", "lean", str(HERE / "AuditRender.lean")], 0),
    ("driver-build.log", ["lake", "env", "lean", "tools/Drivers/View.lean"], 0),
    ("benchmark.log", ["lake", "env", "sh", "-c", 'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" --run "$1/Bench.lean" 3', "run-view", str(HERE)], 0),
    ("benchmark-long.log", ["lake", "env", "sh", "-c", 'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" --run "$1/Bench.lean" 30', "run-view", str(HERE)], 0),
    ("host-render.log", ["lake", "env", "sh", "-c", 'LEAN_PATH="$1:$LEAN_PATH" lean --root="$1" --run "$1/HostRender.lean" "$1/render/host.svg"', "run-view", str(HERE)], 0),
    ("driver-run.log", ["lake", "env", "lean", "--run", "tools/Drivers/View.lean", "--motion", "1", "run", "pFork", str(HERE / "render")], 0),
]
results = []
for log, cmd, expected in commands:
    process = subprocess.run(cmd, cwd=ROOT, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (HERE / log).write_text(process.stdout)
    results.append({"command": cmd, "log": log, "exit": process.returncode, "expected_exit": expected})
    if process.returncode != expected:
        raise SystemExit(f"{log}: exit {process.returncode}, expected {expected}")
    if log == "audit-raw.log" and "9 of 54 declarations" not in process.stdout:
        raise SystemExit("the raw audit's exact rendering exclusions changed")
    print(f"PASS {log} (exit {process.returncode})", flush=True)
svgs = sorted((HERE / "render").glob("[0-9]*.svg"))
assert len(svgs) > 1
for svg in svgs:
    root = ET.parse(svg).getroot()
    assert root.tag == "{http://www.w3.org/2000/svg}svg"
    assert len(root.findall("{http://www.w3.org/2000/svg}text")) > 0
assert "fiber" in svgs[-1].read_text()
host = ET.parse(HERE / "render/host.svg").getroot()
host_text = "".join(host.itertext())
assert "Host.read(3)" in host_text and "number" in host_text
assert "1 calls outstanding" in host_text and "no module:" not in host_text
source = ROOT / "tools/Tools/View/Run.lean"
report = {"base": "9389e543", "head_before_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(), "threads": 3, "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(), "rendered_svg_frames": len(svgs), "commands": results}
(HERE / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
print(f"PASS {len(svgs)} emitted SVG frames parse and contain text")
