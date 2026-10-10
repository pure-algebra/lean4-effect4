#!/usr/bin/env python3
"""Reproduce this isolated L4a review without a full build or external runtime run."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib, json, os, re, subprocess

packet = Path(__file__).resolve().parent
repo = packet.parents[2]
reviewed = "4a83527ac91e6df820d3a13d422cec9c3a6a0b1d"
env = dict(os.environ, LEAN_NUM_THREADS="3", LEAN_PATH=str(packet))
modules = (packet / "build-command.txt").read_text().strip().split()[3:]
report = {"reviewed_commit": reviewed,
    "previous_reviewed_commit": "9e818b39596971d62b89299ca9ccc4e96ad8ea07",
    "environment": {"LEAN_NUM_THREADS": "3", "LEAN_PATH": str(packet)}, "checks": {}}

def checked(name, args):
    started = datetime.now(timezone.utc).isoformat()
    run = subprocess.run(args, cwd=repo, env=env, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = run.stdout + "\nExit: " + str(run.returncode) + "\n"
    (packet / (name + ".log")).write_text(log)
    report["checks"][name] = {"command": args, "started_utc": started,
        "exit": run.returncode, "log_sha256": hashlib.sha256(log.encode()).hexdigest()}
    (packet / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(name + ": " + str(run.returncode), flush=True)
    if run.returncode:
        print(run.stdout, flush=True)
        raise SystemExit(run.returncode)

checked("source-diff", ["git", "diff", "--exit-code", reviewed, "--",
    "src", "Test", "tools", "lakefile.toml", "lake-manifest.json"])
checked("build", ["lake", "build", *modules])
checked("controls", ["lake", "env", "lean", "-DwarningAsError=true",
    "-o", str(packet / "Controls.olean"), str(packet / "Controls.lean")])
checked("audit", ["lake", "env", "lean", "-DwarningAsError=true", str(packet / "Audit.lean")])
report["recorded_utc"] = datetime.now(timezone.utc).isoformat()
controls = (packet / "Controls.lean").read_text()
report["finite_guards"] = len(re.findall(r"^#guard ", controls, re.M))
report["kernel_readers_and_controls"] = len(re.findall(r"^example ", controls, re.M))
report["audit_summary"] = next(line for line in (packet / "audit.log").read_text().splitlines()
                               if line.startswith("#axiom_audit:"))
changed = ["Effect4.Laws.Program.Agreement.Segment",
           "Effect4.Laws.Program.Agreement.Hosted",
           "Effect4.Laws.Program.Agreement.HostedLoop"]
report["source_sha256"] = {"src/" + module.replace(".", "/") + ".lean":
    hashlib.sha256((repo / ("src/" + module.replace(".", "/") + ".lean")).read_bytes()).hexdigest()
    for module in changed}
report["all_recorded_passed"] = True
report["probe_sha256"] = {name: hashlib.sha256((packet / name).read_bytes()).hexdigest()
                         for name in ["Controls.lean", "Audit.lean"]}
(packet / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
