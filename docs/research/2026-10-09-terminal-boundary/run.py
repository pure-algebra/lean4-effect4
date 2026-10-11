"""Reproduce the bounded fold reader and terminal-dispatch controls."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

packet = Path(__file__).resolve().parent
repo = packet.parents[2]
base = "bfe97080657ecb87d4551fc8a4511580369f698d"
primary = "21d8e031f31318db62afea392b3d043beef2e0be"
env = dict(os.environ, LEAN_NUM_THREADS="3")
receipt = {"format": "effect4-terminal-boundary-v1", "dependencySourcePin": base,
           "inspectedPrimary": primary, "sourceChecks": [], "commands": []}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def at(pin, path):
    return subprocess.check_output(["git", "show", pin + ":" + path], cwd=repo)

# Full files where unchanged. Flow's layout changes after ofProgram at primary.
for path in ["tools/Tools/View/Algebra.lean", "tools/Tools/View/Program.lean",
             "tools/Tools/View/Page.lean", "tools/Tools/View/FlowSpecimen.lean",
             "src/Effect4/Program/Fold.lean", "src/Effect4/Program/LayerView.lean",
             "tools/Tools/View/Flow.lean"]:
    data = [at(base, path), at(primary, path), (repo / path).read_bytes()]
    scope = "whole file"
    if path.endswith("/Flow.lean"):
        marker = b"\nmutual\n/-- A flow with each node's two lines replaced"
        assert all(x.count(marker) == 1 for x in data)
        data = [x.split(marker)[0] for x in data]
        scope = "prefix through ofProgram; excludes subsequent layout"
    assert data[0] == data[1] == data[2], ("source drift", path)
    receipt["sourceChecks"].append({"path": path, "scope": scope, "sha256": sha(data[0])})

def run(argv):
    result = subprocess.run(argv, cwd=repo, env=env, capture_output=True, text=True)
    receipt["commands"].append({"argv": argv, "exitCode": result.returncode,
                                "stdout": result.stdout, "stderr": result.stderr})
    (packet / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    return result.stdout

run(["lake", "build", "Tools.View.FlowSpecimen"])
run(["lake", "env", "lean", "--version"])
output = run(["lake", "env", "lean", "-DwarningAsError=true", str(packet / "FoldProbe.lean")])
(packet / "lean-output.txt").write_text(output)
axioms = dict(re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", output))
expected = {
    "Tools.View.Algebra.cata_prod": {"propext"},
    "Tools.View.Program.layer": {"propext", "Classical.choice", "Quot.sound"},
    "Tools.View.Flow.flowLayer": {"propext", "Classical.choice", "Quot.sound"},
    "Tools.View.Flow.waits": {"propext"},
    "TerminalBoundary.readings_eq": {"propext", "Classical.choice", "Quot.sound"},
}
assert set(axioms) == set(expected), axioms
for name, values in expected.items():
    assert set(axioms[name].split(", ")) == values, (name, axioms[name])
receipt["axioms"] = {name: sorted(values) for name, values in expected.items()}
receipt["finiteGuardCount"] = sum(line.startswith("#guard") for line in (packet / "FoldProbe.lean").read_text().splitlines())
receipt["specimenCount"] = int(output.strip().splitlines()[-1])
receipt["probeSha256"] = sha((packet / "FoldProbe.lean").read_bytes())
launcher = packet / "launcher"
assert sha((launcher / "launcher-original.sh").read_bytes()) == sha(at(primary, "tools/view/v"))
run(["python3", str(launcher / "probe.py")])
receipt["launcher"] = json.loads((launcher / "evidence.json").read_text())
receipt["limits"] = [
    "Research reader only; no production change, generated terminal adapter, or full sweep.",
    "Text-dependent concrete reader inherits Classical.choice from the existing readers; generic cata_prod uses propext only.",
    "The wait-target prepass remains separate. No performance measurement.",
    "No Ghostty library execution, real terminal capability test, pixel agreement, or cross-platform conformance.",
    "Finite layout comparison uses the dependency base, before organic strokes; selected program readings match inspected primary."
]
(packet / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps({"lawReader": "checked", "finiteGuards": receipt["finiteGuardCount"],
                  "specimens": receipt["specimenCount"], "launcherControls": len(receipt["launcher"]["rows"])}))
