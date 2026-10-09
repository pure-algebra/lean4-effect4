"""Check only the fragment outputs, using the existing manifest driver's commands."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import tempfile

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
env = {**os.environ, "LEAN_NUM_THREADS": "3"}
plan = json.loads(subprocess.check_output(
    ["lake", "env", "lean", "--run", "tools/Effect4Gen/Driver.lean", "--plan"],
    cwd=root, env=env, text=True))
selected = [row for row in plan["commands"] if row["name"] in {"Fragments", "FragmentLooped", "FragmentRows"}]
assert len(selected) == 3, "the three fragment manifest groups must exist"
results = []
with tempfile.TemporaryDirectory(prefix="effect4-fragment-drift-") as temporary:
    for row in selected:
        canonical = row["out"].replace("\\", "/")
        args = list(row["args"])
        output = Path(temporary) / (row["name"] + ".lean")
        args[args.index("--out") + 1] = str(output)
        command = ["lake", *args, "--header-out", canonical]
        subprocess.run(command, cwd=root, env=env, check=True)
        expected = (root / canonical).read_bytes()
        actual = output.read_bytes()
        assert actual == expected, f"generated drift: {canonical}"
        results.append({"group": row["name"], "path": canonical,
                        "sha256": hashlib.sha256(actual).hexdigest(), "byte_identical": True})
(evidence / "codegen-check.json").write_text(json.dumps(results, indent=2) + "\n")
print(f"PASS fragment codegen: {len(results)} outputs match their manifest producers")
