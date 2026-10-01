from pathlib import Path
import subprocess, sys, json
root = Path(__file__).resolve().parent
green = (root / "census-green.log").read_text()
assert "  fold\t" in green
cases = {
    "valid-green": (green, 0),
    "deliberate-violation": (green.replace("  fold\t", "  structural\t", 1), 1),
    "empty": ("", 1),
    "compiler-error-only": ("error: unknown module prefix Effect4\n", 1),
    "missing-exhaustive-section": (green.split("#exhaustive_gate", 1)[0], 1),
}
results = []
for name, (data, expected) in cases.items():
    path = root / (name + ".log")
    path.write_text(data)
    cmd = [sys.executable, str(root / "check-commit4-rule.py"), str(path)]
    p = subprocess.run(cmd, capture_output=True, text=True, timeout=5)
    (root / (name + ".stdout")).write_text(p.stdout)
    (root / (name + ".stderr")).write_text(p.stderr)
    results.append({"case": name, "command": cmd, "expected_exit": expected,
                    "actual_exit": p.returncode, "stdout": p.stdout, "stderr": p.stderr})
(root / "results.json").write_text(json.dumps(results, indent=2) + "\n")
for r in results:
    print(r["case"], "expected", r["expected_exit"], "actual", r["actual_exit"], repr(r["stdout"]))
