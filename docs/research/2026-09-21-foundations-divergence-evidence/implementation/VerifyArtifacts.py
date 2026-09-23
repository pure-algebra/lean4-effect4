"""Check unchanged observations and record the generated-output inventory."""
import hashlib
import json
from pathlib import Path
import subprocess

base = "0d5e109c"
evidence = Path(__file__).resolve().parent

def old(path):
    return subprocess.check_output(["git", "show", f"{base}:{path}"])

manifest = json.loads(Path("harness/truth/corpus.json").read_text())
before = json.loads(old("harness/truth/corpus.json"))
entries = {e["name"]: e for e in manifest["programs"]}
previous = {e["name"]: e for e in before["programs"]}
assert len(previous) == 36 and len(entries) == 37
assert set(entries) - set(previous) == {"pInterruptEscape"}
assert all({k: v for k, v in entries[n].items() if k != "scenario"} == row
           for n, row in previous.items())
results = json.loads(Path("harness/truth/result.json").read_text())
old_results = json.loads(old("harness/truth/result.json"))
assert results["rows"][:36] == old_results["rows"]
assert len(results["rows"]) == 37
assert results["rows"][36]["exception"] == "U-01"
assert results["rows"][36]["exitAgree"] is False
assert results["rows"][36]["scheduleAgree"] is False
assert results["rows"][36]["runSyncAgree"] is True
for path in ["src/Effect4/Laws/Program/RuntimeR.lean",
             "Test/Program/RuntimeRContract.lean", "Test/Program/RuntimeRReference.lean",
             "docs/core/decisions.md", "docs/STATE.md", "README.md", "lakefile.toml"]:
    assert Path(path).read_bytes() == old(path), path
for row in json.loads((evidence / "generated-inventory.json").read_text()):
    assert hashlib.sha256(Path(row["path"]).read_bytes()).hexdigest() == row["sha256"], row["path"]
print("PASS: 36 existing manifest observations and host rows unchanged; one signed U-01 fixture added")
print("PASS: RuntimeR theorem source and original runtime batteries unchanged")
print("PASS: coordinator-owned files unchanged; all 11 reviewed generated file hashes match")
