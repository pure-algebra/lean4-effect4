#!/usr/bin/env python3
"""Check emitted map callers and an import-only control without changing production."""
import argparse
import hashlib
import json
import shutil
import subprocess
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--evidence", type=Path, required=True)
parser.add_argument("--install", type=Path, required=True)
args = parser.parse_args()
base = args.evidence.resolve()
target = base / "target"
packages = args.install.resolve()
assert (target / "corpus" / "emptyMap.ts").is_file(), "Run Probe.lean first"
assert not (target / "prelude").exists(), "Use a fresh evidence directory"
version = json.loads((packages / "@typescript/native-preview/package.json").read_text())["version"]
assert version == "7.0.0-dev.20260629.1", version
prelude = target / "prelude"
prelude.mkdir()
files = ["prelude-atoms.gen.ts", "records.ts", "tuples.ts", "control.ts"]
for name in files:
    shutil.copyfile(Path("harness/truth") / name, prelude / name)
(prelude / "prelude.ts").write_text("".join('export * from "./' + name + '"\n' for name in files))
config = {"compilerOptions": {"target": "ES2022", "module": "ESNext", "moduleResolution": "Bundler",
    "strict": True, "noEmit": True, "allowImportingTsExtensions": True, "noUnusedLocals": True,
    "noUnusedParameters": True, "skipLibCheck": True}, "include": ["corpus/*.ts", "prelude/*.ts"]}
(target / "tsconfig.json").write_text(json.dumps(config, indent=2) + "\n")
repaired = base / "target-import-control"
shutil.copytree(target, repaired)
changed = []
for path in sorted((repaired / "corpus").glob("*.ts")):
    original = path.read_text()
    control = original.replace("type Readonly, type Record, ", "")
    if control != original:
        path.write_text(control)
        changed.append(path.name)
assert changed == ["emptyMap.ts", "populatedMap.ts"], changed
results = []
for name, root in [("original", target), ("import-control", repaired)]:
    (root / "node_modules").symlink_to(packages, target_is_directory=True)
    command = ["node", str(packages / "@typescript/native-preview/bin/tsgo"), "--noEmit", "-p", str(root / "tsconfig.json")]
    run = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (base / (name + ".tsgo.log")).write_text(run.stdout)
    results.append({"name": name, "command": command, "exitCode": run.returncode, "diagnostics": run.stdout})
    print(name, run.returncode, run.stdout)
    assert (run.returncode == 0) == (name == "import-control")
    if name == "original":
        assert run.stdout.count("error TS2305") == 4 and "Readonly" in run.stdout and "Record" in run.stdout
record = {"reviewedCommit": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
    "compiler": version, "effect": json.loads((packages / "effect/package.json").read_text())["version"],
    "changedControlFiles": changed, "results": results,
    "hashes": {str(path.relative_to(base)): hashlib.sha256(path.read_bytes()).hexdigest()
        for root in [target, repaired] for path in root.rglob("*.ts") if "node_modules" not in path.parts},
    "limit": "Five emitted callers. The copied positive control removes two type imports; production stays unchanged."}
(base / "target-results.json").write_text(json.dumps(record, indent=2) + "\n")
