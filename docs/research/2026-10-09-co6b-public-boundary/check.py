from pathlib import Path
import json, os, subprocess, sys

receipt = Path(__file__).resolve().parent
root = receipt.parents[2]
logs = receipt / "checks"
logs.mkdir(exist_ok=True)
link = receipt / "node_modules"
if not link.exists():
    link.symlink_to("../../../ts/eff/node_modules", target_is_directory=True)
commands = [
    ("public-controls", ["lake", "env", "bash", "-c",
        'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"',
        "review", str(root / ".lake/co6b-public-review"), "-DwarningAsError=true",
        "--run", str(receipt / "PublicBoundary.lean")], 0, "PASS: actual public emit/read/admit controls"),
    ("tsgo-version", [str(root / "ts/eff/node_modules/.bin/tsgo"), "--version"], 0, "7.0.0-dev.20260629.1")]
tsgo = [str(root / "ts/eff/node_modules/.bin/tsgo"), "--noEmit", "--strict",
    "--target", "es2022", "--module", "esnext", "--moduleResolution", "bundler",
    "--allowImportingTsExtensions", "--skipLibCheck"]
commands += [("tsgo-" + name, tsgo + [str(receipt / (name + ".ts"))], code, text)
    for name, code, text in [
        ("canonical", 0, ""), ("changed", 0, ""), ("distinct", 0, ""),
        ("collision", 1, "Cannot redeclare block-scoped variable 'SLayer'"),
        ("behavior", 0, "")]]
commands += [("bun-version", ["bun", "--version"], 0, ""),
    ("host-behavior", ["bun", "run", str(receipt / "behavior.ts")], 0,
        '{"before":1,"after":99,"rootBefore":1,"rootAfter":1}')]
results_path = logs / "results.json"
results = json.loads(results_path.read_text()) if sys.argv[1:] and results_path.exists() else []
for name, command, expected_code, expected_text in commands:
    if sys.argv[1:] and name not in sys.argv[1:]:
        continue
    print("CHECK " + name, flush=True)
    process = subprocess.run(command, cwd=root, env={**os.environ, "LEAN_NUM_THREADS": "3"},
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (logs / (name + ".log")).write_text(process.stdout)
    matched = process.returncode == expected_code and expected_text in process.stdout
    result = {"name": name, "command": command, "exit_code": process.returncode,
        "expected_exit": expected_code, "expected_text": expected_text, "matched": matched}
    results = [r for r in results if r["name"] != name] + [result]
    results_path.write_text(json.dumps(results, indent=2) + "\n")
    print("PASS" if matched else "UNEXPECTED", flush=True)
    if process.stdout:
        print(process.stdout, flush=True)
    if not matched:
        raise SystemExit(1)
