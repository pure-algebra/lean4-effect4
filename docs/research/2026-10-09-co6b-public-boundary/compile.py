from pathlib import Path
import hashlib, json, os, subprocess, sys, time

receipt = Path(__file__).resolve().parent
root = receipt.parents[2]
overlay = root / ".lake/co6b-public-review"
source_root = receipt / "snapshot/src"
logs = receipt / "checks"
logs.mkdir(exist_ok=True)
modules = ["Effect4.Codegen.Print", "Effect4.Codegen.Read", "Effect4.Codegen.Checked", "Effect4.Codegen.Admit", "Effect4.Api"]
results_path = logs / "build-results.json"
results = json.loads(results_path.read_text()) if results_path.exists() else []
for module in modules:
    if sys.argv[1:] and module not in sys.argv[1:]:
        continue
    relative = Path(*module.split("."))
    source = (source_root / relative).with_suffix(".lean")
    output = (overlay / relative).with_suffix(".olean")
    for suffix in [".olean", ".ilean", ".olean.private", ".olean.server", ".ir", ".ir.sig"]:
        output.with_suffix(suffix).unlink(missing_ok=True)
    command = ["lake", "env", "bash", "-c",
        'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"',
        "review", str(overlay), "-DwarningAsError=true", "--root=" + str(source_root),
        "-o", str(output), str(source)]
    print("CHECK " + module, flush=True)
    started = time.monotonic()
    process = subprocess.run(command, cwd=root, env={**os.environ, "LEAN_NUM_THREADS": "3"},
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (logs / (module + ".log")).write_text(process.stdout)
    result = {"module": module, "command": command, "exit_code": process.returncode,
        "seconds": time.monotonic() - started,
        "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
    if output.exists():
        result["olean_sha256"] = hashlib.sha256(output.read_bytes()).hexdigest()
    results = [r for r in results if r["module"] != module] + [result]
    results_path.write_text(json.dumps(results, indent=2) + "\n")
    print("RESULT " + str(process.returncode), flush=True)
    if process.stdout:
        print(process.stdout, flush=True)
    if process.returncode:
        raise SystemExit(process.returncode)
