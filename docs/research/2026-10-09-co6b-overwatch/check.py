from pathlib import Path
import json, os, subprocess, sys
r = Path(__file__).resolve().parent
root = r.parents[2]
logs = r / "checks"
logs.mkdir(exist_ok=True)
link = r / "node_modules"
if not link.exists(): link.symlink_to("../../../ts/eff/node_modules", target_is_directory=True)
commands = [
 ("lean-controls", ["lake", "env", "bash", "-c", 'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec lean "$@"', "review", ".lake/host-coalgebra-review-overlay", "-DwarningAsError=true", "--run", str(r / "ExtractedServices.lean")], 0, "PASS:"),
 ("tsgo-version", [str(root / "ts/eff/node_modules/.bin/tsgo"), "--version"], 0, "7.0.0-dev.20260629.1")]
tsgo = [str(root / "ts/eff/node_modules/.bin/tsgo"), "--noEmit", "--strict", "--target", "es2022", "--module", "esnext", "--moduleResolution", "bundler", "--allowImportingTsExtensions", "--skipLibCheck"]
commands += [("tsgo-" + n, tsgo + [str(r / f)], code, expected) for n, f, code, expected in [
 ("positive", "positive.ts", 0, ""),
 ("collision", "collision.ts", 1, "Cannot redeclare block-scoped variable 'SLayer'"),
 ("method-name", "method-name.ts", 1, "error TS1005"),
 ("changed-request", "changed-request.ts", 0, ""),
 ("method-name-repaired", "method-name-repaired.ts", 0, ""),
 ("prototype-name-repaired", "prototype-name-repaired.ts", 0, ""),
 ("behavior", "behavior.ts", 0, "")]]
commands += [("bun-version", ["bun", "--version"], 0, ""),
             ("host-behavior", ["bun", "run", str(r / "behavior.ts")], 0, '{"original":1,"changedArgument":99}')]
results = json.loads((logs / "results.json").read_text()) if len(sys.argv) > 1 else []
for name, command, wanted, expected in commands:
    if len(sys.argv) > 1 and name not in sys.argv[1:]: continue
    results = [row for row in results if row["name"] != name]
    run = subprocess.run(command, cwd=root, env={**os.environ, "LEAN_NUM_THREADS":"3"}, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / (name + ".log")).write_text(run.stdout)
    ok = run.returncode == wanted and expected in run.stdout
    results.append({"name":name, "command":command, "exit_code":run.returncode, "expected_exit":wanted, "expected_text":expected, "matched":ok})
    (logs / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(name + ": " + ("PASS" if ok else "UNEXPECTED"), flush=True)
    if run.stdout: print(run.stdout, flush=True)
    if not ok: raise SystemExit(1)
