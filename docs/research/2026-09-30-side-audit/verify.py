from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = Path("/Users/pooks/Dev/lean4-effect4")
LEAN = Path("/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean")
SNAPSHOT = Path("/private/tmp/effect4-side-audit/cache")
manifest = json.loads((HERE / "manifest.json").read_text())
for filename, expected in manifest["sourceSha256"].items():
    actual = hashlib.sha256((REPO / filename).read_bytes()).hexdigest()
    if actual != expected:
        sys.exit(f"Reviewed source changed: {filename}")
if SNAPSHOT.exists():
    libraries = sorted(SNAPSHOT.iterdir())
    provenance = "isolated compiled-library snapshot"
else:
    libraries = [REPO / ".lake/build/lib/lean"]
    libraries += sorted((REPO / ".lake/packages").glob("*/.lake/build/lib/lean"))
    provenance = "current compiled libraries; reviewed source hashes checked"
env = dict(os.environ, LEAN_PATH=":".join(map(str, libraries)))
results = []
for source in sorted((HERE / "probes").glob("*.lean")):
    command = [str(LEAN), "-M6144", "-DwarningAsError=true", str(source)]
    result = subprocess.run(command, cwd=HERE, env=env, text=True, capture_output=True)
    output = result.stdout + result.stderr
    (HERE / "logs" / (source.stem + ".log")).write_text(output)
    results.append({"file": source.name, "command": command, "exit": result.returncode})
    print(f"{source.name}: exit {result.returncode}", flush=True)
    if result.returncode or "sorryAx" in output or "Classical.choice" in output:
        print(output)
        sys.exit(1)
command = ["bun", str(HERE / "probes/refusal-probe.ts")]
result = subprocess.run(command, cwd=HERE, text=True, capture_output=True)
output = result.stdout + result.stderr
(HERE / "logs/numeric-host.log").write_text(output)
assert result.returncode == 0, output
assert '"_tag":"Die"' in output, output
assert 'exact printer Ref expression {"_id":"Exit","_tag":"Success","value":true}' in output, output
assert 'exact printer catchCause expression with T1 add {"_id":"Exit","_tag":"Success","value":7}' in output, output
results.append({"file": "refusal-probe.ts", "command": command, "exit": result.returncode})
(HERE / "verification.json").write_text(json.dumps({"libraries": provenance, "results": results}, indent=2) + "\n")
print("numeric-host: exit 0; expected counterexamples observed", flush=True)
