#!/usr/bin/env python3
"""Run retained model-plan evidence sequentially, never build or generate production files."""
import hashlib, json, os, pathlib, re, subprocess, sys
HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCES = [
 ("conservativity", "docs/research/2026-09-30-model-probe/pedigree/Conservativity.lean", 0),
 ("verify-conservativity", "docs/research/2026-09-30-model-probe/pedigree/VerifyConservativity.lean", 0),
 ("r2", "docs/research/2026-09-30-model-probe/TREE/R2Probe.lean", 0),
 ("verify-tree", "docs/research/2026-09-30-model-probe/TREE/verify-Probe.lean", 1),
 ("r2-all-axioms", "docs/research/2026-09-30-model-probe/TREE/verify-R2Probe-allaxioms.lean", 0),
 ("missing-service", "docs/research/2026-09-30-seat-codex-slice6-evidence/H2/diagnostics/MissingServiceTransport.lean", 0),
 ("h2-baseline", "docs/research/2026-09-30-seat-codex-slice6-evidence/H2/Baseline.lean", 0),
 ("h2-part-one", "docs/research/2026-09-30-seat-codex-slice6-evidence/H2/PartOne.lean", 1),
 ("verify-tree-current", "docs/research/2026-09-30-codex-review-model-probe/probes/VerifyTreeCurrent.lean", 0),
 ("morphism-collapse", "docs/research/2026-09-30-codex-review-model-probe/probes/MorphismCollapse.lean", 0),
 ("package-append", "docs/research/2026-09-30-codex-review-model-probe/probes/PackageAppend.lean", 0),
 ("deadlock-mutation", "docs/research/2026-09-30-codex-review-model-probe/probes/DeadlockMutation.lean", 0),
 ("saved-frame", "docs/research/2026-09-30-codex-review-model-probe/probes/SavedFrameTransport.lean", 0),
 ("refinement-iff", "docs/research/2026-09-30-codex-review-model-probe/probes/RefinementNotIff.lean", 0),
 ("closed-before-cleanup", "docs/research/2026-09-30-codex-review-model-probe/probes/ClosedBeforeCleanup.lean", 0),
]
results_file = HERE/"logs"/"results.json"
results = json.loads(results_file.read_text()) if results_file.exists() else []
failed = []
for name, source, expected in SOURCES:
    if len(sys.argv) > 1 and name not in sys.argv[1:]:
        continue
    cmd = ["lake", "env", "lean", "-DwarningAsError=true", source]
    run = subprocess.run(cmd, cwd=ROOT, env=dict(os.environ, LEAN_NUM_THREADS="1"), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (HERE/"logs"/(name+".log")).write_bytes(run.stdout)
    result = dict(name=name, command=cmd, cwd=str(ROOT), exit=run.returncode, expected=expected, sha256=hashlib.sha256((ROOT/source).read_bytes()).hexdigest())
    results = [r for r in results if r["name"] != name] + [result]
    (HERE/"logs"/"results.json").write_text(json.dumps(results, indent=2)+"\n")
    print(name, "exit", run.returncode, "expected", expected, flush=True)

    if run.returncode != expected:
        failed.append(name + ": unexpected exit")
    if expected == 0 and (b"sorryAx" in run.stdout or b"Classical.choice" in run.stdout):
        failed.append(name + ": forbidden proof dependency")
    if name == "verify-tree" and not all(x in run.stdout for x in [b"Unknown identifier `HandlesFit`", b"Unknown identifier `StrongExit`"]):
        failed.append(name + ": expected retired-name failure missing")
    if name == "h2-part-one":
        mapper = subprocess.run(["python3", "docs/research/2026-09-30-seat-codex-slice6-evidence/H2/map_errors.py", "PartOne", str(HERE/"logs"/"h2-part-one.log")], cwd=ROOT, stdout=subprocess.PIPE, check=True)
        (HERE/"logs"/"h2-error-map.json").write_bytes(mapper.stdout)
        mapped = json.loads(mapper.stdout)
        if mapped["distinct_primary_error_theorem_region_count"] != 8 or mapped["non_theorem_primary_errors"]:
            failed.append(name + ": diagnostic region set changed")
if failed:
    raise SystemExit("\n".join(failed))
