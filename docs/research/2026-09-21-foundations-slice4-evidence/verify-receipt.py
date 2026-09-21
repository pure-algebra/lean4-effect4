"""Check this receipt against the retained checkpoints and the actual checkout."""
from pathlib import Path
import hashlib
import gzip
import json
import re
import subprocess

root = Path(__file__).resolve().parents[3]
evidence = Path(__file__).resolve().parent
base = "5d63f91d6baf46ef4a448e616200ec4325e2b234"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


for manifest in ("source-sha256.json", "vendor-sha256.json"):
    for path, expected in json.loads((evidence / manifest).read_text()).items():
        assert sha(root / path) == expected, (manifest, path)
for path, expected in json.loads((evidence / "statement-sha256.json").read_text()).items():
    archive = evidence / "statement-snapshot" / (path.removeprefix("src/") + ".gz")
    assert hashlib.sha256(gzip.decompress(archive.read_bytes())).hexdigest() == expected, path

# Compare the declaration text, not just theorem names or output counts.
groups = [
    ("Effects/ProtocolObligations.lean", "Effect4.Laws.Effects.D12",
     ["mono", "bind", "widen", "inl", "inl_inv", "inr_inv", "pure_inv", "plain_iff"]),
    ("Machine/RefKernel.lean", "RefKernelObligations", ["indexed_ref_step_preserves"]),
    ("Machine/Refinement.lean", "CompositionObligations",
     ["projects_compose", "projects_induces_refines"]),
]


def declaration(text, namespace, name):
    block = text.split("namespace " + namespace + "\n", 1)[1].split("end " + namespace, 1)[0]
    statement = block.split("theorem " + name + " ", 1)[1].split(":= ⟨⟩", 1)[0]
    assert "ProofGraph.Obligation" in statement
    return " ".join(statement.split())


unchanged = []
for path, namespace, names in groups:
    archive = evidence / "statement-snapshot/Effect4/Laws" / (path + ".gz")
    old = gzip.decompress(archive.read_bytes()).decode()
    new = (root / "src/Effect4/Laws" / path).read_text()
    for name in names:
        assert declaration(old, namespace, name) == declaration(new, namespace, name), name
        unchanged.append(namespace + "." + name)

audit = (evidence / "final-audit.log").read_text()
prior = (evidence.parent / "2026-09-21-foundations-slice3-evidence/final-audit.log").read_text()
open_names = sorted(re.findall(r"^OPEN (.+)$", audit, re.MULTILINE))
assert open_names == sorted(re.findall(r"^OPEN (.+)$", prior, re.MULTILINE))
assert "UNIQUE LEDGER: 336 total; 327 proved; 9 open" in audit
assert "256 paired, 80 without a namesake, 0 mismatches" in audit
assert "sorryAx" not in audit

allowed = {
    "src/Effect4/Laws.lean", "src/Effect4/Laws/Effects/Protocol.lean",
    "src/Effect4/Laws/Effects/ProtocolObligations.lean",
    "src/Effect4/Laws/Machine/RefKernel.lean", "src/Effect4/Laws/Machine/Refinement.lean",
    "Test/All.lean", "Test/Program/ProtocolCertificates.lean",
    "Test/Machine/Runtime/RepresentationFoundations.lean",
}
tracked = subprocess.check_output(["git", "diff", "--name-only", base], cwd=root, text=True).splitlines()
new = subprocess.check_output(["git", "ls-files", "--others", "--exclude-standard"], cwd=root, text=True).splitlines()
source_changes = sorted(p for p in set(tracked + new) if not p.startswith("docs/"))
assert set(source_changes) == allowed, source_changes
subprocess.run(["git", "diff", "--check", base], cwd=root, check=True)

rows = json.loads((evidence / "vendor-probe.json").read_text())["rows"]
assert len(rows) == 6 and all(row["pass"] for row in rows)
build = gzip.decompress((evidence / "make-build.log.gz").read_bytes()).decode()
assert "Build completed successfully (699 jobs)." in build
check = gzip.decompress((evidence / "make-check.log.gz").read_bytes()).decode()
assert "PASS library-roots: fresh module, root-closure and axiom audit" in check
assert "PASS check-gen: every Lean-only generated file is what its generator emits" in check

report = {
    "base": base,
    "source_and_snapshot_hashes_match": True,
    "unchanged_checkpoint_declarations": unchanged,
    "source_changes": source_changes,
    "held_runtime_and_generated_source_fence": "unchanged",
    "ledger": {"total": 336, "proved": 327, "open": 9},
    "open_names_unchanged": open_names,
    "vendor_controls_passed": 6,
    "required_build_and_check_logs": "pass",
}
(evidence / "source-check.json").write_text(json.dumps(report, indent=2) + "\n")
print("PASS receipt: source/snapshot hashes, eleven unchanged declarations, source fence, ledger, vendor controls and required checks")
