#!/usr/bin/env python3
"""Check retained research evidence and record packet hashes.

This checks the packet, not the production implementation or a proof theorem.
Run each probe's documented command to produce fresh behavioral evidence.
"""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
from urllib.parse import unquote

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return (HERE / path).read_text()


def data(path):
    return json.loads(read(path))


def command(argv):
    result = subprocess.run(argv, cwd=ROOT, text=True, capture_output=True)
    return {"argv": argv, "exit": result.returncode,
            "stdout": result.stdout, "stderr": result.stderr}


def passes(text):
    return re.findall(r"^PASS (.+)$", text, re.M)


conversion_log = read("conversions/run.log")
assert "MEASURE passed=88" in conversion_log
assert "MEASURE quickcheck_roundtrips=256" in conversion_log
assert "PASS abstract_clock_constructor_hidden" in conversion_log
samples = re.findall(r"^PASS generated_ty_(\d+)_sexp_roundtrip$", conversion_log, re.M)
wire_samples = re.findall(r"^PASS generated_ty_(\d+)_wire_roundtrip$", conversion_log, re.M)
assert samples == wire_samples and len(set(samples)) == 29

jane_log = read("conversions/ecosystem/run.log")
assert "MEASURE ecosystem_passed=24" in jane_log
assert "PASS comparator_witness_prevents_mixing_orders" in jane_log
assert "Desc.comparator_witness is not compatible with type" in jane_log
assert "PASS ecosystem_driver_finished" in jane_log
jane = data("conversions/ecosystem/provenance.json")
carrier_copy = HERE / "conversions/ecosystem/input-eff-types.ml"
assert sha(carrier_copy) == jane["carrier_source"]["sha256"]
assert sha(HERE / "conversions/ecosystem/expanded.ml") == jane["artifacts"]["expanded.ml"]
assert sha(HERE / "conversions/ecosystem/ecosystem_probe.ml") == jane["artifacts"]["ecosystem_probe.ml"]
for path, expected in jane["installed_files"].items():
    assert sha(Path(path)) == expected, path

model = data("model-provenance.json")
assert model["run"]["exit"] == 0 and model["inputs_unchanged_during_run"]
assert len(passes(read("model-probe.log"))) == 12
assert "MEASURE finite_model_checks=12" in read("model-probe.log")

eio_log = read("eio/root-rerun.log")
assert "ALL FINITE PROBES PASSED" in eio_log
assert "PASS compiler refuses a resource without the Lookup interface" in eio_log
assert len(passes(eio_log)) == 22
interop_log = read("eio/interop-root-rerun.log")
assert "ALL INTEROPERABILITY PROBES PASSED" in interop_log
assert len(passes(interop_log)) == 5
native_flow_log = read("eio/native-contract/root-rerun.log")
assert "ALL NATIVE FLOW INTERFACE PROBES PASSED" in native_flow_log
assert len(passes(native_flow_log)) == 14
native_type_log = read("eio/native-contract/root-type-controls.log")
assert "PASS native source dictionary rejects a missing method" in native_type_log
assert "PASS native Flow consumer rejects a sink in the source position" in native_type_log
assert len(passes(native_type_log)) == 2
for path, expected in data("eio/native-contract/sources.json")["source_sha256"].items():
    assert sha(Path(path)) == expected, path

lowering = data("lowering/ocaml-controls.json")
assert len(lowering) == 13
assert [row["exit"] for row in lowering] == [0, 0, 0, 0, 2, 2, 2, 0, 2, 2, 2, 2, 0]
assert "scalar-boundary: finite controls pass" in lowering[1]["output"]
assert "compiler accepts negative naturals and mixed name domains" in lowering[3]["output"]
checker_log = read("lowering/checker-lean.log")
assert "error:" not in checker_log
assert "unbound: checker diagnostics = [unbound-value@probe: `missing_value`]" in checker_log
for label in ("positive", "wrong_type", "raw_scope", "unknown_field", "hole_fill"):
    assert f"{label}: checker diagnostics = []" in checker_log

relative_links = []
for document in sorted(HERE.rglob("*.md")):
    text = document.read_text()
    for raw in re.findall(r"\[[^\]\n]+\]\(([^)\n]+)\)", text):
        target = raw.strip("<>").split("#", 1)[0]
        if not target or "://" in target or target.startswith("mailto:"):
            continue
        path = Path(unquote(target))
        path = path if path.is_absolute() else document.parent / path
        assert path.exists(), f"Unresolved link in {document}: {raw}"
        relative_links.append({"document": str(document.relative_to(HERE)), "target": raw})

# Older slices retain their own source snapshots. Report later concurrent edits explicitly.
source_changes = []
groups = [
    ("conversions", data("conversions/provenance.json")["inputs"]),
    ("lowering", data("lowering/pins.json")["files"]),
    ("model", model["input_sha256_after"]),
]
for label, pins in groups:
    for relative, expected in pins.items():
        path = ROOT / relative
        actual = sha(path) if path.exists() else None
        if actual != expected:
            source_changes.append({"slice": label, "path": relative,
                                   "recorded_sha256": expected, "current_sha256": actual})

files = sorted(path for path in HERE.rglob("*") if path.is_file()
               and "__pycache__" not in path.parts
               and path.name not in {"verification.json", "verification.log"})
record = {
    "verified_utc": datetime.now(timezone.utc).isoformat(),
    "scope": "Retained finite probe outputs, selected input identities, links and packet hashes",
    "head": command(["git", "rev-parse", "HEAD"]),
    "working_tree": command(["git", "status", "--short"]),
    "measurements": {
        "conversion_runtime_checks": 88,
        "generated_ty_constructor_samples": len(samples),
        "ordinary_record_quickcheck_samples": 256,
        "jane_street_runtime_checks": 24,
        "jane_street_compile_rejection": 1,
        "eio_checks_including_compile_rejection": len(passes(eio_log)),
        "scheduler_interoperability_checks": len(passes(interop_log)),
        "native_eio_interface_execution_checks": len(passes(native_flow_log)),
        "native_eio_interface_type_refusals": len(passes(native_type_log)),
        "lean_model_checks": len(passes(read("model-probe.log"))),
        "lowering_commands_with_expected_outcomes": len(lowering),
        "resolved_document_links": len(relative_links),
    },
    "source_changes_since_individual_probes": source_changes,
    "packet_sha256": {str(path.relative_to(HERE)): sha(path) for path in files},
}
(HERE / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
print("PASS retained probe outcomes, selected source hashes, and document links")
print(json.dumps(record["measurements"], indent=2))
print(f"MEASURE changed_source_pins_since_individual_probes={len(source_changes)}")
for change in source_changes:
    print(f"CHANGED {change['slice']} {change['path']}")
