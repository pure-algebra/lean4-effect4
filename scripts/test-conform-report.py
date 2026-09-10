#!/usr/bin/env python3
"""Regression controls for coverage, proof receipts, provenance and producer failure."""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent / "lib"))
from conform_report import InvalidReport, fresh_run, identity, validate


def fixture():
    ids = [{"check": "check", "subject": {"kind": "type", "path": [name]}} for name in ("A", "B")]
    return {"format": "conform-report-v2", "tool": "control", "pins": [{"name": "profile", "value": "fixed"}],
            "inputs": [{"name": "input", "sha256": "a" * 64}], "expected": 2, "required": ids,
            "summary": {"rows": 2, "pass": 2, "refused": 0, "counterexample": 0,
                        "unresolved": 0, "complete": True, "exit": 0},
            "rows": [{**i, "outcome": "pass", "evidence": "tested", "message": "ok", "detail": None} for i in ids]}


class ReportControls(unittest.TestCase):
    def test_positive(self):
        r = fixture()
        self.assertEqual(validate(r, 0, expected_ids=map(identity, r["required"])), 0)

    def test_duplicate_does_not_cover_missing(self):
        r = fixture()
        r["rows"][1] = copy.deepcopy(r["rows"][0])
        with self.assertRaisesRegex(InvalidReport, "duplicate"):
            validate(r)

    def test_extra_row(self):
        r = fixture()
        r["rows"][1]["subject"] = {"kind": "type", "path": ["C"]}
        with self.assertRaisesRegex(InvalidReport, "unexpected"):
            validate(r)

    def test_truncated_unresolved_cannot_pass(self):
        r = fixture()
        r["rows"] = r["rows"][:1]
        r["rows"][0]["outcome"] = "unresolved"
        with self.assertRaisesRegex(InvalidReport, "missing"):
            validate(r)

    def test_truncated_plan_cannot_change_requested_domain(self):
        r = fixture()
        domain = list(map(identity, r["required"]))
        r["required"] = r["required"][:1]
        r["expected"] = 1
        with self.assertRaisesRegex(InvalidReport, "domain changed"):
            validate(r, expected_ids=domain)

    def test_exit_and_summary_checked(self):
        with self.assertRaisesRegex(InvalidReport, "exit"):
            validate(fixture(), 2)
        r = fixture()
        r["summary"]["pass"] = 999
        with self.assertRaisesRegex(InvalidReport, "summary"):
            validate(r)

    def test_boolean_is_not_an_integer_summary(self):
        r = fixture()
        r["summary"]["exit"] = False
        with self.assertRaisesRegex(InvalidReport, "summary field types"):
            validate(r)

    def test_profiles_inputs_and_unknown_fields(self):
        for kw in ({"expected_pins": {"profile": "other"}}, {"expected_inputs": {"input": "b" * 64}}):
            with self.assertRaises(InvalidReport):
                validate(fixture(), **kw)
        r = fixture()
        r["ignored"] = True
        with self.assertRaisesRegex(InvalidReport, "unknown"):
            validate(r)

    def test_proof_name_without_statement_is_rejected(self):
        r = fixture()
        r["rows"][0].update(evidence="proved", detail={"theorem": "not.a.proof"})
        with self.assertRaisesRegex(InvalidReport, "proof binding"):
            validate(r)

    def test_open_obligations_are_not_a_certificate(self):
        r = fixture()
        r["obligations"] = [{"kind": "scalar.domain", "subject": {"kind": "type", "path": ["A"]},
                             "status": "unproved", "dependsOn": [], "profile": "fixed",
                             "statement": "value fits the target", "detail": None}]
        self.assertEqual(validate(r), 0)
        with self.assertRaisesRegex(InvalidReport, "open obligations"):
            validate(r, require_closed=True)

    def test_malformed_obligation_is_rejected(self):
        r = fixture()
        r["obligations"] = [{"kind": "scalar.domain"}]
        with self.assertRaisesRegex(InvalidReport, "missing keys"):
            validate(r)

    def test_unresolved_keeps_exit_two(self):
        r = fixture()
        r["rows"][0]["outcome"] = "unresolved"
        r["summary"].update({"pass": 1, "unresolved": 1, "exit": 2})
        self.assertEqual(validate(r, 2), 2)

    def test_structural_paths(self):
        self.assertNotEqual(identity({"check": "c", "subject": {"kind": "k", "path": ["a/b"]}}),
                            identity({"check": "c", "subject": {"kind": "k", "path": ["a", "b"]}}))

    def test_fresh_output_and_crashed_producer(self):
        with tempfile.TemporaryDirectory() as temp:
            p = Path(temp)
            source = p / "fixture.json"
            source.write_text(json.dumps(fixture()))
            latest = p / "latest.json"
            command = [sys.executable, "-c",
                       "from pathlib import Path; import shutil,sys; shutil.copy(sys.argv[1], Path(sys.argv[2])/'report.json')",
                       str(source), "{out}"]
            self.assertEqual(fresh_run(command, latest, ["report.json"], cwd=p), 0)
            original = latest.read_bytes()
            with self.assertRaisesRegex(InvalidReport, "output set"):
                fresh_run([sys.executable, "-c", "raise SystemExit(1)"], latest, ["report.json"], cwd=p)
            self.assertEqual(latest.read_bytes(), original)

    def test_mutation_during_run_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            p = Path(temp)
            src = p / "fixture.json"
            src.write_text(json.dumps(fixture()))
            reads = iter([{"source": "old"}, {"source": "new"}])
            command = [sys.executable, "-c",
                       "from pathlib import Path; import shutil,sys; shutil.copy(sys.argv[1], Path(sys.argv[2])/'report.json')",
                       str(src), "{out}"]
            with self.assertRaisesRegex(InvalidReport, "inputs changed"):
                fresh_run(command, p / "latest.json", ["report.json"], cwd=p, input_snapshot=lambda: next(reads))
            self.assertFalse((p / "latest.json").exists())


if __name__ == "__main__":
    unittest.main()
