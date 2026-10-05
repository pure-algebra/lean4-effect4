#!/usr/bin/env python3
"""Finite controls of the conformance runner. They need neither Lean nor a compiler.

    python3 scripts/test-conform-runner.py

These are the isolated probes of the conformance review of 2026-10-05, kept as tests. The
review is `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/
conformance-api-review/`: `runner/probe.py`, `core/validator_probe.py` and
`core/fresh_run_probe.py`. Each test calls the runner's own code: `validate` and `fresh_run`
of `scripts/lib/conform_report.py`, and `step_compiler` of `scripts/check-conform.py`. A
producer is a small Python program in a temporary directory. The processes of the compiler
step are answers given here. No test writes into the repository.

Five of the review's observations recorded a fault of that day. Each is kept with the repaired
expectation, and its test says `repaired` in its name:

    a second report without its format tag was accepted as an artifact    now refused
    a refused run lost its files                                          now kept
    a mismatch of the compiled observations left no `actual.txt`          now written first
    a mutation that failed an unrelated observation was accepted          now refused
    a report could shorten its plan and its rows together                 now refused

The validator's own limits stay as the review measured them: a report is self-described, and
only a caller's request detects a plan that shrank. Those tests are in `Validator`.
"""
import contextlib
import copy
import hashlib
import importlib.util
import io
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/lib"))
from conform_report import InvalidReport, fresh_run, validate

_spec = importlib.util.spec_from_file_location("check_conform", ROOT / "scripts/check-conform.py")
checkpoint = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(checkpoint)


def identity(check, kind, name):
    return {"check": check, "subject": {"kind": kind, "path": [name]}}


def report(tool="fixture", ids=(("fixture.check", "fixture", "a"),), outcome="pass", pins=None,
           inputs=None):
    """A report that is consistent with its own plan."""
    required = [identity(*item) for item in ids]
    code = 2 if outcome == "unresolved" else 0 if outcome == "pass" else 1
    count = lambda kind: len(required) if outcome == kind else 0
    return {"format": "conform-report-v2", "tool": tool,
            "pins": [{"name": k, "value": v} for k, v in (pins or {}).items()],
            "inputs": [{"name": k, "sha256": v} for k, v in (inputs or {}).items()],
            "expected": len(required), "required": required,
            "rows": [{**item, "outcome": outcome, "evidence": "tested", "message": "ok",
                      "detail": None} for item in required],
            "summary": {"rows": len(required), "pass": count("pass"), "refused": count("refused"),
                        "counterexample": count("counterexample"),
                        "unresolved": count("unresolved"), "complete": True, "exit": code}}


class Validator(unittest.TestCase):
    """`validate` on one report: what it refuses alone, and what only a request detects."""

    def base(self):
        return report("scout", [("scout.example", "fixture", n) for n in "ab"],
                      pins={"profile": "p1"}, inputs={"source": "0" * 64})

    ids = [("scout.example", "fixture", (n,)) for n in "ab"]

    def accepted(self, value, **options):
        self.assertEqual(validate(value, 0, **options), 0)

    def refused(self, value, reason, **options):
        with self.assertRaisesRegex(InvalidReport, reason):
            validate(value, 0, **options)

    def test_valid_report_with_independent_expectations(self):
        self.accepted(self.base(), expected_tool="scout", expected_ids=self.ids,
                      expected_pins={"profile": "p1"}, expected_inputs={"source": "0" * 64})

    def test_missing_result_is_refused(self):
        value = self.base()
        value["rows"].pop()
        self.refused(value, "missing or unexpected results")

    def test_self_described_empty_domain_passes_alone(self):
        self.accepted(report(ids=()))

    def test_request_refuses_an_empty_domain(self):
        self.refused(report(ids=()), "requested input domain changed",
                     expected_ids=[("fixture.check", "fixture", ("a",))])

    def shrunk(self):
        value = self.base()
        value["rows"].pop()
        value["required"].pop()
        value["expected"] = value["summary"]["rows"] = value["summary"]["pass"] = 1
        return value

    def test_plan_and_results_shrink_together_and_pass_alone(self):
        self.accepted(self.shrunk())

    def test_request_detects_a_shrunk_plan(self):
        self.refused(self.shrunk(), "requested input domain changed", expected_ids=self.ids)

    def test_changed_pin_passes_alone_and_the_request_detects_it(self):
        value = self.base()
        value["pins"][0]["value"] = "p2"
        self.accepted(value)
        self.refused(value, "input profile or toolchain changed", expected_pins={"profile": "p1"})

    def test_changed_digest_passes_alone_and_the_request_detects_it(self):
        value = self.base()
        value["inputs"][0]["sha256"] = "1" * 64
        self.accepted(value)
        self.refused(value, "input manifest changed", expected_inputs={"source": "0" * 64})

    def test_another_tool_is_refused_by_the_request(self):
        self.refused(self.base(), "names the tool `scout`", expected_tool="other")

    def test_proof_metadata_is_a_shape_check_only(self):
        value = self.base()
        value["rows"][0]["evidence"] = "proved"
        value["rows"][0]["detail"] = {"theorem": "NoSuchTheorem", "proposition": "False", "axioms": []}
        # The schema accepts invented metadata: a checked producer has to stand behind it.
        self.accepted(value)
        value["rows"][0]["detail"]["axioms"] = ["sorryAx"]
        self.refused(value, "proof exceeds axiom policy")
        value["rows"][0]["detail"] = None
        self.refused(value, "missing checked proof binding")

    def test_obligations_are_open_work_data(self):
        obligation = {"kind": "made.up.kind", "subject": {"kind": "fixture", "path": ["a"]},
                      "status": "unproved", "dependsOn": ["no-such-obligation"], "profile": "p1",
                      "statement": "Open statement", "detail": None}
        value = self.base()
        value["obligations"] = [obligation]
        self.accepted(value)                                   # an unregistered kind passes the schema
        self.refused(value, "certificate has open obligations", require_closed=True)
        value["obligations"] = [obligation, copy.deepcopy(obligation)]
        self.accepted(value)                                   # so does a repeated obligation
        value.pop("obligations")
        self.accepted(value, require_closed=True)              # closed means none is listed

    def test_unknown_evidence_word_is_refused(self):
        value = self.base()
        value["rows"][0]["evidence"] = "verified"
        self.refused(value, "bad evidence method")


PRODUCER = '''import json, pathlib, sys
out = pathlib.Path(sys.argv[1])
payload = json.loads(pathlib.Path(sys.argv[2]).read_text())
for name, value in payload["files"].items():
    (out / name).write_text(value if isinstance(value, str) else json.dumps(value))
print("producer standard output")
print("producer standard error", file=sys.stderr)
sys.exit(payload["exit"])
'''


class FreshRun(unittest.TestCase):
    """`fresh_run`: the declared role of each output, and what a refused run leaves behind."""

    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.dir = Path(self.scratch.name)
        (self.dir / "producer.py").write_text(PRODUCER)
        self.destination = self.dir / "conform" / "profile.json"

    def tearDown(self):
        self.scratch.cleanup()

    def run_producer(self, files, reports, artifacts=(), exit=0, snapshot=None):
        payload = self.dir / "payload.json"
        payload.write_text(json.dumps({"files": files, "exit": exit}))
        self.command = [sys.executable, str(self.dir / "producer.py"), "{out}", str(payload)]
        return fresh_run(self.command, self.destination, reports, artifacts, cwd=self.dir,
                         input_snapshot=snapshot or (lambda: {"stable": "a" * 64}))

    def refused(self, reason, *args, **kwargs):
        with self.assertRaisesRegex(InvalidReport, reason) as caught:
            self.run_producer(*args, **kwargs)
        return str(caught.exception)

    def attempt(self):
        return json.loads((self.destination.parent / "attempts" / "profile" / "attempt.json").read_text())

    def kept_files(self):
        folder = self.destination.parent / "attempts" / "profile" / "files"
        return {p.name: p.read_text() for p in folder.iterdir()}

    def no_scratch_left(self):
        self.assertEqual(list(self.destination.parent.glob(".conform-*")), [])

    def test_two_declared_reports_pass(self):
        code = self.run_producer({"one.json": report(), "two.json": report()},
                                 {"one.json": "fixture", "two.json": "fixture"})
        self.assertEqual(code, 0)
        receipt = json.loads(self.destination.read_text())
        self.assertEqual(sorted(receipt["reports"]), ["one.json", "two.json"])
        self.assertEqual(receipt["roles"], {"one.json": "report:fixture", "two.json": "report:fixture"})
        self.assertFalse((self.destination.parent / "attempts").exists())
        self.no_scratch_left()

    def test_repaired_report_without_its_format_tag_is_refused(self):
        message = self.refused("two.json: declared a report, and its format is None",
                               {"one.json": report(), "two.json": {"note": "no longer a report"}},
                               {"one.json": "fixture", "two.json": "fixture"})
        self.assertIn("the attempt is kept", message)
        self.assertFalse(self.destination.exists())

    def test_repaired_report_with_an_artifact_tag_is_refused(self):
        self.refused("two.json: declared a report, and its format is 'raw-artifact-v1'",
                     {"one.json": report(), "two.json": {"format": "raw-artifact-v1", "rows": []}},
                     {"one.json": "fixture", "two.json": "fixture"})
        self.assertFalse(self.destination.exists())

    def test_the_same_file_declared_an_artifact_passes(self):
        code = self.run_producer({"one.json": report(), "two.json": {"format": "raw-artifact-v1", "rows": []}},
                                 {"one.json": "fixture"}, ["two.json"])
        self.assertEqual(code, 0)
        receipt = json.loads(self.destination.read_text())
        self.assertEqual(list(receipt["reports"]), ["one.json"])
        self.assertEqual(receipt["roles"]["two.json"], "artifact")
        self.assertIn("two.json", receipt["outputs"])

    def test_declared_artifact_that_carries_a_report_format_is_refused(self):
        self.refused("two.json: declared an artifact, and it carries a report's format",
                     {"one.json": report(), "two.json": report()}, {"one.json": "fixture"}, ["two.json"])

    def test_unsupported_report_format_is_refused(self):
        self.refused("two.json: declared a report, and its format is 'conform-report-v999'",
                     {"one.json": report(), "two.json": {**report(), "format": "conform-report-v999"}},
                     {"one.json": "fixture", "two.json": "fixture"})

    def test_report_of_another_tool_is_refused(self):
        self.refused("two.json: the report names the tool `other`, not `fixture`",
                     {"one.json": report(), "two.json": report(tool="other")},
                     {"one.json": "fixture", "two.json": "fixture"})

    def test_report_that_is_not_json_is_refused(self):
        self.refused("one.json: declared a report, and it is not JSON", {"one.json": "not json"},
                     {"one.json": "fixture"})

    def test_missing_output_is_refused(self):
        self.refused(r"producer output set differs: missing \['two.json'\], unexpected \[\]",
                     {"one.json": report()}, {"one.json": "fixture", "two.json": "fixture"})

    def test_unexpected_output_is_refused(self):
        self.refused(r"producer output set differs: missing \[\], unexpected \['extra.txt'\]",
                     {"one.json": report(), "extra.txt": "x"}, {"one.json": "fixture"})

    def test_profile_without_a_report_is_refused_before_it_runs(self):
        with self.assertRaisesRegex(InvalidReport, "declares no report"):
            fresh_run([sys.executable, "-c", "raise SystemExit(7)"], self.destination, {}, ["a.txt"],
                      cwd=self.dir)
        self.assertFalse((self.destination.parent / "attempts").exists())

    def test_output_named_in_two_roles_is_refused_before_it_runs(self):
        with self.assertRaisesRegex(InvalidReport, "names an output twice"):
            fresh_run([sys.executable, "-c", "pass"], self.destination, {"a.json": "fixture"},
                      ["a.json"], cwd=self.dir)

    def test_reported_failure_is_published_with_its_exit(self):
        code = self.run_producer({"one.json": report(outcome="refused")}, {"one.json": "fixture"}, exit=1)
        self.assertEqual(code, 1)
        self.assertEqual(json.loads(self.destination.read_text())["exit"], 1)

    def test_unresolved_rows_stay_exit_two(self):
        code = self.run_producer({"one.json": report(outcome="unresolved")}, {"one.json": "fixture"}, exit=2)
        self.assertEqual(code, 2)

    def test_exit_that_differs_from_its_reports_is_refused(self):
        self.refused("phase exit differs from its reports", {"one.json": report()},
                     {"one.json": "fixture"}, exit=1)

    def test_repaired_refused_run_keeps_its_evidence(self):
        message = self.refused("producer output set differs",
                               {"failure.json": {"detail": "useful incomplete result"}, "raw.ml": "let x = 1\n"},
                               {"one.json": "fixture"}, exit=2)
        self.assertIn(str(self.destination.parent / "attempts" / "profile"), message)
        record = self.attempt()
        self.assertEqual(record["format"], "conform-attempt-v1")
        self.assertIs(record["valid"], False)
        self.assertEqual(record["command"], self.command)
        self.assertEqual(record["exit"], 2)
        self.assertEqual(record["stdout"], "producer standard output\n")
        self.assertEqual(record["stderr"], "producer standard error\n")
        self.assertIn("producer output set differs", record["error"])
        self.assertEqual(record["roles"], {"one.json": "report:fixture"})
        self.assertEqual(record["inputs"], {"stable": "a" * 64})
        self.assertEqual(sorted(record["files"]), ["failure.json", "raw.ml"])
        self.assertEqual(record["files"]["raw.ml"], hashlib.sha256(b"let x = 1\n").hexdigest())
        self.assertEqual(self.kept_files()["raw.ml"], "let x = 1\n")
        self.assertIn("useful incomplete result", self.kept_files()["failure.json"])
        # Nothing of the attempt is published: no receipt, no artifact folder.
        self.assertFalse(self.destination.exists())
        self.assertFalse((self.destination.parent / "artifacts").exists())
        self.no_scratch_left()

    def test_refused_run_leaves_the_earlier_receipt_as_it_was(self):
        self.run_producer({"one.json": report()}, {"one.json": "fixture"})
        earlier = self.destination.read_bytes()
        self.refused("producer output set differs", {}, {"one.json": "fixture"}, exit=2)
        self.assertEqual(self.destination.read_bytes(), earlier)
        self.assertEqual(self.attempt()["exit"], 2)

    def test_the_attempt_folder_holds_the_latest_refused_run(self):
        self.refused("producer output set differs", {"first.txt": "1"}, {"one.json": "fixture"}, exit=2)
        self.refused("producer output set differs", {"second.txt": "2"}, {"one.json": "fixture"}, exit=3)
        self.assertEqual(sorted(self.kept_files()), ["second.txt"])
        self.assertEqual(self.attempt()["exit"], 3)

    def test_invalid_report_keeps_the_attempt_too(self):
        bad = report()
        bad["rows"] = []
        self.refused("one.json: missing or unexpected results", {"one.json": bad}, {"one.json": "fixture"})
        self.assertEqual(sorted(self.kept_files()), ["one.json"])

    def test_changed_input_is_refused_and_named(self):
        states = iter([{"a": "1" * 64, "b": "2" * 64}, {"a": "1" * 64, "b": "3" * 64}])
        self.refused(r"inputs changed during execution: \['b'\]", {"one.json": report()},
                     {"one.json": "fixture"}, snapshot=lambda: next(states))
        self.assertFalse(self.destination.exists())

    def test_producer_that_cannot_start_is_refused_and_recorded(self):
        with self.assertRaisesRegex(InvalidReport, "the attempt is kept"):
            fresh_run([str(self.dir / "no-such-producer"), "{out}"], self.destination,
                      {"one.json": "fixture"}, cwd=self.dir)
        self.assertIs(self.attempt()["valid"], False)
        self.assertNotIn("exit", self.attempt())


def compiled(exit=0, stdout="", stderr=""):
    return SimpleNamespace(returncode=exit, stdout=stdout, stderr=stderr)


class CompilerStep(unittest.TestCase):
    """`step_compiler` with every process answered here: the decisions of the Python step."""

    fixtures = [("key/never", ["source", "target", "host"]),
                ("key/handle-utf8", ["source", "target", "host"]),
                ("contains-order", ["host"]),
                ("names/mulCap", ["target", "host"])]
    controls = ["a source mutation", "support-body"]
    roots = ["Root.first", "Root.second"]
    profile = {"input-mode": "persisted-mono", "source-fuel": "20000", "target-fuel": "40000",
               "word-bits": "63"}

    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.out = Path(self.scratch.name) / "out"
        self.out.mkdir()
        self.environment = patch.dict(os.environ, {"OCAMLOPT": "/isolated/ocamlopt"})
        self.environment.start()
        self.host = [name for name, lanes in self.fixtures if "host" in lanes]
        prefix = lambda name: "".join(f"{n}\tPASS\n" for n in self.host[:self.host.index(name)])
        self.actual = compiled(stdout="".join(f"{n}\tPASS\n" for n in self.host))
        self.mutants = {"mutated": compiled(1, prefix("key/handle-utf8"), "key/handle-utf8\tFAIL\n"),
                        "mutated-support": compiled(1, prefix("names/mulCap"), "names/mulCap\tFAIL\n")}
        self.files = self.produced()
        self.calls = []

    def tearDown(self):
        self.environment.stop()
        self.scratch.cleanup()

    def produced(self, fixtures=None, source=None, pins=None):
        """The files of a producer that answers its selection."""
        fixtures = self.fixtures if fixtures is None else fixtures
        selection = {"format": "conform-selection-v1", "tool": "conform.normalization",
                     "pins": [{"name": k, "value": v} for k, v in self.profile.items()],
                     "phase": "mono", "roots": self.roots,
                     "fixtures": [{"name": n, "lanes": lanes} for n, lanes in fixtures],
                     "controls": self.controls}
        text = json.dumps(selection, indent=2) + "\n"
        bound = {"selection": hashlib.sha256(text.encode()).hexdigest()}
        lane = lambda l: [n for n, lanes in fixtures if l in lanes]
        ids = ([("normalization.source", "fixture", n) for n in (lane("source") if source is None else source)]
               + [("normalization.target", "fixture", n) for n in lane("target")]
               + [("normalization.control", "mutation", c) for c in self.controls])
        lean = checkpoint.lean_version()
        return {
            "selection.json": text,
            "normalization.json": json.dumps(report("conform.normalization", ids, inputs=bound,
                                                    pins={"lean": lean, **(pins or self.profile)})),
            "validity.json": json.dumps(report("conform-lcnf-validity",
                                               [("lcnf.decl.valid", "declaration", r) for r in self.roots + ["Reached.helper"]],
                                               pins={"lean": lean, "phase": "mono"}, inputs=bound)),
            "closure.json": json.dumps({"format": "conform-lcnf-manifest-v1", "roots": self.roots}),
            "normalization.ml": "let f s i = Char.code (String.get s i)\nlet m a b = if a = 0 then 0 else if b > max_int / a then max_int else a * b\n",
            "expected.txt": "".join(f"{n}\tPASS\n" for n in lane("host")),
        }

    def execute(self, command):
        """The processes of the step, answered: the Lean driver, the compiler and the runs."""
        self.calls.append(command)
        if command[:3] == ["lake", "env", "lean"]:
            for name, text in self.files.items():
                (self.out / name).write_text(text)
            return compiled()
        if command[-1] == "-version":
            return compiled(stdout="5.1.1\n")
        if "-o" in command:
            Path(command[-1]).write_text("a compiled program")
            return compiled()
        name = Path(command[0]).name
        return self.actual if name == "normalization" else self.mutants[name]

    def step(self):
        self.printed = io.StringIO()
        with contextlib.redirect_stdout(self.printed):
            return checkpoint.step_compiler(self.out, execute=self.execute)

    def refused(self, reason):
        with self.assertRaisesRegex((RuntimeError, ValueError), reason):
            self.step()

    def test_intended_failures_pass(self):
        self.assertEqual(self.step(), 0)
        self.assertEqual(self.printed.getvalue(),
                         "compiler checkpoint: 4 actual OCaml checks and 2 emitted-code mutations passed\n")
        made = json.loads((self.out / "ocaml.json").read_text())
        planned = [(item["check"], item["subject"]["path"][0]) for item in made["required"]]
        self.assertEqual(planned, [("normalization.ocaml", n) for n in self.host]
                         + [("normalization.ocaml.control", "utf8-mutation"),
                            ("normalization.ocaml.control", "support-mutation")])
        self.assertEqual([i["name"] for i in made["inputs"]], ["selection", "normalization.ml", "expected.txt"])
        self.assertEqual((self.out / "actual.txt").read_text(), self.actual.stdout)
        self.assertEqual((self.out / "mutation.txt").read_text(), "key/handle-utf8\tFAIL\nnames/mulCap\tFAIL\n")
        # The outputs are exactly the profile's: the compiled programs are removed.
        declared = checkpoint.PROFILES["compiler"]
        self.assertEqual({p.name for p in self.out.iterdir()}, set(declared["reports"]) | set(declared["artifacts"]))
        # Each process is kept with its command and its result, and no path of the run is in it.
        processes = json.loads((self.out / "processes.json").read_text())
        self.assertEqual(len(processes), len(self.calls))
        self.assertEqual(processes[1]["command"], ["/isolated/ocamlopt", "-w", "-a", "{out}/normalization.ml", "-o", "{out}/normalization"])
        self.assertEqual(processes[2], {"command": ["{out}/normalization"], "exit": 0, "stdout": self.actual.stdout, "stderr": ""})
        self.assertNotIn(str(self.out), (self.out / "processes.json").read_text())
        self.assertIn("a * a", (self.out / "mutated-support.ml").read_text())

    def test_repaired_unrelated_mutation_failure_is_refused(self):
        self.mutants["mutated"] = compiled(1, "", "NOT-IN-THE-PLAN\tFAIL\n")
        self.refused("mutated: the mutation failed NOT-IN-THE-PLAN, not one of")

    def test_another_fixture_of_the_selection_is_not_the_intended_failure(self):
        self.mutants["mutated"] = compiled(1, "", "key/never\tFAIL\n")
        self.refused(r"mutated: the mutation failed key/never, not one of \['key/handle-utf8'\]")

    def test_wrong_mutation_exit_is_refused(self):
        self.mutants["mutated"] = compiled(2, "key/never\tPASS\n", "key/handle-utf8\tFAIL\n")
        self.refused("mutated: the mutation did not fail exactly one selected observation")

    def test_failure_without_a_marker_is_refused(self):
        self.mutants["mutated"] = compiled(1, "", "compiler error\n")
        self.refused("mutated: the mutation did not fail exactly one selected observation")

    def test_unrelated_exception_is_refused(self):
        self.mutants["mutated-support"] = compiled(2, "", "Fatal error: exception Not_found\n")
        self.refused("mutated-support: the mutation did not fail exactly one selected observation")

    def test_two_failed_observations_are_refused(self):
        self.mutants["mutated"] = compiled(1, "", "key/handle-utf8\tFAIL\nnames/mulCap\tFAIL\n")
        self.refused("mutated: the mutation did not fail exactly one selected observation")

    def test_changed_prefix_before_the_failure_is_refused(self):
        self.mutants["mutated-support"] = compiled(1, "key/never\tPASS\n", "names/mulCap\tFAIL\n")
        self.refused("mutated-support: the observations before names/mulCap differ")

    def test_mutation_that_does_not_fail_is_refused(self):
        self.mutants["mutated"] = self.actual
        self.refused("mutated: the mutation did not fail exactly one selected observation")

    def test_missing_mutation_anchor_is_refused(self):
        self.files["normalization.ml"] = "let f s i = 0\n"
        self.refused("mutated: mutation anchor missing or ambiguous")

    def test_mutation_of_a_fixture_outside_the_selection_is_refused(self):
        self.files = self.produced([f for f in self.fixtures if f[0] != "names/mulCap"])
        self.actual = compiled(stdout="key/never\tPASS\nkey/handle-utf8\tPASS\ncontains-order\tPASS\n")
        self.refused(r"mutated-support: \['names/mulCap'\] is not a host fixture of the selection")

    def test_repaired_mismatch_writes_the_observation_first(self):
        self.actual = compiled(stdout="key/never\tPASS\nkey/handle-utf8\tWRONG\n")
        self.refused("compiled OCaml observations differ .*line 2: observed 'key/handle-utf8\\\\tWRONG'")
        self.assertEqual((self.out / "actual.txt").read_text(), "key/never\tPASS\nkey/handle-utf8\tWRONG\n")
        self.assertFalse((self.out / "ocaml.json").exists())
        # The step stopped, and it kept what it ran.
        processes = json.loads((self.out / "processes.json").read_text())
        self.assertEqual(processes[-1]["command"], ["{out}/normalization"])

    def test_failed_observation_keeps_the_prefix_and_the_failure(self):
        self.actual = compiled(1, "key/never\tPASS\n", "key/handle-utf8\tFAIL\n")
        self.refused(r"\(exit 1\): the run stopped before 'key/handle-utf8\\tPASS'\nkey/handle-utf8\tFAIL")
        self.assertEqual((self.out / "actual.txt").read_text(), "key/never\tPASS\n")

    def test_failed_compilation_keeps_its_full_diagnostic(self):
        diagnostic = "File normalization.ml, line 1:\n" + "x" * 9000 + "\nError: unbound value\n"
        original = self.execute

        def failing(command):
            if "-o" in command:
                self.calls.append(command)
                return compiled(2, "", diagnostic)
            return original(command)
        with self.assertRaises(RuntimeError) as caught:
            checkpoint.step_compiler(self.out, execute=failing)
        self.assertIn(diagnostic, str(caught.exception))
        self.assertEqual(json.loads((self.out / "processes.json").read_text())[-1]["stderr"], diagnostic)
        self.assertFalse((self.out / "actual.txt").exists())

    def test_repaired_report_that_shrinks_plan_and_rows_is_refused(self):
        self.files = {**self.files, "normalization.json": self.produced(source=["key/never"])["normalization.json"]}
        # The report is consistent with itself: only the request shows the missing fixture.
        self.assertEqual(validate(json.loads(self.files["normalization.json"])), 0)
        self.refused("normalization.json: requested input domain changed")

    def test_report_with_another_profile_is_refused(self):
        changed = {**self.profile, "target-fuel": "4"}
        self.files = {**self.files, "normalization.json": self.produced(pins=changed)["normalization.json"]}
        self.refused("normalization.json: input profile or toolchain changed")

    def test_report_bound_to_another_selection_is_refused(self):
        other = self.produced(self.fixtures + [("merge/never/never", ["source", "target", "host"])])
        self.files = {**self.files, "validity.json": other["validity.json"]}
        self.refused("validity.json: input manifest changed")

    def test_expected_observations_that_differ_from_the_selection_are_refused(self):
        self.files["expected.txt"] = "key/never\tPASS\n"
        self.refused("expected.txt differs from the host lane of the selection")

    def test_closure_from_other_roots_is_refused(self):
        self.files["closure.json"] = json.dumps({"roots": ["Root.first"]})
        self.refused("validity.json: the closure does not start from the requested roots")

    def test_report_with_failed_rows_stops_the_step(self):
        bad = json.loads(self.files["normalization.json"])
        bad["rows"][0]["outcome"] = "counterexample"
        bad["summary"].update({"pass": bad["summary"]["pass"] - 1, "counterexample": 1, "exit": 1})
        self.files["normalization.json"] = json.dumps(bad)
        self.refused("normalization.json: checkpoint has unresolved or failed rows")

    def malformed(self, change, reason):
        selection = json.loads(self.files["selection.json"])
        change(selection)
        self.files["selection.json"] = json.dumps(selection)
        self.refused(reason)

    def test_selection_with_a_fixture_named_twice_is_refused(self):
        self.malformed(lambda s: s["fixtures"].append(s["fixtures"][0]), "selection.json: a fixture is named twice")

    def test_selection_with_an_unknown_lane_is_refused(self):
        self.malformed(lambda s: s["fixtures"][0].update(lanes=["wasm"]), "selection.json: invalid fixtures")

    def test_selection_with_a_fixture_in_no_lane_is_refused(self):
        self.malformed(lambda s: s["fixtures"][0].update(lanes=[]), "selection.json: invalid fixtures")

    def test_selection_of_another_format_is_refused(self):
        self.malformed(lambda s: s.update(format="conform-report-v2"), "selection.json: unsupported format")

    def test_selection_for_another_tool_is_refused(self):
        self.malformed(lambda s: s.update(tool="other"), "selection.json: written for the tool 'other'")

    def test_missing_selection_is_refused(self):
        del self.files["selection.json"]
        self.refused("selection.json")

    def test_the_production_mutations_name_fixtures_by_name(self):
        for spec in checkpoint.MUTATIONS:
            for name in spec["fails"]:
                self.assertFalse(name.isdigit(), f"{spec['id']} names a fixture by its number")


if __name__ == "__main__":
    unittest.main()
