#!/usr/bin/env python3
"""Finite controls for dependency-ordered generation; no Lean or repository writes."""
import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import generate

from lib.derived_plan import stages


def row(name, imports, executable="effect4gen"):
    return {"name": name, "out": f"src/Effect4/{name}.lean",
            "args": ["exe", executable, "Main", "--imports", imports, "--out", f"src/Effect4/{name}.lean"]}


def fixture():
    return {
        "commands": [row("Consumer", "Effect4.Base", "effect4gen-catalogue"), row("Base", "Input")],
        "imports": [
            {"module": "Effect4Gen.Exe", "imports": ["Lean"]},
            {"module": "Effect4Gen.CatalogueExe", "imports": ["Effect4.Base"]},
            {"module": "Effect4.Base", "imports": ["Input"]},
            {"module": "Input", "imports": ["Lean"]},
            {"module": "Lean", "imports": []},
        ],
    }


class PlanControls(unittest.TestCase):
    def test_reorders_stale_or_missing_outputs(self):
        self.assertEqual([[r["name"] for r in s] for s in stages(fixture())], [["Base"], ["Consumer"]])

    def test_catalogue_compile_dependency_counts(self):
        plan = fixture()
        plan["commands"][0] = row("Consumer", "Input", "effect4gen-catalogue")
        self.assertEqual([[r["name"] for r in s] for s in stages(plan)], [["Base"], ["Consumer"]])

    def test_independent_rows_share_stage(self):
        plan = fixture()
        plan["commands"].append(row("Sibling", "Input"))
        self.assertEqual([[r["name"] for r in s] for s in stages(plan)], [["Base", "Sibling"], ["Consumer"]])

    def test_unknown_import_refuses(self):
        plan = fixture()
        plan["imports"].pop()
        with self.assertRaisesRegex(ValueError, "missing import evidence"):
            stages(plan)

    def test_duplicate_output_refuses(self):
        plan = fixture()
        extra = copy.deepcopy(plan["commands"][0])
        extra["name"] = "Other"
        plan["commands"].append(extra)
        with self.assertRaisesRegex(ValueError, "duplicate generated"):
            stages(plan)

    def test_duplicate_module_refuses(self):
        plan = fixture()
        plan["imports"].append(plan["imports"][0])
        with self.assertRaisesRegex(ValueError, "duplicate module"):
            stages(plan)

    def test_early_effect4_import_refuses(self):
        plan = fixture()
        plan["imports"][0]["imports"].append("Effect4.Base")
        with self.assertRaisesRegex(ValueError, "early generator imports"):
            stages(plan)

    def test_catalogue_self_dependency_refuses(self):
        plan = fixture()
        plan["commands"][1]["args"][1] = "effect4gen-catalogue"
        with self.assertRaisesRegex(ValueError, "own output"):
            stages(plan)

    def test_cycle_refuses(self):
        plan = fixture()
        plan["imports"][3]["imports"] = ["Effect4.Consumer"]
        plan["imports"].append({"module": "Effect4.Consumer", "imports": ["Effect4.Base"]})
        with self.assertRaisesRegex(ValueError, "own output|cycle"):
            stages(plan)

    def test_unknown_executable_refuses(self):
        plan = fixture()
        plan["commands"][0]["args"][1] = "unknown"
        with self.assertRaisesRegex(ValueError, "unknown generator"):
            stages(plan)


class EmissionControls(unittest.TestCase):
    def test_stale_output_cannot_replace_fresh_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            root, out, scratch = base / "repo", base / "out", base / "scratch"
            root.mkdir()
            out.mkdir()
            scratch.mkdir()
            plan = fixture()
            for row_ in plan["commands"]:
                for parent in [root, out]:
                    target = parent / row_["out"]
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_text("previous bytes")
            def run(args, capture=False):
                return json.dumps(plan) if capture else None
            with patch.object(generate, "ROOT", root), patch.object(generate, "run", run):
                with self.assertRaisesRegex(ValueError, "generator left no output"):
                    generate.derived(out, True, scratch)
            self.assertEqual((root / plan["commands"][1]["out"]).read_text(), "previous bytes")

    def test_output_alias_refuses_before_build(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            calls = []
            def run(args, capture=False):
                calls.append(args)
                return json.dumps(fixture())
            with patch.object(generate, "ROOT", root), patch.object(generate, "run", run):
                with self.assertRaisesRegex(ValueError, "aliases repository"):
                    generate.derived(root, True, root / "scratch")
            self.assertEqual(len(calls), 1)

    def test_check_difference_stops_before_dependent_build(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            root, out, scratch = base / "repo", base / "out", base / "scratch"
            root.mkdir()
            scratch.mkdir()
            calls = []
            plan = fixture()
            def run(args, capture=False):
                calls.append(args)
                if capture:
                    return json.dumps(plan)
                if "--batch" in args:
                    batch = json.loads(Path(args[-1]).read_text())
                    for words in batch:
                        Path(words[words.index("--out") + 1]).write_text("new bytes")
                return None
            with patch.object(generate, "ROOT", root), patch.object(generate, "run", run):
                with self.assertRaisesRegex(ValueError, "is not what Lean emits"):
                    generate.derived(out, True, scratch)
            self.assertFalse(any("effect4gen-catalogue" in call for call in calls))


if __name__ == "__main__":
    unittest.main()
