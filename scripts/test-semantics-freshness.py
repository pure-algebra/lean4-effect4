#!/usr/bin/env python3
"""Exercise Make's semantics cache with disposable files; no Lean or host tools run."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("semantics_check", ROOT / "scripts/check-semantics.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class Freshness(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="semantics-make-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.original_root = checker.ROOT
        checker.ROOT = self.root
        self.addCleanup(setattr, checker, "ROOT", self.original_root)
        self.write("Makefile", (ROOT / "Makefile").read_bytes())
        self.write("scripts/check-semantics.py", (ROOT / "scripts/check-semantics.py").read_bytes())
        for name in (*checker.INPUTS, *checker.POLICY_FILES):
            if not (self.root / name).exists():
                self.write(name)
        self.write("src/Imported.lean")
        self.write("tools/ProofGraph/Ledger.lean")
        self.write("tools/Tools/GeneratedStamp.lean")
        self.write("ts/eff/test/nested/control.ts")
        self.artifact = ".lake/build/lib/lean/Imported.olean"
        self.write(self.artifact)
        self.write(".lake/build/lib/lean/Imported.trace")
        self.write(".lake/packages/dep/Dep/Imported.lean")
        self.write(".lake/packages/dep/lakefile.toml")
        for target in checker.TARGETS:
            relative = target.replace(".", "/")
            self.write(checker.TRACE_DIR + relative + ".trace")
            self.write(".lake/build/ir/" + relative + ".setup.json")
        for name in checker.FILES:
            self.write("generated/" + name)
        for name in ("effect/package.json", "@typescript/native-preview/package.json",
                     "@typescript/native-preview/bin/tsgo"):
            self.write("ts/eff/node_modules/" + name)
        # Existing Make input discovery traverses these directories, without running tools.
        (self.root / ".lake/packages").mkdir(parents=True, exist_ok=True)
        for directory in ("tools/Conform", "ocaml", "src/Effect4/Schema", "Test/fixtures/trust-gate"):
            (self.root / directory).mkdir(parents=True, exist_ok=True)
        for mode, directory in (("generate", "gen"), ("check", "check")):
            receipt = {"result": "passed", "mode": mode, "savedOutputs": {self.artifact: "saved"},
                       "outputDirectory": "generated"}
            receipt["dependencyFiles"] = checker.dependency_files(mode, receipt)
            self.write(f".lake/{directory}/semantics.receipt.json", json.dumps(receipt).encode())
            self.write(f".lake/{directory}/semantics", b"", 200)

    def write(self, name, data=b"{}", timestamp=100):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        os.utime(path, (timestamp, timestamp))

    def make(self, expected):
        for mode in ("gen", "check"):
            result = subprocess.run(["make", "-q", f".lake/{mode}/semantics"], cwd=self.root,
                                    capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, expected, result.stderr + result.stdout)

    def alter_receipts(self, update):
        for directory in ("gen", "check"):
            path = self.root / f".lake/{directory}/semantics.receipt.json"
            receipt = json.loads(path.read_text())
            update(receipt)
            path.write_text(json.dumps(receipt))

    def test_unchanged_skips_without_tools(self):
        self.make(0)

    def test_build_configuration_changes_invalidate(self):
        for name in ("lakefile.toml", "lake-manifest.json", "Makefile", "lean-toolchain"):
            with self.subTest(name=name):
                os.utime(self.root / name, (300, 300))
                self.make(1)
                os.utime(self.root / name, (100, 100))

    def test_prepared_artifact_and_transitive_source_changes_invalidate(self):
        for name in (self.artifact, "src/Imported.lean", ".lake/build/ir/Effect4/Laws.setup.json"):
            with self.subTest(name=name):
                os.utime(self.root / name, (300, 300))
                self.make(1)
                os.utime(self.root / name, (100, 100))

    def test_deleted_inputs_do_not_disappear_from_globs(self):
        for name in (self.artifact, ".lake/build/lib/lean/Imported.trace",
                     ".lake/packages/dep/Dep/Imported.lean", ".lake/packages/dep/lakefile.toml",
                     "src/Imported.lean", "generated/semantics.json",
                     "generated/semantics.md"):
            with self.subTest(name=name):
                path = self.root / name
                data = path.read_bytes()
                path.unlink()
                self.make(1)
                self.write(name, data)

    def test_package_changes_invalidate(self):
        for name in (".lake/packages/dep/Dep/Imported.lean", ".lake/packages/dep/lakefile.toml"):
            with self.subTest(name=name):
                os.utime(self.root / name, (300, 300))
                self.make(1)
                os.utime(self.root / name, (100, 100))

    def test_new_source_is_discovered(self):
        self.write("src/New.lean", timestamp=300)
        self.make(1)

    def test_nested_typescript_deletion_invalidates_check(self):
        (self.root / "ts/eff/test/nested/control.ts").unlink()
        result = subprocess.run(["make", "-q", ".lake/check/semantics"], cwd=self.root,
                                capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 1, result.stderr)

    def test_modified_report_invalidates(self):
        self.write("generated/semantics.json", b"changed", 300)
        self.make(1)

    def test_old_receipt_invalidates_once(self):
        self.alter_receipts(lambda receipt: receipt.pop("dependencyFiles"))
        self.make(1)

    def test_failed_receipt_cannot_reuse_success_marker(self):
        self.alter_receipts(lambda receipt: receipt.update(result="failed"))
        self.make(1)

    def test_missing_and_malformed_receipts_refuse_cache(self):
        for directory in ("gen", "check"):
            (self.root / f".lake/{directory}/semantics.receipt.json").unlink()
        self.make(1)
        for directory in ("gen", "check"):
            self.write(f".lake/{directory}/semantics.receipt.json", b"not json")
        self.make(1)

    def test_external_generation_cannot_refresh_default_cache(self):
        self.alter_receipts(lambda receipt: receipt.update(outputDirectory="/tmp/elsewhere"))
        self.assertEqual(checker.make_dependencies("generate"), "FORCE")

    def test_invalid_saved_paths_refuse_cache(self):
        for invalid in ("../elsewhere", "/tmp/elsewhere", "a\nb", {"not": "a path"}):
            with self.subTest(path=invalid):
                self.alter_receipts(lambda receipt: receipt["dependencyFiles"].append(invalid))
                self.make(1)
                self.alter_receipts(lambda receipt: receipt["dependencyFiles"].pop())

    def test_inventory_remembers_sources_and_excludes_installed_typescript(self):
        self.write("ts/eff/node_modules/irrelevant/implementation.ts")
        receipt = {"savedOutputs": {self.artifact: "saved"}}
        files = checker.dependency_files("check", receipt)
        self.assertIn("ts/eff/test/nested/control.ts", files)
        self.assertIn("src/Imported.lean", files)
        self.assertIn(self.artifact, files)
        self.assertNotIn("ts/eff/node_modules/irrelevant/implementation.ts", files)

    def generate_with_stub_producer(self, change_inventory=False):
        """Exercise publication around a stub producer; no claim about Lean evidence."""
        preflights = 0

        def prepared(receipt):
            nonlocal preflights
            preflights += 1
            receipt["savedOutputs"] = {self.artifact: "saved"}
            if change_inventory and preflights == 2:
                self.write("src/AddedDuringRun.lean")

        def produce(_file, _receipt, stage):
            (stage / "semantics.json").write_text(json.dumps({
                "provenance": {"roots": [checker.TARGETS[0]]}}))
            (stage / "semantics.md").write_text("new report\n")

        with patch.object(checker, "require_artifacts", prepared), \
                patch.object(checker, "lean", produce), \
                patch.object(checker, "run", return_value=""), \
                patch.object(checker.sys, "argv", ["check-semantics.py", "--generate", "generated"]):
            result = checker.main()
        self.assertEqual(preflights, 2)
        return result

    def test_successful_generation_saves_inventory(self):
        self.assertEqual(self.generate_with_stub_producer(), 0)
        receipt = json.loads((self.root / ".lake/gen/semantics.receipt.json").read_text())
        self.assertEqual(receipt["result"], "passed")
        self.assertEqual(receipt["outputDirectory"], "generated")
        self.assertIn(self.artifact, receipt["dependencyFiles"])
        self.assertNotEqual(checker.make_dependencies("generate"), "FORCE")

    def test_inventory_change_before_publication_preserves_report(self):
        before = {name: (self.root / "generated" / name).read_bytes() for name in checker.FILES}
        self.assertEqual(self.generate_with_stub_producer(change_inventory=True), 1)
        self.assertEqual(before, {name: (self.root / "generated" / name).read_bytes()
                                  for name in checker.FILES})
        self.assertEqual(checker.make_dependencies("generate"), "FORCE")


if __name__ == "__main__":
    unittest.main(verbosity=2)
