#!/usr/bin/env python3
"""Controls for root repair, negative fixtures, slow batteries and Laws separation."""
import importlib.util
import tempfile
import unittest
from pathlib import Path

spec = importlib.util.spec_from_file_location('wire_roots', Path(__file__).with_name('wire-roots.py'))
roots = importlib.util.module_from_spec(spec)
spec.loader.exec_module(roots)


class RootRepair(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        for path, text in {
            'src/Effect4.lean': 'import Effect4.Core\n\n/-! The root. -/\n',
            'src/Effect4/Core.lean': '',
            'src/Effect4/Laws.lean': 'import Effect4\n',
            'Test/All.lean': 'import Effect4.Laws\nimport Test.Audit.AxiomGate\n\n#effect4_axiom_gate\n',
            'Test/Audit/AxiomGate.lean': 'private def slowLane : List String := ["Test/Slow.lean", "Test/Long.lean"]\n',
            'Test/Slow.lean': 'import Test.All\nimport Test.Long\n',
            'Test/Long.lean': '',
            'Test/fixtures/Negative.lean': 'this cannot compile\n',
        }.items():
            self.write(path, text)

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def test_routes_only_unreached_modules_and_is_idempotent(self):
        self.write('src/Effect4/New.lean', 'import Effect4.Helper\n')
        self.write('src/Effect4/Helper.lean', '')
        self.write('src/Effect4/Laws/New.lean', 'import Effect4.New\n')
        self.write('Test/New.lean', 'import Effect4.Laws.New\n')
        self.assertEqual({
            'src/Effect4.lean': ['Effect4.New'],
            'src/Effect4/Laws.lean': ['Effect4.Laws.New'],
            'Test/All.lean': ['Test.New'],
        }, roots.plan(self.root))
        self.assertTrue(roots.wire(self.root))
        self.assertEqual({}, roots.plan(self.root))
        self.assertIn('import Test.New\n\n#effect4_axiom_gate', (self.root / 'Test/All.lean').read_text())

    def test_core_must_not_import_laws(self):
        self.write('src/Effect4/New.lean', 'import Effect4.Laws.New\n')
        self.write('src/Effect4/Laws/New.lean', '')
        with self.assertRaisesRegex(ValueError, 'orphan core module reaches Laws'):
            roots.plan(self.root)

    def test_slow_exception_does_not_spread_silently(self):
        self.write('Test/New.lean', 'import Test.Long\n')
        with self.assertRaisesRegex(ValueError, 'orphan battery reaches the slow lane'):
            roots.plan(self.root)

    def test_cycles_refuse_before_writing(self):
        self.write('src/Effect4/A.lean', 'import Effect4.B\n')
        self.write('src/Effect4/B.lean', 'import Effect4.A\n')
        with self.assertRaisesRegex(ValueError, 'orphan import cycle'):
            roots.wire(self.root)


if __name__ == '__main__':
    unittest.main()
