#!/usr/bin/env python3
"""Detector reactions: real file removal, new misses, ignored trees and named allowances."""
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

checker = Path(__file__).with_name('check-source-citations.py')
spec = importlib.util.spec_from_file_location('citations', checker)
citations = importlib.util.module_from_spec(spec)
spec.loader.exec_module(citations)


class CitationReactions(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.put('src/' + 'Effect4' + '/Target.lean', 'import Std\n')
        self.put('docs/' + 'Guide.md', '`src/' + 'Effect4' + '/Target.lean:999999`\n')

    def put(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def run_gate(self):
        return subprocess.run([sys.executable, str(checker), '--root', str(self.root)],
                              capture_output=True, text=True)

    def test_existence_does_not_assert_line_resolution(self):
        self.assertEqual(self.run_gate().returncode, 0)

    def test_deleted_target_changes_key_and_refuses(self):
        before = citations.inspect(self.root)[0].hexdigest()
        (self.root / ('src/' + 'Effect4' + '/Target.lean')).unlink()
        self.assertNotEqual(before, citations.inspect(self.root)[0].hexdigest())
        self.assertNotEqual(self.run_gate().returncode, 0)

    def test_new_missing_path_cannot_hide_in_baseline_count(self):
        self.put(citations.BASELINE, 'src/' + 'Effect4' + '/Old.lean\n')
        self.put('docs/' + 'Guide.md', '`src/' + 'Effect4' + '/New.lean`\n')
        self.assertNotEqual(self.run_gate().returncode, 0)

    def test_excluded_research_is_not_a_source_dependency(self):
        self.put('docs/research/Notes.md', '`src/' + 'Effect4' + '/Missing.lean`\n')
        self.assertEqual(self.run_gate().returncode, 0)

    def test_authority_note_requires_visible_marker(self):
        self.put('docs/ARCHITECTURE.md', '`docs/research/Notes.md`\n')
        self.assertNotEqual(self.run_gate().returncode, 0)
        self.put('docs/ARCHITECTURE.md', '`docs/research/Notes.md` (untracked working note)\n')
        self.assertEqual(self.run_gate().returncode, 0)

    def test_allowance_is_exact(self):
        self.put(citations.ALLOW, 'src/' + 'Effect4' + '/Surface/Handler.lean\tfrozen red\n')
        self.put('docs/' + 'Guide.md', '`src/' + 'Effect4' + '/Surface/Handler.lean`\n')
        self.assertEqual(self.run_gate().returncode, 0)
        self.put('docs/' + 'Guide.md', '`src/' + 'Effect4' + '/Surface/Handlers.lean`\n')
        self.assertNotEqual(self.run_gate().returncode, 0)

    def test_case_mismatch_refuses_even_on_windows(self):
        self.put('docs/' + 'Guide.md', '`src/' + 'Effect4' + '/target.lean`\n')
        self.assertNotEqual(self.run_gate().returncode, 0)

    def test_unknown_historical_revision_refuses(self):
        self.put('docs/' + 'Guide.md', '`git:' + '0000000:src/' + 'Effect4' + '/Target.lean`\n')
        self.assertNotEqual(self.run_gate().returncode, 0)


if __name__ == '__main__':
    unittest.main()
