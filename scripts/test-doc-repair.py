#!/usr/bin/env python3
"""A deleted path keeps its evidence; a typo and generated prose remain findings."""
import subprocess
import tempfile
import unittest
from pathlib import Path

from lib.doc_refs import repair_deleted_paths, stale_references


class DocumentRepair(unittest.TestCase):
    def test_repairs_deletions_without_inventing_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'src').mkdir()
            (root / 'src/Old.lean').write_text('def old := 1\n')
            (root / 'src/Pending.lean').write_text('def pending := 2\n')
            (root / 'Makefile').write_text('check:\n')
            (root / 'README.md').write_text(
                'Keep `src/Old.lean:3` and [old](src/Old.lean#heading).\n'
                'Keep `src/Pending.lean`.\nMissing `src/Typo.lean`.\n')
            (root / 'generated.md').write_text('<!-- GENERATED -->\nKeep `src/Old.lean`.\n')
            def git(*args):
                return subprocess.run(['git', *args], cwd=root, check=True,
                                      capture_output=True, text=True).stdout.strip()
            git('init', '--quiet')
            git('add', 'src/Old.lean', 'src/Pending.lean', 'Makefile', 'README.md', 'generated.md')
            git('-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '--quiet', '-m', 'before')
            before = git('rev-parse', 'HEAD')
            git('rm', 'src/Old.lean')
            git('-c', 'user.name=Test', '-c', 'user.email=test@example.invalid', 'commit', '--quiet', '-m', 'delete')
            head = git('rev-parse', 'HEAD')
            (root / 'src/Pending.lean').unlink()
            self.assertEqual(3, len(repair_deleted_paths(root)))
            result = (root / 'README.md').read_text()
            self.assertIn(f'`git:{before}:src/Old.lean`', result)
            self.assertIn(f'[old](git:{before}:src/Old.lean)', result)
            self.assertIn(f'`git:{head}:src/Pending.lean`', result)
            self.assertEqual({'src/Typo.lean', 'src/Old.lean'}, {item.text for item in stale_references(root)})
            self.assertEqual([], repair_deleted_paths(root))


if __name__ == '__main__':
    unittest.main()
