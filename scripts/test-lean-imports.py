#!/usr/bin/env python3
"""Finite controls for the shared Lean import reader (`scripts/lib/lean_imports.py`)."""
import unittest
import tempfile
from pathlib import Path

from lib.lean_imports import header_imports, imports_of, source_closure

ROOT = Path(__file__).resolve().parents[1]


class HeaderImports(unittest.TestCase):
    def test_closure_follows_public_imports_and_cycles(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'src').mkdir()
            (root / 'src/A.lean').write_text('module\npublic import B\nimport Lean\n')
            (root / 'src/B.lean').write_text('import A\n')
            self.assertEqual(source_closure(root, ['A']), ['src/A.lean', 'src/B.lean'])

    def test_missing_root_refuses_instead_of_empty_closure(self):
        with tempfile.TemporaryDirectory() as directory:
            for entry in ['Missing', 'Missing.lean']:
                with self.subTest(entry=entry), self.assertRaises(FileNotFoundError):
                    source_closure(Path(directory), [entry])

    def test_plain(self):
        self.assertEqual(header_imports('import A\nimport B.C\n\ndef x := 1\n'), ['A', 'B.C'])

    def test_modifiers(self):
        text = 'module\n\npublic import A\nmeta import B\npublic meta import C\nimport all D\n'
        self.assertEqual(header_imports(text), ['A', 'B', 'C', 'D'])

    def test_block_comment_first(self):
        # the build profile stopped here before HC-R8
        self.assertEqual(header_imports('/-\nHeader text.\n-/\nimport A\n'), ['A'])

    def test_nested_and_line_comments(self):
        text = '/- outer /- inner -/ still -/\n-- a line\nimport A -- trailing\nimport B\n'
        self.assertEqual(header_imports(text), ['A', 'B'])

    def test_header_ends(self):
        text = 'import A\n\n/-! doc\nimport Z\n-/\n\nset_option x true\nimport Y\n'
        self.assertEqual(header_imports(text), ['A'])

    def test_prelude(self):
        self.assertEqual(header_imports('prelude\nimport Init.Core\n'), ['Init.Core'])

    def test_guillemets(self):
        self.assertEqual(header_imports('import «my mod».X\n'), ['«my mod».X'])

    def test_quoted_plain_part(self):
        # Lean reads `«Effect4»` as `Effect4` (HCF-01)
        self.assertEqual(header_imports('import «Effect4».Program.Ty\n'), ['Effect4.Program.Ty'])

    def test_module_doc_ends_header(self):
        # `/-!` is a token of the header grammar, not a comment (HCF-02)
        self.assertEqual(header_imports('import A\n/-! d -/\nimport B\n'), ['A'])

    def test_doc_comment_ends_header(self):
        # `/--` likewise (HCF-02)
        self.assertEqual(header_imports('import A\n/-- d -/\nimport B\n'), ['A'])

    def test_tree_ty(self):
        # `Ty.lean` opens with `module` and four `public import`s (Codex's control, HC-R8)
        self.assertEqual(imports_of(ROOT / 'src/Effect4/Program/Ty.lean'),
                         ['Effect4.Data.Row', 'Effect4.Data.FieldOrder', 'Effect4.Program.TyEq',
                          'Effect4.Program.TyVariance'])


if __name__ == '__main__':
    unittest.main()
