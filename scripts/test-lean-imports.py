#!/usr/bin/env python3
"""Finite controls for the shared Lean import reader (`scripts/lib/lean_imports.py`)."""
import unittest
from pathlib import Path

from lib.lean_imports import header_imports, imports_of

ROOT = Path(__file__).resolve().parents[1]


class HeaderImports(unittest.TestCase):
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

    def test_tree_ty(self):
        # `Ty.lean` opens with `module` and four `public import`s (Codex's control, HC-R8)
        self.assertEqual(imports_of(ROOT / 'src/Effect4/Program/Ty.lean'),
                         ['Effect4.Data.Row', 'Effect4.Data.FieldOrder', 'Effect4.Program.TyEq',
                          'Effect4.Program.TyVariance'])


if __name__ == '__main__':
    unittest.main()
