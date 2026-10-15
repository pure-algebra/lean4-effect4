#!/usr/bin/env python3
"""Controls for stale passes, failed runs and cross-worktree result reuse."""
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from lib.gate_cache import prepare, run

REPO = Path(__file__).resolve().parents[1]


class GateCache(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.base = Path(self.directory.name)
        self.root = self.base / 'first'
        self.root.mkdir()
        (self.root / 'source').write_text('one')
        self.store = self.base / 'store'
        self.tools = patch('lib.gate_cache.tool_identity', return_value={'python': 'test'})
        self.tools.start()
        self.addCleanup(self.tools.stop)

    def key(self, root=None):
        return prepare(root or self.root, 'probe', ['source'])

    def execute(self, script, root=None):
        return run(root or self.root, 'probe', [sys.executable, '-c', script], store=self.store)

    def test_times_do_not_change_identity_but_same_time_edit_does(self):
        first = self.key()
        stamp = self.root / '.lake/check/probe.key'
        before = stamp.stat().st_mtime_ns
        source = self.root / 'source'
        old = source.stat()
        os.utime(source, ns=(old.st_atime_ns, old.st_mtime_ns + 1_000_000_000))
        self.assertEqual(first, self.key())
        self.assertEqual(before, stamp.stat().st_mtime_ns)
        source.write_text('two')
        os.utime(source, ns=(old.st_atime_ns, old.st_mtime_ns))
        self.assertNotEqual(first, self.key())

    def test_same_inputs_in_another_worktree_reuse_pass(self):
        second = self.base / 'second'
        second.mkdir()
        (second / 'source').write_text('one')
        self.assertEqual(self.key(), self.key(second))
        script = "from pathlib import Path; Path('ran').write_text('yes')"
        self.assertEqual(0, self.execute(script))
        self.assertEqual(0, self.execute(script, second))
        self.assertFalse((second / 'ran').exists())
        self.assertTrue((second / '.lake/check/probe').is_file())

    def test_failure_is_never_cached(self):
        key = self.key()
        self.assertEqual(7, self.execute('raise SystemExit(7)'))
        self.assertFalse((self.store / 'probe' / key).exists())
        self.assertFalse((self.root / '.lake/check/probe').exists())

    def test_input_change_during_run_refuses_publication(self):
        key = self.key()
        with self.assertRaisesRegex(ValueError, 'during its run'):
            self.execute("from pathlib import Path; Path('source').write_text('two')")
        self.assertFalse((self.store / 'probe' / key).exists())

    def test_input_change_before_run_refuses_old_key(self):
        self.key()
        (self.root / 'source').write_text('two')
        with self.assertRaisesRegex(ValueError, 'after key preparation'):
            self.execute('pass')

    def test_changed_command_does_not_reuse_pass(self):
        self.key()
        self.assertEqual(0, self.execute('pass'))
        self.assertEqual(0, self.execute("from pathlib import Path; Path('different').touch()"))
        self.assertTrue((self.root / 'different').exists())

    def test_missing_input_cannot_be_an_empty_key(self):
        self.key()
        (self.root / 'source').unlink()
        with self.assertRaises(FileNotFoundError):
            self.key()

    def test_directory_addition_and_deletion_change_identity(self):
        (self.root / 'inputs').mkdir()
        original = prepare(self.root, 'probe', ['inputs'])
        (self.root / 'inputs/added').write_text('new')
        self.assertNotEqual(original, prepare(self.root, 'probe', ['inputs']))
        (self.root / 'inputs/added').unlink()
        self.assertEqual(original, prepare(self.root, 'probe', ['inputs']))

    def test_tool_and_environment_are_inputs(self):
        first = self.key()
        with patch('lib.gate_cache.tool_identity', return_value={'python': 'different'}):
            self.assertNotEqual(first, self.key())
        with patch.dict(os.environ, {'EFFECT4_TEST_PROFILE': 'first'}):
            first = prepare(self.root, 'probe', ['source'], environment=['EFFECT4_TEST_PROFILE'])
        with patch.dict(os.environ, {'EFFECT4_TEST_PROFILE': 'second'}):
            self.assertNotEqual(first, prepare(self.root, 'probe', ['source'], environment=['EFFECT4_TEST_PROFILE']))


@unittest.skipUnless(shutil.which('make'), 'GNU make integration runs in the build environment')
class MakeIntegration(unittest.TestCase):
    def test_stamp_and_shared_result_follow_content(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / 'repo'
            root.mkdir()
            (root / 'scripts/lib').mkdir(parents=True)
            for name in ['scripts/gate-cache.py', 'scripts/lib/gate_cache.py', 'scripts/lib/lean_imports.py']:
                shutil.copyfile(REPO / name, root / name)
            (root / 'source').write_text('one')
            (root / 'Makefile').write_text('''PY := python3
.PHONY: all FORCE _run
all: .lake/check/probe
.lake/check/probe.key: FORCE
\t@$(PY) scripts/gate-cache.py key probe --inputs source Makefile scripts/gate-cache.py scripts/lib/gate_cache.py
.lake/check/probe: .lake/check/probe.key
\t@$(PY) scripts/gate-cache.py run $(if $(findstring B,$(firstword $(MAKEFLAGS))),--force,) probe -- $(MAKE) --no-print-directory _run
_run:
\t@$(PY) -c "from pathlib import Path; p=Path('runs'); p.write_text(p.read_text()+'x' if p.exists() else 'x')"
''')
            def command(args, cwd=root):
                return subprocess.run(args, cwd=cwd, check=True, capture_output=True, text=True)
            command(['git', 'init', '--quiet'])
            command(['git', 'add', 'Makefile', 'source', 'scripts/gate-cache.py', 'scripts/lib/gate_cache.py',
                     'scripts/lib/lean_imports.py'])
            command(['git', '-c', 'user.name=Cache Test', '-c', 'user.email=cache@example.invalid',
                     'commit', '--quiet', '-m', 'fixture'])
            command(['make', '--no-print-directory'])
            command(['make', '--no-print-directory'])
            self.assertEqual('x', (root / 'runs').read_text())
            source = root / 'source'
            previous = source.stat()
            os.utime(source, ns=(previous.st_atime_ns, previous.st_mtime_ns + 1_000_000_000))
            command(['make', '--no-print-directory'])
            self.assertEqual('x', (root / 'runs').read_text())
            second = Path(directory) / 'second'
            command(['git', 'worktree', 'add', '--quiet', '--detach', str(second)])
            command(['make', '--no-print-directory'], second)
            self.assertFalse((second / 'runs').exists())
            source.write_text('two')
            os.utime(source, ns=(previous.st_atime_ns, previous.st_mtime_ns))
            command(['make', '--no-print-directory'])
            self.assertEqual('xx', (root / 'runs').read_text())
            command(['make', '--no-print-directory', '-B'])
            self.assertEqual('xxx', (root / 'runs').read_text())


if __name__ == '__main__':
    unittest.main()
