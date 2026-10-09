"""Finite failure-retention controls using the caller-selected pinned compiler and runtime."""
import os
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import ts_packet as packet


class PacketRetention(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix='effect4-packet-retention-test-')
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name)
        self.install = Path(os.environ['EFFECT4_TS_INSTALL']).resolve()
        truth = self.root / 'harness/truth'
        truth.mkdir(parents=True)
        for name in packet.PRELUDE_FILES:
            shutil.copyfile(packet.ROOT / 'harness/truth' / name, truth / name)
        self.output = self.root / 'output'
        packet.prepare_output(self.install, self.output)
        self.emitted = 'export const main = Effect.succeed(1)\n'
        (self.output / 'main.ts').write_text(self.emitted)
        (self.output / 'manifest.json').write_text('{"finite": true}\n')
        self.observer = self.root / 'observer.ts'
        self.observer.write_text('export const finite = true\n')
        self.root_patch = patch.object(packet, 'ROOT', self.root)
        self.root_patch.start()
        self.addCleanup(self.root_patch.stop)

    def compile(self):
        return packet.compiled_packet(self.install, self.output, ['main.ts'], self.observer,
                                      'effect4-packet-retention-case-')

    def retained(self):
        folder = self.output / 'compiled-inputs'
        return {path.name: path.read_bytes() for path in folder.iterdir()}

    def check_helpers(self, inputs):
        for name in packet.PRELUDE_FILES:
            self.assertEqual(inputs[name], (self.root / 'harness/truth' / name).read_bytes())
        expected = ''.join(f'export * from "./{name}"\n' for name in packet.PRELUDE_FILES)
        self.assertEqual(inputs['prelude.ts'], expected.encode())

    def test_helper_discovery_failure_retains_available_inputs(self):
        with (self.root / 'harness/truth/control.ts').open('a') as helper:
            helper.write('\nthrow new Error("finite helper initialization failure")\n')
        with self.assertRaisesRegex(RuntimeError, 'finite helper initialization failure'):
            with self.compile():
                self.fail('early failure must not yield a compiled packet')
        inputs = self.retained()
        self.assertEqual(set(inputs), set(packet.PRELUDE_FILES + ['prelude.ts']))
        self.check_helpers(inputs)
        self.assertIn('finite helper initialization failure', (self.output / 'failure.txt').read_text())
        self.assertEqual((self.output / 'main.ts').read_text(), self.emitted)
        self.assertFalse((self.output / 'receipt.json').exists())

    def test_compiler_failure_retains_exact_complete_inputs(self):
        (self.output / 'main.ts').write_text('export const main: string = 1\n')
        prepared = {}
        retain = packet.retain_inputs

        def capture(work, output, names, **options):
            prepared.update({name: (work / name).read_bytes() for name in names
                             if (work / name).is_file()})
            return retain(work, output, names, **options)

        with patch.object(packet, 'retain_inputs', capture):
            with self.assertRaisesRegex(RuntimeError, 'TS2322'):
                with self.compile():
                    self.fail('a compiler refusal must not yield a compiled packet')
        inputs = self.retained()
        self.assertEqual(inputs, prepared)
        self.assertEqual(len(inputs), 9)
        self.check_helpers(inputs)
        self.assertTrue(inputs['main.ts'].endswith(b'export const main: string = 1\n'))
        self.assertEqual(inputs['observe.ts'], self.observer.read_bytes())
        self.assertEqual(inputs['manifest.json'], (self.output / 'manifest.json').read_bytes())
        self.assertIn('TS2322', (self.output / 'failure.txt').read_text())
        self.assertFalse((self.output / 'receipt.json').exists())

    def test_success_keeps_strict_complete_inventory(self):
        with self.compile() as (work, diagnostics, names):
            self.assertEqual(diagnostics, '')
            packet.retain_inputs(work, self.output, names)
            self.assertEqual(self.retained(), {name: (work / name).read_bytes() for name in names})
            with self.assertRaises(FileNotFoundError):
                packet.retain_inputs(work, self.output, ['missing.ts'])
        self.assertFalse((self.output / 'failure.txt').exists())

    def test_partial_setup_failure_retains_only_existing_inputs(self):
        (self.root / 'harness/truth/control.ts').unlink()
        with self.assertRaises(FileNotFoundError):
            with self.compile():
                self.fail('missing helper must not yield a compiled packet')
        self.assertEqual(set(self.retained()), set(packet.PRELUDE_FILES[:-1]))
        self.assertIn('control.ts', (self.output / 'failure.txt').read_text())
        self.assertFalse((self.output / 'compiled-inputs/prelude.ts').exists())

    def test_output_and_version_refusals_remain(self):
        with self.assertRaisesRegex(RuntimeError, 'Refuse to overwrite retained evidence'):
            packet.prepare_output(self.install, self.output)
        fake = self.root / 'wrong-install'
        (fake / 'effect').mkdir(parents=True)
        (fake / 'effect/package.json').write_text('{"version":"wrong"}')
        absent = self.root / 'uncreated-output'
        with self.assertRaisesRegex(RuntimeError, 'Wrong installed effect version'):
            packet.prepare_output(fake, absent)
        self.assertFalse(absent.exists())
        (fake / 'effect/package.json').write_text('{"version":"4.0.1"}')
        (fake / '@typescript/native-preview').mkdir(parents=True)
        (fake / '@typescript/native-preview/package.json').write_text('{"version":"wrong"}')
        with self.assertRaisesRegex(RuntimeError, 'Wrong installed @typescript/native-preview version'):
            packet.prepare_output(fake, absent)
        self.assertFalse(absent.exists())


if __name__ == '__main__':
    unittest.main()
