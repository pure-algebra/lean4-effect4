#!/usr/bin/env python3
"""Independent mutations at the compatibility boundary. No fixture is overwritten."""
import json
import copy
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'lib'))
import compatibility as c


def ty(name):
    return {'constant': name, 'levels': []}


def argument(name, type_name):
    return {'name': name, 'type': ty(type_name), 'proof': False}


def sample():
    # Independently authored tiny data, not the extractor's own output.
    return {'format': c.FORMAT, 'roots': ['Example.Sum', 'Example.Record'], 'families': [
        {'family': 'Example.Sum', 'instance': ty('Example.Sum'), 'kind': 'inductive',
         'mutual': ['Example.Sum'], 'fields': [], 'constructors': [
             {'name': 'none', 'ordinal': 0, 'arguments': []},
             {'name': 'value', 'ordinal': 1, 'arguments': [argument('n', 'Nat')]}]},
        {'family': 'Example.Record', 'instance': ty('Example.Record'), 'kind': 'structure',
         'mutual': ['Example.Record'], 'fields': ['left', 'right'], 'constructors': [
             {'name': 'mk', 'ordinal': 0, 'arguments': [argument('left', 'Nat'), argument('right', 'String')]}]},
    ], 'byte_maps': {name: [{'name': 'first', 'byte': 1}, {'name': 'second', 'byte': 7}]
                    for name in ('Kind', 'HandleKind', 'Tag')},
        'framing': {'length': 'be64', 'ctor': 'declaration-order'},
        'consumers': {'first': ['Example.Sum', 'Example.Record']}}


class CompatibilityTests(unittest.TestCase):
    def test_retained_snapshot_and_independent_actual_mutations(self):
        baseline = json.loads((c.ROOT / 'Test/fixtures/baseline/66ee4657-supplement-v1/snapshot.json').read_text())
        self.assertEqual((len(baseline['roots']), len(baseline['families'])), (49, 56))
        self.assertEqual(c.compare(baseline, copy.deepcopy(baseline))['status'], 'pass')
        def family(x, name): return next(f for f in x['families'] if f['family'] == name)
        def payload(x): family(x, 'Effect4.Machine.Err')['constructors'][1]['arguments'][0]['type'] = ty('String')
        def order(x):
            cs = family(x, 'Effect4.Program.Ty')['constructors']
            cs[0], cs[1] = cs[1], cs[0]
            for i, row in enumerate(cs): row['ordinal'] = i
        def fields(x):
            f = family(x, 'Effect4.Program.EffTy')
            f['fields'].reverse(); f['constructors'][0]['arguments'].reverse()
        def kind(x): x['byte_maps']['Kind'][0]['byte'] = 254
        def handle(x): x['byte_maps']['HandleKind'][0]['byte'] = 254
        def frame(x): x['framing']['length_definition'] = 'little-endian mutant'
        def selection(x): x['consumers']['wire'].pop()
        def toolchain(x): x['source']['toolchain'] = 'unreviewed-compiler'
        for mutate in (payload, order, fields, kind, handle, frame, selection, toolchain):
            with self.subTest(mutation=mutate.__name__):
                changed = copy.deepcopy(baseline); mutate(changed)
                self.assertEqual(c.compare(baseline, changed)['status'], 'fail')
        changed = copy.deepcopy(baseline)
        changed['byte_maps']['Tag'][1]['byte'] = changed['byte_maps']['Tag'][0]['byte']
        with self.assertRaises(ValueError): c.compare(baseline, changed)
        changed = copy.deepcopy(baseline)
        cs = family(changed, 'Effect4.Program.Ty')['constructors']
        cs.append({'name': 'futureProbe', 'ordinal': len(cs), 'arguments': []})
        self.assertEqual(c.compare(baseline, changed, {'constructor_appends': ['Effect4.Program.Ty.futureProbe']})['status'], 'pass')

    def test_unchanged(self):
        self.assertEqual(c.compare(sample(), sample())['status'], 'pass')

    def test_declared_append(self):
        newer = sample()
        newer['families'][0]['constructors'].append({'name': 'text', 'ordinal': 2, 'arguments': [argument('s', 'String')]})
        self.assertEqual(c.compare(sample(), newer, {'constructor_appends': ['Example.Sum.text']})['status'], 'pass')
        self.assertEqual(c.compare(sample(), newer)['status'], 'fail')

    def test_meaningful_mutants(self):
        def payload(x): x['families'][0]['constructors'][1]['arguments'][0]['type'] = ty('Int')
        def reorder(x):
            x['families'][0]['constructors'].reverse()
            for i, row in enumerate(x['families'][0]['constructors']): row['ordinal'] = i
        def remove(x): x['families'][0]['constructors'].pop()
        def fields(x):
            x['families'][1]['fields'].reverse()
            x['families'][1]['constructors'][0]['arguments'].reverse()
        def remap(x): x['byte_maps']['HandleKind'][1]['byte'] = 6
        def frame(x): x['framing']['length'] = 'le64'
        def selection(x): x['consumers']['first'].pop()
        for label, mutate, expected in [
            ('same-name payload', payload, 'payload'), ('constructor reorder', reorder, 'reordered'),
            ('constructor removal', remove, 'removed'), ('field reorder', fields, 'fields'),
            ('explicit byte remap', remap, 'byte map'), ('framing', frame, 'framing'),
            ('consumer omitted', selection, 'consumer selection'),
        ]:
            with self.subTest(label=label):
                newer = sample(); mutate(newer)
                result = c.compare(sample(), newer)
                self.assertEqual(result['status'], 'fail')
                self.assertTrue(any(expected in error for error in result['errors']), result)

    def test_malformed_descriptors(self):
        for mutate in [
            lambda x: x['byte_maps']['Tag'][1].update(byte=1),
            lambda x: x['families'][0]['constructors'][1].update(ordinal=0),
            lambda x: x['families'][0]['constructors'][1]['arguments'][0].update(type={'unknown': 'Nat'}),
            lambda x: x['families'][0]['constructors'][1]['arguments'][0].update(type={'bound': 0}),
            lambda x: x['families'][0].update(family='Forged.Name'),
            lambda x: x.update(roots=[]),
            lambda x: x.update(families=[]),
            lambda x: x['consumers'].update(first=[]),
        ]:
            newer = sample(); mutate(newer)
            with self.assertRaises(ValueError): c.compare(sample(), newer)

    def test_stale_and_unknown_permissions(self):
        self.assertEqual(c.compare(sample(), sample(), {'constructor_appends': ['Example.Sum.missing']})['status'], 'fail')
        with self.assertRaises(ValueError): c.compare(sample(), sample(), {'ignore_breakage': True})

    def test_policy_dimensions(self):
        before = {'fail-boolean': {'admitted': True, 'type': 'Bool'}}
        after = {'fail-boolean': {'admitted': False, 'reason': 'unsupported-error'}}
        expected = {'fail-boolean': {'before': before['fail-boolean'], 'after': after['fail-boolean']}}
        result = c.policy_delta(before, after, expected, 'admission')
        self.assertEqual(result['status'], 'pass')
        # This input-policy change does not alter an old byte or descriptor.
        self.assertEqual(c.compare(sample(), sample())['status'], 'pass')
        self.assertEqual(c.policy_delta({'sleep': True}, {'sleep': False}, {}, 'execution_permission')['status'], 'fail')
        with self.assertRaises(ValueError): c.policy_delta({'sleep': True}, {}, {}, 'execution_permission')

    def test_cli_failure_and_separate_not_run_dimensions(self):
        with tempfile.TemporaryDirectory(prefix='effect4-compatibility-test-') as tmp:
            old, new = Path(tmp) / 'old.json', Path(tmp) / 'new.json'
            old.write_text(c.canonical(sample())); new.write_text(c.canonical(sample()))
            cmd = [sys.executable, str(c.ROOT / 'scripts/check-compatibility.py'), 'compare', '--baseline', str(old), '--candidate', str(new)]
            result = subprocess.run(cmd, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            report = json.loads(result.stdout)
            for dimension in ('decoding', 'admission', 'execution_permission'):
                self.assertEqual(report[dimension]['status'], 'not_run')
            newer = sample(); newer['families'][0]['constructors'][1]['arguments'][0]['type'] = ty('Int')
            new.write_text(c.canonical(newer))
            self.assertEqual(subprocess.run(cmd, capture_output=True).returncode, 1)


if __name__ == '__main__':
    unittest.main(verbosity=2)
