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


def tagged_sample(tags, order=None):
    """The sample in the second format, its sum redeclared in `order` and tagged by `tags`."""
    result = sample()
    result['format'] = c.FORMAT_TAGGED
    if order is not None:
        known = {row['name']: row for row in result['families'][0]['constructors']}
        result['families'][0]['constructors'] = [
            dict(known.get(name, {'name': name, 'arguments': []}), name=name, ordinal=i) for i, name in enumerate(order)]
    c.apply_tags(result['families'], tags)
    return result


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
        self.assertEqual(c.compare(baseline, changed, {'constructor_additions': ['Effect4.Program.Ty.futureProbe']})['status'], 'pass')

    def test_the_named_policy_is_well_formed_and_names_the_choose_history(self):
        policy = json.loads((c.ROOT / 'Test/fixtures/baseline/66ee4657-supplement-v1.policy.json').read_text())
        checked = c.read_policy(policy)
        self.assertEqual(checked['baseline'], '66ee4657-supplement-v1')
        row = checked['historical_renumbering'][0]
        self.assertEqual((row['family'], row['removed']), ('Effect4.Program.Eff', {'choose': 23}))
        # The baseline against itself uses none of the policy: every entry is then stale.
        baseline = json.loads((c.ROOT / 'Test/fixtures/baseline/66ee4657-supplement-v1/snapshot.json').read_text())
        result = c.compare(baseline, copy.deepcopy(baseline), policy)
        self.assertEqual(result['status'], 'fail')
        self.assertTrue(any('unused exemption Effect4.Program.Eff.choose' in e for e in result['errors']), result)

    def test_the_assignment_file_obeys_its_own_rules(self):
        tags = c.wire_tags(lambda path: (c.ROOT / path).read_bytes())
        self.assertIn('Effect4.Program.Eff', tags)
        for bad in [
            {'format': 'other', 'families': {}},
            {'format': c.TAGS_FORMAT, 'families': {}, 'extra': 1},
            {'format': c.TAGS_FORMAT, 'families': {'F': {'active': {'a': 0, 'b': 0}, 'retired': {}}}},
            {'format': c.TAGS_FORMAT, 'families': {'F': {'active': {'a': 0}, 'retired': {'z': 0}}}},
            {'format': c.TAGS_FORMAT, 'families': {'F': {'active': {'a': 0}, 'retired': {'a': 4}}}},
            {'format': c.TAGS_FORMAT, 'families': {'F': {'active': {}, 'retired': {}}}},
            {'format': c.TAGS_FORMAT, 'families': {'F': {'active': {'a': -1}, 'retired': {}}}},
            {'format': c.TAGS_FORMAT, 'families': {'F': {'active': {'a': 0}}}},
        ]:
            with self.assertRaises(ValueError): c.wire_tags(lambda path, bad=bad: json.dumps(bad).encode())
        # A key written twice would silently keep its last row in an ordinary JSON reader.
        twice = '{"format": "%s", "families": {"F": {"active": {"a": 0, "a": 1}, "retired": {}}}}' % c.TAGS_FORMAT
        with self.assertRaises(ValueError): c.wire_tags(lambda path: twice.encode())
        self.assertIsNone(c.wire_tags(lambda path: (_ for _ in ()).throw(FileNotFoundError(path))))

    def test_unchanged(self):
        self.assertEqual(c.compare(sample(), sample())['status'], 'pass')

    def test_declared_addition(self):
        newer = sample()
        newer['families'][0]['constructors'].append({'name': 'text', 'ordinal': 2, 'arguments': [argument('s', 'String')]})
        self.assertEqual(c.compare(sample(), newer, {'constructor_additions': ['Example.Sum.text']})['status'], 'pass')
        self.assertEqual(c.compare(sample(), newer)['status'], 'fail')

    def test_tags_are_not_positions(self):
        # The declaration order changes and a constructor is inserted in the middle; every
        # retained constructor keeps its tag, so every retained byte keeps its meaning.
        newer = tagged_sample({'Example.Sum': {'active': {'fresh': 2, 'value': 1, 'none': 0}, 'retired': {}}},
                              order=['fresh', 'value', 'none'])
        self.assertEqual(c.compare(sample(), newer, {'constructor_additions': ['Example.Sum.fresh']})['status'], 'pass')
        # The same declaration with positional tags moves `value` and `none`: refused.
        moved = tagged_sample({'Example.Sum': {'active': {'fresh': 0, 'value': 1, 'none': 2}, 'retired': {}}},
                              order=['fresh', 'value', 'none'])
        result = c.compare(sample(), moved, {'constructor_additions': ['Example.Sum.fresh']})
        self.assertEqual(result['status'], 'fail')
        self.assertTrue(any('changed wire tag' in e for e in result['errors']), result)
        self.assertTrue(any('reused wire tag' in e for e in result['errors']), result)

    def test_retirement_leaves_a_hole_for_good(self):
        retire = {'constructor_retirements': ['Example.Sum.none']}
        holed = tagged_sample({'Example.Sum': {'active': {'value': 1}, 'retired': {'none': 0}}}, order=['value'])
        self.assertEqual(c.compare(sample(), holed, retire)['status'], 'pass')
        self.assertEqual(c.compare(sample(), holed)['status'], 'fail')
        # Deleted without a retired row: a constructor leaves by retirement only.
        deleted = tagged_sample({'Example.Sum': {'active': {'value': 1}, 'retired': {}}}, order=['value'])
        self.assertTrue(any('removed constructor' in e for e in c.compare(sample(), deleted, retire)['errors']))
        # Retired at another tag than it held.
        shifted = tagged_sample({'Example.Sum': {'active': {'value': 1}, 'retired': {'none': 5}}}, order=['value'])
        self.assertTrue(any('retired at tag 5' in e for e in c.compare(sample(), shifted, retire)['errors']))
        # The hole is taken by a new constructor: a reused tag, whatever the policy names.
        reuse = tagged_sample({'Example.Sum': {'active': {'value': 1, 'fresh': 0}, 'retired': {}}}, order=['value', 'fresh'])
        result = c.compare(sample(), reuse, {'constructor_additions': ['Example.Sum.fresh'], **retire})
        self.assertTrue(any('reused wire tag 0 of none' in e for e in result['errors']), result)
        # Across two promotions: the retired row stays, is never dropped and never comes back.
        later = tagged_sample({'Example.Sum': {'active': {'value': 1, 'fresh': 2}, 'retired': {'none': 0}}}, order=['value', 'fresh'])
        self.assertEqual(c.compare(holed, later, {'constructor_additions': ['Example.Sum.fresh']})['status'], 'pass')
        dropped = tagged_sample({'Example.Sum': {'active': {'value': 1}, 'retired': {}}}, order=['value'])
        self.assertTrue(any('retired row dropped' in e for e in c.compare(holed, dropped)['errors']))
        back = tagged_sample({'Example.Sum': {'active': {'value': 1, 'none': 0}, 'retired': {}}}, order=['value', 'none'])
        self.assertTrue(any('retired row dropped' in e for e in c.compare(holed, back)['errors']))
        reborn = tagged_sample({'Example.Sum': {'active': {'value': 1, 'none': 7}, 'retired': {}}}, order=['value', 'none'])
        self.assertTrue(any('retired constructor declared again' in e or 'retired row dropped' in e
                            for e in c.compare(holed, reborn)['errors']))
        # A retired constructor's fields are gone, so a retained one that changed fields is
        # not excused by any retirement.
        changed = copy.deepcopy(holed)
        changed['families'][0]['constructors'][0]['arguments'][0]['type'] = ty('Int')
        self.assertTrue(any('changed payload' in e for e in c.compare(sample(), changed, retire)['errors']))

    def test_historical_exemption_is_exact(self):
        def exemption(**rows):
            return {'historical_renumbering': [dict({'family': 'Example.Sum', 'commit': 'abc', 'reason': 'test',
                                                       'removed': {}, 'moved': {}, 'reused': {}}, **rows)]}
        moved = tagged_sample({'Example.Sum': {'active': {'value': 0}, 'retired': {}}}, order=['value'])
        ok = exemption(removed={'none': 0}, moved={'value': [1, 0]})
        self.assertEqual(c.compare(sample(), moved, ok)['status'], 'pass')
        for bad in [exemption(removed={'none': 0}),                                  # the move is not named
                    exemption(moved={'value': [1, 0]}),                              # the removal is not named
                    exemption(removed={'none': 3}, moved={'value': [1, 0]}),         # the wrong tag
                    exemption(removed={'none': 0, 'ghost': 9}, moved={'value': [1, 0]}),   # an unused row
                    exemption(removed={'none': 0}, moved={'value': [1, 0]}, reused={'value': 0})]:
            self.assertEqual(c.compare(sample(), moved, bad)['status'], 'fail', bad)
        with self.assertRaises(ValueError): c.compare(sample(), moved, {'historical_renumbering': [{'family': 'Example.Sum'}]})
        with self.assertRaises(ValueError): c.compare(sample(), moved, exemption(moved={'value': [1, 1]}))
        # A vacated tag taken by a new constructor must be named as reused.
        taken = tagged_sample({'Example.Sum': {'active': {'value': 0, 'fresh': 1}, 'retired': {}}}, order=['value', 'fresh'])
        add = {'constructor_additions': ['Example.Sum.fresh']}
        self.assertEqual(c.compare(sample(), taken, {**add, **exemption(removed={'none': 0}, moved={'value': [1, 0]}, reused={'fresh': 1})})['status'], 'pass')
        self.assertEqual(c.compare(sample(), taken, {**add, **exemption(removed={'none': 0}, moved={'value': [1, 0]})})['status'], 'fail')

    def test_malformed_tagged_snapshot(self):
        good = tagged_sample({'Example.Sum': {'active': {'none': 0, 'value': 4}, 'retired': {'old': 2}}})
        c.validate(good)
        for mutate in [
            lambda x: x['families'][0]['constructors'][1].update(tag=0),                   # a tag twice
            lambda x: x['families'][0]['retired'][0].update(tag=4),                        # a retired tag in use
            lambda x: x['families'][0]['retired'][0].update(name='none'),                  # a retired name in use
            lambda x: x['families'][0]['constructors'][0].pop('tag'),
            lambda x: x['families'][0].pop('retired'),
            lambda x: x['families'][1]['constructors'][0].update(tag=3),                   # a structure is tag 0
            lambda x: x['families'][1]['retired'].append({'name': 'old', 'tag': 9}),
        ]:
            newer = copy.deepcopy(good); mutate(newer)
            with self.assertRaises(ValueError): c.validate(newer)

    def test_retained_vectors(self):
        with tempfile.TemporaryDirectory(prefix='effect4-compatibility-test-') as tmp:
            root = Path(tmp)
            (root / 'kept.hex').write_bytes(b'0a\n'); (root / 'moved.bin').write_bytes(b'new')
            (root / 'note.json').write_bytes(b'changed, but not a byte vector')
            listing = '\n'.join(f'{c.digest(data)}  {path}' for path, data in [
                ('kept.hex', b'0a\n'), ('moved.bin', b'old'), ('gone.bin', b'x'), ('note.json', b'before')]) + '\n'
            named = {'vector_removals': ['gone.bin'], 'vector_migrations': ['moved.bin']}
            result = c.retained_vectors(listing, root, named)
            self.assertEqual((result['status'], result['unchanged']), ('pass', 1))
            self.assertEqual(c.retained_vectors(listing, root)['status'], 'fail')
            for stale in [{'vector_removals': ['gone.bin', 'kept.hex'], 'vector_migrations': ['moved.bin']},
                          {'vector_removals': ['gone.bin'], 'vector_migrations': ['moved.bin', 'kept.hex']},
                          {'vector_removals': ['gone.bin', 'never.bin'], 'vector_migrations': ['moved.bin']}]:
                self.assertEqual(c.retained_vectors(listing, root, stale)['status'], 'fail', stale)
            with self.assertRaises(ValueError): c.retained_vectors('not a digest row\n', root, named)

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
            ('same-name payload', payload, 'payload'), ('constructor reorder', reorder, 'changed wire tag'),
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
        for kind in ('constructor_additions', 'constructor_retirements', 'family_additions', 'consumer_additions'):
            self.assertEqual(c.compare(sample(), sample(), {kind: ['Example.Sum.missing']})['status'], 'fail', kind)
        with self.assertRaises(ValueError): c.compare(sample(), sample(), {'ignore_breakage': True})
        with self.assertRaises(ValueError): c.compare(sample(), sample(), {'constructor_appends': []})
        with self.assertRaises(ValueError): c.compare(sample(), sample(), {'format': 'some-other-policy'})
        with self.assertRaises(ValueError): c.compare(sample(), sample(), {'constructor_additions': ['x', 'x']})

    def test_family_and_consumer_additions_are_named(self):
        newer = sample()
        newer['families'].append({'family': 'Example.New', 'instance': ty('Example.New'), 'kind': 'inductive',
                                  'mutual': ['Example.New'], 'fields': [], 'constructors': [{'name': 'only', 'ordinal': 0, 'arguments': []}]})
        newer['consumers']['first'] = ['Example.Record', 'Example.New', 'Example.Sum']   # order moves no byte
        newer['consumers']['second'] = ['Example.New']
        named = {'family_additions': ['Example.New'], 'consumer_additions': ['first:Example.New', 'second:Example.New']}
        self.assertEqual(c.compare(sample(), newer, named)['status'], 'pass')
        for drop in ('family_additions', 'consumer_additions'):
            self.assertEqual(c.compare(sample(), newer, {k: v for k, v in named.items() if k != drop})['status'], 'fail')
        gone = sample(); gone['consumers'] = {'other': ['Example.Sum']}
        self.assertTrue(any('removed consumer' in e for e in c.compare(sample(), gone, {'consumer_additions': ['other:Example.Sum']})['errors']))

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

    def test_promotion_refusals_leave_the_baselines_alone(self):
        baselines = c.ROOT / 'Test/fixtures/baseline'
        before = sorted(str(p.relative_to(baselines)) for p in baselines.rglob('*'))
        head = c.resolve_revision(c.ROOT, 'HEAD')
        good_name = head[:8] + '-probe'
        script = str(c.ROOT / 'scripts/check-compatibility.py')
        with tempfile.TemporaryDirectory(prefix='effect4-compatibility-test-') as tmp:
            def promote(source, destination, name):
                work = Path(tempfile.mkdtemp(dir=tmp))
                (work / 'source.json').write_text(json.dumps(source))
                return subprocess.run([sys.executable, script, 'promote', '--work', str(work),
                                       '--destination', str(destination), '--name', name],
                                      capture_output=True, text=True)
            committed = {'origin': 'git', 'revision': head}
            cases = [
                ('an existing baseline is never overwritten', committed, baselines / '66ee4657-supplement-v1', '66ee4657-supplement-v1', 'new sibling'),
                ('the original baseline is never a destination', committed, baselines / '66ee4657', '66ee4657-x', 'new sibling'),
                ('a baseline lives beside the others', committed, Path(tmp) / good_name, good_name, 'new sibling'),
                ('a baseline name has a fixed form', committed, baselines / 'Probe', 'Probe', 'baseline name'),
                ('the directory carries the name', committed, baselines / (good_name + '-other'), good_name, 'must carry'),
                ('a working tree is not an origin', {'origin': 'working-tree', 'revision': head}, baselines / good_name, good_name, 'working-tree'),
                ('a moving name is not an origin', {'origin': 'git', 'revision': 'HEAD'}, baselines / good_name, good_name, 'immutable commit'),
                ('the name begins with its revision', committed, baselines / '00000000-probe', '00000000-probe', 'first eight digits'),
            ]
            for label, source, destination, name, expected in cases:
                with self.subTest(label=label):
                    result = promote(source, destination, name)
                    self.assertEqual(result.returncode, 1, result.stderr)
                    self.assertIn(expected, result.stderr)
        self.assertEqual(before, sorted(str(p.relative_to(baselines)) for p in baselines.rglob('*')))
        for name in ('66ee4657-supplement-v1', head[:8] + '-eff-series'):
            self.assertEqual(c.baseline_name(name), name)
        for name in ('', 'series', '66EE4657-x', '66ee4657', '66ee4657_x', '66ee4657-', None):
            with self.assertRaises(ValueError): c.baseline_name(name)

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
