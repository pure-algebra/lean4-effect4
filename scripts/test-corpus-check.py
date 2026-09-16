#!/usr/bin/env python3
"""Planted defects the corpus checker's acceptance logic must refuse (`make check-tools`).

The audit of 2026-09-13 reproduced four ways `scripts/check-corpus.py` accepted what it had
not checked: a program never compiled was labelled compiler-clean, a synchronous-exit
disagreement was dropped by the parent, a worsened schedule difference left the saved row
unchanged, and a registered program name excused any disagreement of that program. Each is a
case below, against the checker's pure classification, registration and verdict functions;
no host, compiler or Lean process runs.
"""
import importlib.util
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location('check_corpus', ROOT / 'scripts/check-corpus.py')
check = importlib.util.module_from_spec(spec)
spec.loader.exec_module(check)


def entry(name, well_typed=True, exit={'success': 1}, schedule=('started 0', 'exited 0 success')):
    return {'name': name, 'wellTyped': well_typed, 'straight': True,
            'run': {'exit': exit, 'fibers': [{'id': 0, 'parkedToken': None}], 'schedule': list(schedule)}}


def row(name, host_schedule=('started 0', 'exited 0 success'), sync=True, exit_agree=True, schedule_agree=True, notes=()):
    return {'program': name, 'leanExit': 'success 1', 'hostExit': 'success 1', 'exitAgree': exit_agree,
            'scheduleAgree': schedule_agree, 'runSyncAgree': sync, 'notes': list(notes),
            'host': {'schedule': list(host_schedule)}}


EMITTED = {'source': 'decl', 'inferred': True, 'refusal': None}
AGREE = {'status': 'agree', 'issues': [], 'columns': {}}


class CorpusCheckTests(unittest.TestCase):
    def one(self, name='g1', **kw):
        return check.classify({name: entry(name, **kw.pop('entry', {}))}, kw.pop('emitted', {name: EMITTED}),
                              kw.pop('rows', {name: row(name)}), kw.pop('hung', set()),
                              kw.pop('tsc_errors', {}), kw.pop('observations', {name: AGREE}))[0]

    def test_a_program_without_a_module_is_not_compiler_clean(self):
        r = self.one(emitted={'g1': {'source': None, 'inferred': False, 'refusal': 'internal action setContext'}}, rows={})
        self.assertEqual((r['module'], r['tsc'], r['run']), ('refused', 'not-compiled', 'refused-by-printer'))
        self.assertIn('printer refused', r['note'])
        r = self.one(emitted={}, rows={})
        self.assertEqual((r['module'], r['tsc']), ('refused', 'not-compiled'))

    def test_an_unreported_program_is_not_an_agreement(self):
        r = self.one(rows={})
        self.assertEqual(r['run'], 'not-run')
        self.assertEqual(r['sync'], 'n/a')

    def test_a_synchronous_disagreement_is_a_disagreement(self):
        records = [self.one(rows={'g1': row('g1', sync=False)})]
        self.assertEqual(records[0]['sync'], 'differs')
        self.assertEqual(records[0]['run'], 'agree')
        self.assertEqual(check.disagreements_of(records), [('g1', 'sync', 'differs')])
        fresh = check.render(records)
        code, message = check.judge(fresh, fresh, check.disagreements_of(records), set())
        self.assertEqual(code, 1)
        self.assertIn('g1 sync differs', message)

    def test_a_worsened_schedule_changes_the_row(self):
        notes = ('schedule differ at row 1: Lean "forked 0 1", rc.112 "started 1"',)
        first = self.one(rows={'g1': row('g1', ('started 0', 'started 1', 'exited 1 fail', 'exited 0 success'), schedule_agree=False, notes=notes)})
        worse = self.one(rows={'g1': row('g1', ('started 0', 'started 1', 'exited 0 success'), schedule_agree=False, notes=notes)})
        self.assertEqual(first['run'], 'schedule-differs')
        self.assertEqual(first['note'], worse['note'])
        self.assertNotEqual(first['hostSchedule'], worse['hostSchedule'])
        self.assertNotEqual(check.render([first]), check.render([worse]))
        self.assertEqual(first['hostSchedule'], 'started 0,started 1,exited 1 fail,exited 0 success')

    def test_scheduled_rows_are_dropped_as_the_runner_drops_them(self):
        self.assertEqual(check.compared_schedule(['started 0', 'scheduled 0 0', 'parked 0', 'ran 0']), 'started 0,parked 0,ran 0')

    def test_a_registration_names_program_dimension_and_outcome(self):
        register = ('| program | outcome | why |\n| --- | --- | --- |\n'
                    '| `g1` `g2` | run schedule-differs | DI-75 |\n'
                    '| `g3` | types mismatch-A | DI-76 |\n'
                    '| `g9` | sync differs | DI-73 |\n'
                    'Prose that mentions `g4` registers nothing.\n')
        registered = check.parse_register(register)
        self.assertEqual(registered, {('g1', 'run', 'schedule-differs'), ('g2', 'run', 'schedule-differs'),
                                      ('g3', 'types', 'mismatch-A'), ('g9', 'sync', 'differs')})
        records = [self.one(rows={'g1': row('g1', exit_agree=False, notes=('same kind, values differ',))})]
        self.assertEqual(check.disagreements_of(records), [('g1', 'run', 'differ')])
        fresh = check.render(records)
        code, message = check.judge(fresh, fresh, check.disagreements_of(records), registered)
        self.assertEqual(code, 1)
        self.assertIn('g1 run differ', message)

    def test_a_stale_registration_fails(self):
        records = [self.one()]
        fresh = check.render(records)
        code, message = check.judge(fresh, fresh, [], {('g1', 'run', 'differ')})
        self.assertEqual(code, 1)
        self.assertIn('no longer occur', message)
        code, message = check.judge(fresh, fresh, [], set())
        self.assertEqual(code, 0)

    def test_drift_is_reported_before_the_register(self):
        records = [self.one()]
        fresh = check.render(records)
        code, message = check.judge(fresh, fresh.replace('agree', 'differ', 1), [], set())
        self.assertEqual(code, 1)
        self.assertIn('differs from', message)
        code, message = check.judge(fresh, None, [], set())
        self.assertEqual(code, 1)

    def test_compiler_errors_on_a_well_typed_program_are_a_disagreement(self):
        r = self.one(tsc_errors={'g1': "error TS2345: Argument of type 'boolean' is not assignable"})
        self.assertEqual(r['tsc'], 'errors')
        self.assertIn('tsc: error TS2345', r['note'])
        self.assertEqual(check.disagreements_of([r]), [('g1', 'tsc', 'errors')])
        untyped = self.one(entry={'well_typed': False}, rows={}, tsc_errors={'g1': 'error TS2345: x'}, observations={})
        self.assertEqual((untyped['run'], untyped['types'], untyped['tsc']), ('untyped', 'untyped', 'errors'))
        self.assertEqual(check.disagreements_of([untyped]), [])

    def test_a_refused_type_query_carries_its_reason(self):
        refused = {'status': 'refused', 'columns': {}, 'issues': [
            {'code': 'unresolved-unknown', 'axis': 'A', 'message': 'actual A contains unknown'}]}
        r = self.one(observations={'g1': refused})
        self.assertEqual(r['types'], 'refused')
        self.assertIn('types refused: unresolved-unknown/A', r['note'])
        mismatch = {'status': 'mismatch', 'issues': [], 'columns': {
            'A': {'actualToExpected': True, 'expectedToActual': False, 'agreement': 'mismatch'},
            'E': {'actualToExpected': True, 'expectedToActual': True, 'agreement': 'exact'}}}
        self.assertEqual(self.one(observations={'g1': mismatch})['types'], 'mismatch-A')

    def test_error_containment_is_not_an_extra_mismatching_column(self):
        observation = {'status': 'mismatch', 'issues': [], 'columns': {
            'A': {'actualToExpected': True, 'expectedToActual': False, 'agreement': 'mismatch'},
            'E': {'actualToExpected': True, 'expectedToActual': False, 'agreement': 'strict-containment'}}}
        self.assertEqual(self.one(observations={'g1': observation})['types'], 'mismatch-A')
        observation['status'] = 'agree'
        observation['columns']['A'] = {'actualToExpected': True, 'expectedToActual': True, 'agreement': 'exact'}
        self.assertEqual(self.one(observations={'g1': observation})['types'], 'agree')

    def test_a_killed_process_is_a_hang(self):
        r = self.one(rows={}, hung={'g1'})
        self.assertEqual(r['run'], 'host-hang')
        self.assertIn('killed', r['host'])
        self.assertEqual(check.disagreements_of([r]), [('g1', 'run', 'host-hang')])


if __name__ == '__main__':
    unittest.main()
