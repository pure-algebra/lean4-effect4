#!/usr/bin/env python3
"""Seat M0's red controls on real data: the lane's comparison over a faulted release result.

    python3 docs/research/2026-10-05-seat-M0/red-controls.py

Run the release lane once first (`make check-truth-release`): this script reads the result
that the lane kept under `.lake/truth-release/release/`. It starts no host and changes no file.
Each control takes the committed manifest, the committed pin result and the kept release
result, breaks the release result in one place, and gives it to `judge_runs`, the function the
lane itself calls (`scripts/check-truth-release.py`). The kept controls of the same rules, on
a small manifest, are in that script's `--self-test`.

Evidence word: tested (finite, on the truth manifest of the tree it runs in).
"""
import copy
import importlib.util
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(root / 'scripts/lib'))
spec = importlib.util.spec_from_file_location('lane', root / 'scripts/check-truth-release.py')
lane = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lane)
import truth_ledger  # noqa: E402

truth = root / 'harness/truth'
kept = root / '.lake/truth-release/release/harness/truth/result.json'
if not kept.is_file():
    sys.exit(f'no kept release result at {kept.relative_to(root)}: run the release lane first')
manifest = json.loads((truth / 'corpus.json').read_text())
on_pin = json.loads((truth / 'result.json').read_text())
on_release = json.loads(kept.read_text())
ledger = (truth / 'build-ledger.tsv').read_text()
pin, release = lane.BUILDS
ran = {report['program'] for report in on_release['rows']}
skipped = [program['name'] for program in manifest['programs'] if program['name'] not in ran]


def judged(release_result, pin_result=on_pin, skip=skipped):
    try:
        findings, _, _ = lane.judge_runs(lane.BUILDS, manifest, {pin: pin_result, release: release_result},
                                         {release: skip}, ledger)
    except truth_ledger.Inconsistent as refusal:
        return [f'(the result is refused) {refusal}']
    return findings


def faulted(name, change):
    result = copy.deepcopy(on_release)
    report = next(r for r in result['rows'] if r['program'] == name)
    change(result, report)
    return result


outcomes = []


def control(title, findings, must, must_not=()):
    ok = any(must in finding for finding in findings) and not any(
        text in finding for finding in findings for text in must_not)
    outcomes.append(ok)
    print(f'--- {title}: {"refused as expected" if ok else "WRONG"}')
    for finding in findings or ['(no finding)']:
        print(f'    FAIL truth-release: {finding}')


unchanged = judged(on_release)
outcomes.append(unchanged == [])
print(f'--- green: the kept release result, unchanged: {"no finding, as expected" if not unchanged else "WRONG"}')
for finding in unchanged:
    print(f'    FAIL truth-release: {finding}')

# The coordinator's first control: a known difference in one field excuses no other field.
schedule = [name for name in ran if truth_ledger.entries_of(
    next(p for p in manifest['programs'] if p['name'] == name),
    next(r for r in on_release['rows'] if r['program'] == name))['schedule'] != truth_ledger.YES]
print(f'programs whose schedule on effect@{release} is a known difference: {", ".join(sorted(schedule))}')
for name in sorted(schedule):
    control(f'{name}: its observed exit is altered, its schedule difference stays',
            judged(faulted(name, lambda result, report: report.update(exitAgree=False, hostExit='success 99'))),
            f'{name}: {release} exit: the ledger says "yes", observed "no: machine',
            must_not=[f'{name}: {release} schedule', f'{name}: {release} sync'])
    control(f'{name}: its observed sync exit is altered, its schedule difference stays',
            judged(faulted(name, lambda result, report: (report.update(runSyncAgree=False),
                                                         report['hostSync'].update(exit={'success': 99})))),
            f'{name}: {release} sync: the ledger says "yes", observed "no: machine',
            must_not=[f'{name}: {release} schedule', f'{name}: {release} exit'])

# The coordinator's second control: a missing observation is neither agreement nor disagreement.
control('pBind: its observation is removed from the release result',
        judged(faulted('pBind', lambda result, report: result['rows'].remove(report))),
        'pBind: the runner reports no result for it')
control('pFork: the field `runSyncAgree` is absent from its result',
        judged(faulted('pFork', lambda result, report: report.pop('runSyncAgree'))),
        f'pFork: {release} sync: the ledger says "yes", observed "n/a"')
control('p42: the field `scheduleAgree` is null in its result',
        judged(faulted('p42', lambda result, report: report.update(scheduleAgree=None))),
        f'p42: {release} schedule: the ledger says "yes", observed "n/a"')
control('pKv: the field `exitAgree` is null in its result',
        judged(faulted('pKv', lambda result, report: report.update(exitAgree=None))),
        f'pKv: {release} exit: the ledger says "yes", observed "n/a"')
pin_without = copy.deepcopy(on_pin)
pin_without['rows'] = [report for report in pin_without['rows'] if report['program'] != 'pGen']
control('pGen: its observation is removed from the committed pin result',
        judged(on_release, pin_without), 'pGen: the runner reports no result for it')
if skipped:
    first = skipped[0]
    control(f'{first}: not run on effect@{release}, and the lane is told that it ran',
            judged(on_release, skip=[name for name in skipped if name != first]),
            f'{first}: the runner reports no result for it')
    as_if_agreeing = copy.deepcopy(on_release)
    as_if_agreeing['rows'].append(dict(next(r for r in on_pin['rows'] if r['program'] == first)))
    control(f'{first}: not run on effect@{release}, and a result for it is slipped in',
            judged(as_if_agreeing), f'{first}: the lane did not select it, and the runner reports it')

print(f'red controls on real data: {sum(outcomes)} of {len(outcomes)} as expected')
sys.exit(0 if all(outcomes) else 1)
