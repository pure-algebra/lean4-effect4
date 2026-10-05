from pathlib import Path
import importlib.util, json, sys
sys.dont_write_bytecode = True
root = Path('/Users/pooks/Dev/lean4-effect4')
spec = importlib.util.spec_from_file_location('truth_ledger', root / 'scripts/lib/truth_ledger.py')
ledger = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ledger)
builds = ('4.0.0-rc.112', '4.0.1')
line = {'entries': {(b,f): ledger.YES for b in builds for f in ledger.FIELDS}, 'reason': 'scope link changes the schedule', 'slice': 'M2 scopes'}
line['entries'][(builds[0], 'schedule')] = 'no: machine adds a parent link event'
lines = {'fixture': line}
observed = {b: {'fixture': {f: line['entries'][(b,f)] for f in ledger.FIELDS}} for b in builds}
checks = []
def add(name, ok):
    assert ok, name
    checks.append({'name': name, 'passed': True})
add('known schedule difference leaves independent exit and sync expectations', not ledger.judge(builds, ['fixture'], lines, ['fixture'], observed))
for b,f in ((builds[0],'exit'), (builds[0],'sync'), (builds[1],'exit'), (builds[1],'schedule')):
    changed = json.loads(json.dumps(observed))
    changed[b]['fixture'][f] = 'no: changed observation'
    findings = ledger.judge(builds, ['fixture'], lines, ['fixture'], changed)
    add('changed '+b+' '+f+' refused', len(findings) == 1 and f in findings[0])
add('same judge supports pinned observations alone', not ledger.judge(builds, ['fixture'], lines, ['fixture'], {builds[0]: observed[builds[0]]}))
changed = json.loads(json.dumps(observed))
changed[builds[1]]['fixture']['exit'] = 'not-run'
add('missing run does not satisfy agreement', bool(ledger.judge(builds, ['fixture'], lines, ['fixture'], changed)))
print(json.dumps({'kind':'isolated Python validator controls; no runtime comparison','python':sys.version,'checks':checks}, indent=2))
