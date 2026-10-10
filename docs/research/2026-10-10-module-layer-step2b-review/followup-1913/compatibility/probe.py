import contextlib, hashlib, io, json, subprocess
from pathlib import Path
ROOT = Path('/Users/pooks/Dev/lean4-effect4-wt/module-layers')
OUT = Path('/private/tmp/ml2-c2-followup-audit')
BASE = '1c98dd94831c060e591cd7e5bef19d6528c5d22a'
PRE = subprocess.check_output(['git', '-C', str(ROOT), 'rev-parse', '235403a03b8843d4b86cb05759df4090a9d9bdb1^'], text=True).strip()
inputs = {}
def read(rev, path):
    raw = subprocess.check_output(['git', '-C', str(ROOT), 'show', rev + ':' + path]) if rev else (ROOT / path).read_bytes()
    inputs[(rev or 'working-tree') + ':' + path] = hashlib.sha256(raw).hexdigest()
    return raw.decode()
SOURCE = 'scripts/lib/conservativity.py'
current = read(None, SOURCE)
original = read(BASE, SOURCE)
ns = {'__name__': 'review_probe', '__file__': str(ROOT / SOURCE)}
exec(compile(current, SOURCE, 'exec'), ns)
paths = [ns['WIRE_TAGS'], ns['POLICY']] + ns['MANIFESTS']
old_inputs = {p: read(PRE, p) for p in paths}
head_inputs = {p: read(BASE, p) for p in paths}
work_inputs = {p: read(None, p) for p in paths}
assert head_inputs == work_inputs
policy = json.loads(head_inputs[ns['POLICY']])
mutations = json.loads(read(None, ns['MUTATIONS']))
class Side:
    def __init__(self, data): self.data = data
    def read(self, path): return self.data.get(path)
results = []
def check(mode, scope, label, code_ns, before, after, pol, expected):
    output = io.StringIO()
    with contextlib.redirect_stdout(output): got = code_ns['c2'](Side(before), Side(after), pol)
    row = {'mode': mode, 'scope': scope, 'case': label, 'expected': expected, 'actual': got, 'output': output.getvalue()}
    results.append(row)
    print(f'{mode} | {scope} | {label} | {"PASS" if got else "REFUSE"}')
    assert got == expected, row
for mode, code in [('original at base', original), ('current working repair', current)]:
    code_ns = {'__name__': 'review_probe', '__file__': str(ROOT / SOURCE)}
    exec(compile(code, SOURCE, 'exec'), code_ns)
    check(mode, 'well-formed', 'unchanged baseline', code_ns, head_inputs, head_inputs, policy, True)
    check(mode, 'well-formed', 'authorized defs field addition', code_ns, old_inputs, head_inputs, policy, True)
    pol = dict(policy); pol['constructor_retypings'] = []
    check(mode, 'well-formed', 'same field addition without policy name', code_ns, old_inputs, head_inputs, pol, False)
    changed = dict(head_inputs)
    tags = json.loads(changed[ns['WIRE_TAGS']])
    assert tags['families']['Effect4.Program.Eff']['active']['defs'] == 30
    tags['families']['Effect4.Program.Eff']['active']['defs'] = 99
    changed[ns['WIRE_TAGS']] = json.dumps(tags)
    check(mode, 'well-formed', 'JSON numeric tag 30 to 99', code_ns, head_inputs, changed, policy, False)
    changed = dict(head_inputs)
    assert changed[ns['TAG_MANIFEST']].count('defs=30') == 1
    changed[ns['TAG_MANIFEST']] = changed[ns['TAG_MANIFEST']].replace('defs=30', 'defs=99')
    check(mode, 'well-formed', 'text tag change during field addition', code_ns, old_inputs, changed, policy, mode == 'original at base')
    check(mode, 'well-formed', 'text tag change after field addition', code_ns, head_inputs, changed, policy, mode == 'original at base')
    for case in mutations:
        if not case['name'].startswith(('R4 ', 'G6 ')): continue
        changed = dict(head_inputs)
        for edit in case['edits']:
            path = edit['path']; text = changed[path]
            assert text.count(edit['old']) == 1
            changed[path] = text.replace(edit['old'], edit['new'])
        check(mode, 'well-formed', case['name'], code_ns, head_inputs, changed, json.loads(changed[ns['POLICY']]), case['expect'] == 'PASS')
    for label, old, new in [('named constructor moves', 'defs=30 invoke=31', 'invoke=31 defs=30'), ('named constructor renamed', 'defs=30', 'renamed=30'), ('named constructor removed', ' defs=30', '')]:
        changed = dict(head_inputs)
        assert changed[ns['TAG_MANIFEST']].count(old) == 1
        changed[ns['TAG_MANIFEST']] = changed[ns['TAG_MANIFEST']].replace(old, new)
        check(mode, 'well-formed', label, code_ns, head_inputs, changed, policy, False)
    changed = dict(head_inputs)
    good = next(x for x in changed[ns['TAG_MANIFEST']].splitlines() if x.startswith('Eff:'))
    bad = good.replace('defs=30', 'defs=99')
    changed[ns['TAG_MANIFEST']] = changed[ns['TAG_MANIFEST']].replace(good, bad + '\n' + good)
    check(mode, 'malformed duplicate-family control', 'bad Eff line followed by original Eff line', code_ns, head_inputs, changed, policy, True)
(OUT / 'results.json').write_text(json.dumps({'base': BASE, 'pre_landing': PRE, 'scope': 'Finite C2 calls only; candidate edits in memory; no producer, Lean build, behavior gate, or axiom audit', 'results': results}, indent=2) + '\n')
(OUT / 'inputs.json').write_text(json.dumps(inputs, indent=2, sort_keys=True) + '\n')
print(f'{len(results)} finite controls matched expected.')
