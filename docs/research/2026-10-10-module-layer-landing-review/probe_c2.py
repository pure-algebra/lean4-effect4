#!/usr/bin/env python3
"""Finite C2 controls against committed inputs; all candidate edits stay in memory."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import subprocess

REVIEWED = '235403a03b8843d4b86cb05759df4090a9d9bdb1'
PRIMARY = '1c98dd94831c060e591cd7e5bef19d6528c5d22a'
SOURCE = 'scripts/lib/conservativity.py'
TEXT_TAGS = 'ocaml/goldens/eff/wire-tags.txt'
HERE = Path(__file__).resolve().parent
inputs = {}


def read(rev, path):
    resolved = subprocess.check_output(
        ['git', 'rev-parse', '--verify', rev + '^{commit}'], text=True).strip()
    raw = subprocess.check_output(['git', 'show', resolved + ':' + path])
    inputs[resolved + ':' + path] = hashlib.sha256(raw).hexdigest()
    return raw.decode('utf-8')


class Side:
    def __init__(self, data):
        self.data = data

    def read(self, path):
        return self.data.get(path)


source = read(REVIEWED, SOURCE)
assert source == read(PRIMARY, SOURCE)
old = 'if y is not None and item_name(x) == item_name(y) and (fam, item_name(x)) in retyped:'
new = "if path != 'ocaml/goldens/eff/wire-tags.txt' and y is not None and item_name(x) == item_name(y) and (fam, item_name(x)) in retyped:"
assert source.count(old) == 1
results = []
for mode in ['landed', 'minimal repair']:
    code = source if mode == 'landed' else source.replace(old, new)
    ns = {'__name__': 'review_probe', '__file__': SOURCE}
    exec(compile(code, mode, 'exec'), ns)
    paths = [ns['WIRE_TAGS']] + ns['MANIFESTS']
    base = {path: read(REVIEWED + '^', path) for path in paths}
    cand = {path: read(REVIEWED, path) for path in paths}
    policy = json.loads(read(REVIEWED, ns['POLICY']))

    def check(label, before, after, pol, expected):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            got = ns['c2'](Side(before), Side(after), pol)
        result = {'mode': mode, 'case': label, 'expected': expected,
                  'actual': got, 'output': output.getvalue()}
        results.append(result)
        print(f'{mode} | {label} | {"PASS" if got else "REFUSE"}')
        assert got == expected, result

    check('ordinary defs retyping', base, cand, policy, True)
    pol = dict(policy)
    pol['constructor_retypings'] = []
    check('policy removal', base, cand, pol, False)

    altered = dict(cand)
    tags = json.loads(altered[ns['WIRE_TAGS']])
    assert tags['families']['Effect4.Program.Eff']['active']['defs'] == 30
    tags['families']['Effect4.Program.Eff']['active']['defs'] = 99
    altered[ns['WIRE_TAGS']] = json.dumps(tags)
    check('JSON tag 30 -> 99', base, altered, policy, False)

    altered = dict(cand)
    assert altered[TEXT_TAGS].count('defs=30') == 1
    altered[TEXT_TAGS] = altered[TEXT_TAGS].replace('defs=30', 'defs=99')
    check('text tag 30 -> 99', base, altered, policy, mode == 'landed')
    check('text tag change after landing', cand, altered, policy, mode == 'landed')

    for case in json.loads(read(REVIEWED, ns['MUTATIONS'])):
        if not case['name'].startswith(('G6', 'R4')):
            continue
        altered = dict(cand)
        pol = policy
        for edit in case['edits']:
            path = edit['path']
            text = read(REVIEWED, path)
            assert text.count(edit['old']) == 1
            text = text.replace(edit['old'], edit['new'])
            if path == ns['POLICY']:
                pol = json.loads(text)
            else:
                altered[path] = text
        check(case['name'], cand, altered, pol, case['expect'] == 'PASS')

import difflib
patch = ''.join(difflib.unified_diff(source.splitlines(keepends=True),
    source.replace(old, new).splitlines(keepends=True),
    fromfile='a/' + SOURCE, tofile='b/' + SOURCE))
(HERE / 'repair.patch').write_text(patch)
(HERE / 'inputs.json').write_text(json.dumps(inputs, indent=2, sort_keys=True) + '\n')
(HERE / 'results.json').write_text(json.dumps({
    'reviewed_commit': REVIEWED, 'primary_head': PRIMARY,
    'source_unchanged_at_primary_head': True,
    'scope': 'C2 only; no other compatibility clause, generator, build, runtime or behavior gate',
    'checks': len(results), 'matched_expected': all(x['actual'] == x['expected'] for x in results),
    'results': results}, indent=2) + '\n')
print(f'{len(results)} finite controls matched their expected results.')
