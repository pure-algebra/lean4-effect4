#!/usr/bin/env python3
"""Read-only, exact-revision census plus isolated instrumentation source preparation.

No compiler or generator runs. Output files are outside the repository.
The proposed Lean instrumentation and controls must be compiled before relying on them.
"""
import hashlib
import json
import pathlib
import re
import subprocess

REPO = pathlib.Path('/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4')
OUT = pathlib.Path(__file__).resolve().parent
BASE = subprocess.check_output(['git', '-C', str(REPO), 'rev-parse', '8c9be258'], text=True).strip()
FILES = ['src/Effect4/Laws/Machine/Approximation.lean', 'src/Effect4/Laws/Machine/Scheduling.lean']
FAMILIES = ['hops_leaf', 'hops_observers', 'hops_cmd', 'hops_loop', 'queue_hops']

def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args], text=True)

OUT.joinpath('sources').mkdir(exist_ok=True)
OUT.joinpath('instrumented').mkdir(exist_ok=True)
OUT.joinpath('baseline').mkdir(exist_ok=True)
helper = OUT.joinpath('A3Instrumentation.lean').read_text()
helper = helper.replace('import Lean\n', '', 1)
hash_report = OUT.joinpath('HashReport.lean.txt').read_text()

def with_harness(src):
    imports = list(re.finditer(r'^import [^\n]*\n', src, re.M))
    assert imports
    pos = imports[-1].end()
    return src[:pos]+'import Lean\n\n'+helper+'\n'+src[pos:]+hash_report

families, sites, sources = [], [], []
for file in FILES:
    src = git('show', f'{BASE}:{file}')
    OUT.joinpath('sources', pathlib.Path(file).name).write_text(src)
    sources.append({'path': file, 'sha256': hashlib.sha256(src.encode()).hexdigest()})
    spans, replacements = [], []
    for family in FAMILIES:
        pat = rf'^macro "{family}"[^\n]*`\(tactic\| first\n(?P<arms>(?:  \| [^\n]*\n)+)'
        m = re.search(pat, src, re.M)
        if not m:
            continue
        # Every audited arm is one line and the last closes the macro quotation.
        raw = m.group('arms').splitlines()
        assert raw[-1].endswith(')'), (family, raw)
        raw[-1] = raw[-1][:-1]
        arms = [line.removeprefix('  | ') for line in raw]
        assert len(arms) in (2, 6)
        start = src.count('\n', 0, m.start()) + 1
        end = src.count('\n', 0, m.end())
        spans.append((start, end, family))
        families.append({'family': family, 'path': file, 'line': start,
                         'arms': [{'index': i, 'text': arm, 'line': start+i}
                                  for i, arm in enumerate(arms, 1)]})
        newarms = []
        for i, arm in enumerate(arms, 1):
            label = arm.removeprefix('exact ').split()[0]
            newarms.append(f'  | a3_arm "{family}" / "{i}:{label}" => {arm}')
        replacements.append((m.start('arms'), m.end('arms'), '\n'.join(newarms)+')\n'))
    declaration = None
    for n, line in enumerate(src.splitlines(), 1):
        dm = re.match(r'(?:private |protected )?(?:theorem|def|macro)\s+(\S+)', line)
        if dm:
            declaration = dm.group(1)
        for family in FAMILIES:
            if re.search(rf'\b{family}\b', line):
                owning = next((f for lo, hi, f in spans if lo <= n <= hi), None)
                kind = 'definition' if line.startswith(f'macro "{family}"') else ('nested-arm' if owning else 'proof-site')
                sites.append({'path': file, 'line': n, 'family': family, 'kind': kind,
                              'declaration': declaration, 'ownerMacro': owning, 'text': line.strip()})
    prepared = src
    for begin, end, replacement in sorted(replacements, reverse=True):
        prepared = prepared[:begin]+replacement+prepared[end:]
    # The same logger and hash report occur in both copies; only the 22 arm wrappers differ.
    OUT.joinpath('baseline', pathlib.Path(file).name).write_text(with_harness(src))
    OUT.joinpath('instrumented', pathlib.Path(file).name).write_text(with_harness(prepared))

matches = git('grep', '-n', '-w', *sum((['-e', f] for f in FAMILIES), []), BASE, '--', 'src', 'tools', 'Test')
OUT.joinpath('all-sites.git-grep.txt').write_text(matches)
assert len(matches.splitlines()) == len(sites), 'A call outside the two audited files requires manual review'
report = {'base': BASE, 'sources': sources, 'families': families, 'sites': sites,
          'counts': {'families': len(families), 'directArms': sum(len(x['arms']) for x in families),
                     **{kind: sum(s['kind'] == kind for s in sites) for kind in ['definition', 'nested-arm', 'proof-site']}},
          'dynamicCounts': None, 'compilerRun': False}
OUT.joinpath('census.json').write_text(json.dumps(report, indent=2)+'\n')
lines = ['# A3 static arm and site census', '', f'Base: `{BASE}`. No Lean compiler run.', '',
         '| Family | Definition | Direct arms, in order | Proof sites | Nested callers |',
         '| --- | --- | --- | --- | --- |']
for f in families:
    proof = [f"{pathlib.Path(s['path']).name}:{s['line']} ({s['declaration']})" for s in sites if s['family'] == f['family'] and s['kind'] == 'proof-site']
    nested = [f"{s['ownerMacro']}:{s['line']}" for s in sites if s['family'] == f['family'] and s['kind'] == 'nested-arm']
    lines.append('| '+ ' | '.join([f['family'], f"{pathlib.Path(f['path']).name}:{f['line']}", '<br>'.join(a['text'] for a in f['arms']), '<br>'.join(proof) or 'none', '<br>'.join(nested) or 'none'])+' |')
lines += ['', 'Counts: '+json.dumps(report['counts'])+'. These are source occurrences, not runtime selections.']
OUT.joinpath('table.md').write_text('\n'.join(lines)+'\n')
print(json.dumps({'base': BASE, 'counts': report['counts'], 'dynamicCounts': None, 'compilerRun': False}, indent=2))
