#!/usr/bin/env python3
"""Read-only cutover preflight against one Git commit. No source writes."""
import collections
import re
import subprocess
import sys

base = sys.argv[1] if len(sys.argv) > 1 else '01c83fbc0f319999faf9a9ab306137a95f6dd303'
def git(*args):
    return subprocess.check_output(['git', *args], text=True)
paths = git('ls-tree', '-r', '--name-only', base).splitlines()
core = 'src/Effect4/Modules/'
laws = 'src/Effect4/Laws/Modules/'
models = ['Queue', 'Semaphore', 'Pool', 'Latch', 'Stream']
moves = {}
groups = collections.Counter()
for p in paths:
    if not p.endswith('.lean'):
        continue
    if p.startswith(core):
        tail = p[len(core):]
        if tail == 'Step.lean' or tail.startswith('Step/'):
            moves[p] = 'src/Effect4/' + tail
            groups['core-step'] += 1
        else:
            moves[p] = 'src/Effect4/Library/' + tail
            groups['core-library'] += 1
    elif p.startswith(laws):
        tail = p[len(laws):]
        if any(tail == m + '/Model.lean' for m in models):
            moves[p] = 'src/Effect4/Library/' + tail
            groups['core-model'] += 1
        elif any(tail.startswith(m + '/') for m in models):
            moves[p] = 'src/Effect4/Laws/Library/' + tail
            groups['library-laws'] += 1
        else:
            if tail == 'Step.lean':
                target = 'src/Effect4/Laws/Step.lean'
            elif tail.startswith('Step/'):
                target = 'src/Effect4/Laws/' + tail
            else:
                target = 'src/Effect4/Laws/Step/' + tail
            moves[p] = target
            groups['shared-laws'] += 1

def mod(p):
    return p.removeprefix('src/').removeprefix('tools/').removesuffix('.lean').replace('/', '.')
module_moves = {mod(p): mod(q) for p, q in moves.items()}
pattern = re.compile(r'^(?P<prefix>(?:public\s+)?(?:meta\s+)?import\s+)(?P<module>[A-Za-z0-9_.]+)', re.M)
missed = []
refs = []
for p in paths:
    if not p.endswith('.lean') or not p.startswith(('src/', 'tools/', 'Test/')):
        continue
    text = git('show', base + ':' + p)
    for match in pattern.finditer(text):
        if match.group('module') in module_moves and 'meta' in match.group('prefix'):
            missed.append((p, match.group(0)))
    if p in ['Test/Audit/AxiomGate.lean', 'tools/Tools/SemanticsRegistry.lean']:
        for line in text.splitlines():
            for name in re.findall(r'`([A-Za-z0-9_.]+)', line):
                if name in module_moves:
                    refs.append((p, name, module_moves[name]))
print('base', base)
print('move groups', dict(groups), 'total', len(moves))
print('meta import lines missed by import/public-import-only rewrite:', len(missed))
for p, line in missed:
    print(' ', p, ':', line)
print('non-import module references in gate and registry:', len(refs))
for p, old, new in refs:
    print(' ', p, ':', old, '=>', new)
stream = git('show', base + ':' + laws + 'Stream/Model.lean')
print('Stream model theorem declarations:', re.findall(r'^theorem\s+(\S+)', stream, re.M))
assert len(missed) == 12
assert len(refs) == 28
assert len(re.findall(r'^theorem\s+', stream, re.M)) == 3

# Finite controls for the mechanical rewrite.
def rewrite_imports(text):
    return pattern.sub(lambda m: m.group('prefix') + module_moves.get(m.group('module'), m.group('module')), text)
for prefix in ['import ', 'public import ', 'meta import ', 'public meta import ']:
    sample = prefix + 'Effect4.Modules.Step.Elab\n'
    assert rewrite_imports(sample) == prefix + 'Effect4.Step.Elab\n'
    assert rewrite_imports(rewrite_imports(sample)) == rewrite_imports(sample)
negative = 'namespace Effect4.Modules\n#check Effect4.Modules.Step.sound\n'
assert rewrite_imports(negative) == negative
legacy = re.compile(r'^(?:public\s+)?import\s+([A-Za-z0-9_.]+)', re.M)
assert not legacy.search('public meta import Effect4.Modules.Step.Elab\n')
assert not legacy.search('meta import Effect4.Modules.Step.Elab\n')
print('positive controls: four header forms rewrite once, then stay unchanged')
print('negative controls: legacy pattern misses meta headers; declaration references stay unchanged')
