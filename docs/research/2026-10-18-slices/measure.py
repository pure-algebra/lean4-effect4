#!/usr/bin/env python3
"""The burden baseline of the slices plan (README.md §1), measured from the tree.

Run from the repository root: `python3 docs/research/2026-10-18-slices/measure.py`.
It reads files only; it builds nothing. Rerun it after each wave and compare.
"""
import os
import re
import subprocess

ROOT = subprocess.run(['git', 'rev-parse', '--show-toplevel'], capture_output=True,
                      text=True).stdout.strip()
OC = os.path.join(ROOT, 'ocaml')


def read(p):
    with open(os.path.join(ROOT, p), errors='replace') as f:
        return f.read()


def lines(p):
    full = os.path.join(ROOT, p)
    return read(p).count('\n') if os.path.exists(full) else 0


def defs(p):
    out = set()
    for line in read(p).splitlines():
        m = re.match(r"^(?:let rec|let|and)\s+([a-z_][A-Za-z0-9_']*)", line)
        if m:
            out.add(m.group(1))
    return out


print('== 1. OCaml lines, hand and generated (a GENERATED mark in the first 2,000 bytes)')
hand = gen = 0
for dp, _, fs in os.walk(OC):
    if '_build' in dp:
        continue
    for f in fs:
        if f.endswith(('.ml', '.mli')):
            text = open(os.path.join(dp, f), errors='replace').read()
            n = text.count('\n')
            if 'GENERATED' in text[:2000]:
                gen += n
            else:
                hand += n
print(f'hand {hand}  generated {gen}')

print('== 2. Hand OCaml that restates a Lean fact (second owners)')
twins = [
    ('carrier JSON, twin of ShapeDoc.print/read', 'ocaml/engine/kit/kit_json.ml'),
    ('JSON text renderer', 'ocaml/eff/eff_json_text.ml'),
    ('authoring wrappers, twin of Effect4.Program.Authoring', 'ocaml/engine/kit/kit_author.ml'),
    ('their interface', 'ocaml/engine/kit/kit_author.mli'),
    ('host module type REPO and its adapter, of the file', 'ocaml/engine/test/todo/native_todo.ml'),
    ('the kit commands check/run/explore beside the tool', 'ocaml/engine/kit/kit_serve.ml'),
    ('list twins of the engine carriers (Ref instance)', None),
]
total = 0
for what, p in twins:
    if p and p.endswith('native_todo.ml'):
        text = read(p).splitlines()
        start = next(i for i, l in enumerate(text) if l.startswith('module type REPO'))
        adapter = next(i for i, l in enumerate(text) if l.startswith('let host'))
        end = next(i for i in range(adapter, len(text)) if not text[i].strip())
        n = end - start
        total += n
        print(f'{n:6d}  {p}  ({what}: {n} of {len(text)} lines)')
        continue
    if p is None:
        twin_dirs = ['engine', 'engine/test/reference']
        n = sum(lines(os.path.join('ocaml', d, f)) for d in twin_dirs if os.path.isdir(os.path.join(OC, d))
                for f in os.listdir(os.path.join(OC, d)) if f.endswith('_list.ml'))
        p = 'ocaml/engine/{,test/reference/}e4_*_list.ml'
    elif not os.path.exists(os.path.join(ROOT, p)):
        print(f'{0:6d}  {p}  ({what}: deleted)')
        continue
    else:
        n = lines(p)
    total += n
    print(f'{n:6d}  {p}  ({what})')
print(f'{total:6d}  total')

print('== 3. Generated closures that repeat api_gen.ml')
base = defs('ocaml/gen/api_gen.ml')
for p in ['ocaml/engine/test/lanes/lanes_gen.ml', 'ocaml/engine/test/todo/todo_gen.ml',
          'ocaml/engine/test/modeled/modeled_gen.ml', 'ocaml/engine/test/ctors/ctors_gen.ml',
          'ocaml/engine/test/rocq/rocq_gen.ml']:
    if not os.path.exists(os.path.join(ROOT, p)):
        continue
    d = defs(p)
    print(f'{p}: {lines(p)} lines, {len(d)} top-level definitions, {len(d & base)} also in api_gen.ml')

print('== 4. Packaging')
opams = [os.path.join(dp, f) for dp, _, fs in os.walk(OC) if '_build' not in dp
         for f in fs if f.endswith('.opam')]
pub = subprocess.run(['grep', '-rn', 'public_name', OC, '--include=dune'], capture_output=True,
                     text=True).stdout
pub = [l for l in pub.splitlines() if '_build' not in l]
print(f'.opam files {len(opams)}; public_name stanzas {len(pub)}')
for l in pub:
    print('  ' + l.replace(ROOT + '/', ''))

print('== 5. Hand library modules with no .mli (rule 5)')
missing = []
for d in ['eff', 'gen', 'lcnf', 'clock', 'engine', 'engine/bytes', 'engine/cas', 'engine/kit']:
    for f in sorted(os.listdir(os.path.join(OC, d))):
        if f.endswith('.ml') and not os.path.exists(os.path.join(OC, d, f[:-3] + '.mli')):
            text = open(os.path.join(OC, d, f), errors='replace').read()
            if 'GENERATED' not in text[:2000]:
                missing.append(f'{d}/{f}')
print(f'{len(missing)}: ' + ' '.join(missing))

print('== 6. One fact, several owners, in Lean')
copy = 'Test/fixtures/session/requests.jsonl'
if os.path.exists(os.path.join(ROOT, copy)):
    same = read('ocaml/engine/test/kit/tool-requests.jsonl') == read(copy)
    print(f'tool-requests.jsonl is a byte copy of {copy}: {same}')
else:
    print(f'the session fixture is one file: {copy} is gone (C1)')
for name, pat, path in [
        ('wire method names', r'def (Request\.method|supportedMethods|descriptions)\b', 'src/Effect4/Tool'),
        ('journal replays with their own append law',
         r'theorem (replayCursor_snoc|replayState_snoc|transcript_replays|journal_replays|load_own)\b',
         'src/Effect4')]:
    out = subprocess.run(['grep', '-rEn', pat, os.path.join(ROOT, path)], capture_output=True,
                         text=True).stdout.strip().splitlines()
    print(f'{name}: {len(out)}')
    for l in out:
        print('  ' + l.replace(ROOT + '/', '').split(':')[0] + ': ' + re.search(pat, l).group(1))
refusals = subprocess.run(['grep', '-rEn', r'^inductive [A-Za-z]*(Refusal|Reason)\b',
                           os.path.join(ROOT, 'src/Effect4')], capture_output=True,
                          text=True).stdout.strip().splitlines()
print(f'refusal and reason types under src/Effect4: {len(refusals)}')

print('== 7. Agent-facing facts read from source')
methods = read('src/Effect4/Tool/Methods.lean')
mcp = read('ocaml/engine/kit/kit_mcp.ml')
print(f'"annotations" in Tool/Methods.lean or kit_mcp.ml: {("annotations" in methods) or ("annotations" in mcp)}')
print(f'"outputSchema" in Tool/Methods.lean or kit_mcp.ml: {("outputSchema" in methods) or ("outputSchema" in mcp)}')
codec = read('src/Effect4/Tool/CodecProfile.lean')
m = re.search(r'inductive Refusal where(.*?)\n\n', codec, re.S)
print('CodecProfile.Refusal: ' + ' '.join(x.strip() for x in m.group(1).splitlines() if x.strip()))
goals = subprocess.run(['grep', '-rEn', r'^\s*(@\[[^]]*\]\s*)?proof_goal [A-Za-z]', os.path.join(ROOT, 'src')],
                       capture_output=True, text=True).stdout.strip().splitlines()
print(f'planned goals in src: {len(goals)}')
for g in goals:
    print('  ' + g.replace(ROOT + '/', '').split(':')[0] + ': ' + re.search(r'proof_goal (\S+)', g).group(1))
