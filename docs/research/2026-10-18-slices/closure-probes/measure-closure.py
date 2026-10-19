#!/usr/bin/env python3
"""C5 measurements over one revision of the tree: duplicate definitions and generated lines.

Usage: measure-closure.py REPO REV
Reads every file with `git show REV:path` (REV may be a commit or WORKTREE for the working tree).
1. Definitions: measure.py's rule (a line `let|let rec|and NAME` at column 0) per generated lane
   unit, and how many of those names `ocaml/gen/api_gen.ml` also defines.
2. Closure manifests: Lean declarations per unit, and those also in api_gen's manifest.
3. Generated lines of the lane outputs (.ml and .mli) and their manifests.
"""
import re
import subprocess
import sys

repo, rev = sys.argv[1], sys.argv[2]


def read(path):
    if rev == 'WORKTREE':
        try:
            return open(f'{repo}/{path}', errors='replace').read()
        except FileNotFoundError:
            return None
    r = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{path}'], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def defs(text):
    out = set()
    for line in text.splitlines():
        m = re.match(r"^(?:let rec|let|and)\s+([a-z_][A-Za-z0-9_']*)", line)
        if m:
            out.add(m.group(1))
    return out


def manifest(text):
    rows = [l.split('\t') for l in text.splitlines() if l and not l.startswith('#')]
    header, body = rows[0], rows[1:]
    i = header.index('lean')
    return {r[i] for r in body}


units = ['ocaml/engine/test/todo/todo_gen', 'ocaml/engine/test/ctors/ctors_gen',
         'ocaml/engine/test/modeled/modeled_gen', 'ocaml/engine/test/rocq/rocq_gen',
         'ocaml/engine/test/lanes/lanes_gen']
api = read('ocaml/gen/api_gen.ml')
base = defs(api)
print(f'== {rev}')
print('-- 1. top-level definitions (measure.py rule) also in ocaml/gen/api_gen.ml')
total_ml = total_mli = 0
for u in units:
    ml, mli = read(u + '.ml'), read(u + '.mli')
    if ml is None:
        print(f'{u}.ml: absent')
        continue
    d = defs(ml)
    n_ml = ml.count('\n')
    n_mli = mli.count('\n') if mli else 0
    total_ml += n_ml
    total_mli += n_mli
    print(f'{u}.ml: {n_ml} lines, {len(d)} definitions, {len(d & base)} also in api_gen.ml; '
          f'.mli {n_mli} lines')
print(f'lane outputs: {total_ml} .ml lines, {total_mli} .mli lines, {total_ml + total_mli} in all')
print('-- 2. closure manifests: Lean declarations, and those also in closure-api_gen.tsv')
api_m = manifest(read('ocaml/gen/closure-api_gen.tsv'))
eng_m = manifest(read('ocaml/gen/closure-api_engine.tsv'))
manifests = {}
for stem in ['todo_gen', 'ctors_gen', 'modeled_gen', 'rocq_gen', 'lanes_gen']:
    t = read(f'ocaml/gen/closure-{stem}.tsv')
    if t is None:
        continue
    manifests[stem] = manifest(t)
    print(f'closure-{stem}.tsv: {len(manifests[stem])} declarations, '
          f'{len(manifests[stem] & api_m)} also in api_gen')
lanes = set().union(*manifests.values())
print(f'all lane closures: {sum(len(m) for m in manifests.values())} rows, '
      f'{len(lanes)} distinct declarations, {len(lanes & api_m)} also in api_gen; '
      f'api_engine shares {len(eng_m & api_m)} of {len(eng_m)} with api_gen')
