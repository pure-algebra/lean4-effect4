#!/usr/bin/env python3
"""D1 measurements: the LCNF family's generated lines, its repeated definitions, and its compile CPU.

Usage:
  measure-scopes.py lines REPO REV   REV is a commit, or WORKTREE for the working tree
  measure-scopes.py cpu CHROME_JSON  a cold build's trace, from `dune trace cat --chrome-trace`

`lines` reads every generated file of the family with `git show REV:path` and prints, per unit,
its .ml and .mli lines and its top-level definitions (measure.py's rule: a line `let`, `let rec`
or `and NAME` at column 0). The closure is ocaml/gen/closure_gen.ml when REV has it, else
ocaml/gen/api_gen.ml. It prints how many of the lanes' definitions the closure also defines, and
how many manifest rows each unit compiles (the `unit` column; before D1, one unit per manifest).

`cpu` sums each compiler run's user and system CPU by unit, as closure-probes/trace-cpu.py does,
with the closure unit added. Only process names, arguments and rusage are read.

The cold build, at each revision (D = an empty scratch directory):
  git archive REV ocaml | tar -x -C D
  cd D/ocaml && opam exec --switch=effect4 -- dune build --cache=disabled --trace-file T
  opam exec --switch=effect4 -- dune trace cat --chrome-trace --trace-file T > C
  python3 measure-scopes.py cpu C
Delete T and C afterwards: a dune trace records the environment of the run.
Evidence: finite counts of committed files (lines); host-only CPU on a shared machine (cpu).
"""
import ast
import json
import re
import subprocess
import sys

GENERATED = ['ocaml/gen/closure_gen', 'ocaml/gen/api_gen', 'ocaml/engine/test/lanes/lanes_gen',
             'ocaml/engine/test/todo/todo_gen', 'ocaml/engine/test/ctors/ctors_gen',
             'ocaml/engine/test/modeled/modeled_gen', 'ocaml/engine/test/rocq/rocq_gen',
             'ocaml/gen/facade/effect4']
MANIFESTS = ['ocaml/gen/closure-api_gen.tsv', 'ocaml/gen/closure-lanes_gen.tsv']
UNITS = ['closure_gen', 'api_gen', 'lanes_gen', 'todo_gen', 'ctors_gen', 'modeled_gen', 'rocq_gen',
         'effect4', 'api_engine']


def read(repo, rev, path):
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


def lines(repo, rev):
    texts = {u: (read(repo, rev, u + '.ml'), read(repo, rev, u + '.mli')) for u in GENERATED}
    closure = 'ocaml/gen/closure_gen' if texts['ocaml/gen/closure_gen'][0] else 'ocaml/gen/api_gen'
    base = defs(texts[closure][0])
    print(f'== {rev}: the closure is {closure}.ml')
    total_ml = total_mli = 0
    for u in GENERATED:
        ml, mli = texts[u]
        if ml is None:
            continue
        n_ml, n_mli = ml.count('\n'), (mli.count('\n') if mli else 0)
        total_ml += n_ml
        total_mli += n_mli
        d = defs(ml)
        also = '' if u == closure else f', {len(d & base)} also in {closure.split("/")[-1]}.ml'
        print(f'{u}: .ml {n_ml} lines, .mli {n_mli} lines, {len(d)} definitions{also}')
    print(f'the family: {total_ml} .ml lines, {total_mli} .mli lines, {total_ml + total_mli} in all')
    for path in MANIFESTS:
        t = read(repo, rev, path)
        if t is None:
            continue
        rows = [l.split('\t') for l in t.splitlines() if l and not l.startswith('#')]
        header, body = rows[0], rows[1:]
        if 'unit' in header:
            i = header.index('unit')
            counts = {}
            for r in body:
                counts[r[i]] = counts.get(r[i], 0) + 1
            per = ', '.join(f'{v} in {k}' for k, v in sorted(counts.items()))
        else:
            per = 'one unit'
        lean = {r[header.index('lean')] for r in body}
        print(f'{path}: {len(body)} rows, {len(lean)} distinct declarations; compiled: {per}')


def cpu(chrome):
    trace = json.load(open(chrome))
    events = trace if isinstance(trace, list) else trace.get('traceEvents', [])
    total = 0
    by_unit = {u: 0 for u in UNITS}
    count = {u: 0 for u in UNITS}
    processes = 0
    for e in events:
        if e.get('cat') != 'process' or e.get('ph') != 'X':
            continue
        processes += 1
        args = e.get('args', {})
        usage = args.get('rusage')
        if not usage:
            continue
        r = ast.literal_eval(usage) if isinstance(usage, str) else usage
        used = r['user_cpu_time'] + r['system_cpu_time']
        total += used
        if not re.search(r'ocaml(c|opt)(\.opt)?$', args.get('prog', '')):
            continue
        words = args.get('process_args', [])
        words = ast.literal_eval(words) if isinstance(words, str) else words
        for u in UNITS:
            if any(re.search(rf'(^|/){u}\.mli?$', w) for w in words):
                by_unit[u] += used
                count[u] += 1
                break
    print(f'whole build: {total / 1e9:.1f} s CPU over {processes} processes')
    for u in UNITS:
        if count[u]:
            print(f'{u}: {by_unit[u] / 1e9:.2f} s CPU in {count[u]} compiler runs')
    gen = ['closure_gen', 'api_gen', 'effect4']
    lanes = ['lanes_gen', 'todo_gen', 'ctors_gen', 'modeled_gen', 'rocq_gen']
    print(f'ocaml/gen\'s generated units: {sum(by_unit[u] for u in gen) / 1e9:.2f} s; '
          f'the lanes\' generated units: {sum(by_unit[u] for u in lanes) / 1e9:.2f} s; '
          f'together: {sum(by_unit[u] for u in gen + lanes) / 1e9:.2f} s CPU')


if __name__ == '__main__':
    if len(sys.argv) == 4 and sys.argv[1] == 'lines':
        lines(sys.argv[2], sys.argv[3])
    elif len(sys.argv) == 3 and sys.argv[1] == 'cpu':
        cpu(sys.argv[2])
    else:
        sys.exit(__doc__)
