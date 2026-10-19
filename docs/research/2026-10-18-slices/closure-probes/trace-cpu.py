#!/usr/bin/env python3
"""CPU of a cold dune build by generated unit, from `dune trace cat --chrome-trace` output.

Usage: trace-cpu.py CHROME_JSON
Every finished process carries its rusage (user and system CPU, in nanoseconds). A compiler run
belongs to a unit when one of its arguments is that unit's .ml or .mli. The report gives each
unit's compile CPU (ocamlc and ocamlopt, implementation and interface) and the whole build's.
Only process names, arguments and rusage are read; the environment is never printed.

The cold build, run for C5's receipt at the base and at the head (D = a scratch directory):
  git archive REV ocaml | tar -x -C D
  cd D/ocaml && opam exec --switch=effect4 -- dune build --cache=disabled --trace-file T
  opam exec --switch=effect4 -- dune trace cat --chrome-trace --trace-file T > C
  python3 trace-cpu.py C
Delete T and C afterwards: a dune trace records the environment of the run.
"""
import ast
import json
import re
import sys

UNITS = ['api_gen', 'api_engine', 'todo_gen', 'ctors_gen', 'modeled_gen', 'rocq_gen',
         'lanes_gen', 'effect4']
trace = json.load(open(sys.argv[1]))
events = trace if isinstance(trace, list) else trace.get('traceEvents', [])
total = 0
by_unit = {u: 0 for u in UNITS}
count = {u: 0 for u in UNITS}
for e in events:
    if e.get('cat') != 'process' or e.get('ph') != 'X':
        continue
    args = e.get('args', {})
    usage = args.get('rusage')
    if not usage:
        continue
    r = ast.literal_eval(usage) if isinstance(usage, str) else usage
    cpu = r['user_cpu_time'] + r['system_cpu_time']
    total += cpu
    prog = args.get('prog', '')
    if not re.search(r'ocaml(c|opt)(\.opt)?$', prog):
        continue
    words = args.get('process_args', [])
    words = ast.literal_eval(words) if isinstance(words, str) else words
    for u in UNITS:
        if any(re.search(rf'(^|/){u}\.mli?$', w) for w in words):
            by_unit[u] += cpu
            count[u] += 1
            break
print(f'whole build: {total / 1e9:.1f} s CPU over {sum(1 for e in events if e.get("cat") == "process" and e.get("ph") == "X")} processes')
for u in UNITS:
    if count[u]:
        print(f'{u}: {by_unit[u] / 1e9:.2f} s CPU in {count[u]} compiler runs')
lanes = ['todo_gen', 'ctors_gen', 'modeled_gen', 'rocq_gen', 'lanes_gen']
print(f'the lanes\' generated units: {sum(by_unit[u] for u in lanes) / 1e9:.2f} s CPU')
