#!/usr/bin/env python3
"""Probe U, question 1: the exhaustive gate's `Ty` rows split by where they sit.

    python3 U/scripts/gate-join.py            (reads U/logs/census.log; prints the split)

A row is a `fold_of` connector (`….hom`), a match in a generated module (`Fold`, `TyView`,
`Derived/Program`), or a hand match; hand rows are grouped by definition, and a definition is
counted as compile-forced when one of its matches has no catch-all.
"""
import collections, os

U = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GENERATED = {'Effect4.Program.Fold', 'Effect4.Laws.Program.TyView',
             'Effect4.Store.Domain.Derived.Program'}

rows, mode = [], None
for line in open(os.path.join(U, 'logs', 'census.log')).read().splitlines():
    if line.startswith('#exhaustive_gate'):
        mode = 'g'; continue
    if line.startswith('#traversal_census'):
        mode = 'c'; continue
    if mode == 'g' and line.startswith('  '):
        rows.append(line.strip().split('\t'))

homs = [r for r in rows if r[0].endswith('.hom')]
gen = [r for r in rows if r[1] in GENERATED and not r[0].endswith('.hom')]
hand = [r for r in rows if not r[0].endswith('.hom') and r[1] not in GENERATED]
print(f'gate rows {len(rows)}: no catch-all {sum(r[5] == "catchAll false" for r in rows)}, '
      f'catch-all {sum(r[5] == "catchAll true" for r in rows)}')
print(f'fold_of .hom rows {len(homs)} | generated-module rows {len(gen)} | hand rows {len(hand)}')
defs = collections.OrderedDict()
for r in hand:
    defs.setdefault(r[0].split(' [')[0], []).append(r[5])
forced = [d for d, v in defs.items() if 'catchAll false' in v]
review = [d for d, v in defs.items() if 'catchAll false' not in v]
print(f'hand definitions {len(defs)} | with a match with no catch-all (compile-forced) {len(forced)} '
      f'| with catch-alls only (review) {len(review)}')
print('compile-forced:', ', '.join(d.split('.')[-1] for d in forced))
print('review:', ', '.join(d.split('.')[-1] for d in review))
