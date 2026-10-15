"""Which of the engine's generated types reach a carrier parameter, and does the program reach one.

    python3 docs/research/2026-10-15-lowering-state/probes/program-closure.py

Reads the one recursive type group of `ocaml/engine/api_engine.ml`. A type names a carrier when
its body says `X.t` for a one-letter module `X`. A type reaches a carrier when it names one or
names a type that does. Prints the closure of `node` and the carrier types in it.
"""
import re
L = open('ocaml/engine/api_engine.ml').read().split('\n')
heads = [i for i, l in enumerate(L[:1200]) if re.match(r'^(type|and) ', l)]
decl = {}
for a, b in zip(heads, heads[1:] + [heads[-1] + 1]):
    m = re.match(r"^(?:type|and)\s+(?:\([^)]*\)\s+|'\w+\s+)?(\w+)", L[a])
    decl[m.group(1)] = '\n'.join(L[a:b])
names = set(decl)
def refs(body):
    body = re.sub(r"^(?:type|and)\s+(?:\([^)]*\)\s+|'\w+\s+)?\w+\s*=", '', body, count=1)
    body = re.sub(r'\b\w+\s*:(?!:)', ' ', body)  # record labels are not type names
    return {w for w in re.findall(r'\b[a-z_][a-z0-9_]*\b', body) if w in names}
deps = {n: refs(b) for n, b in decl.items()}
direct = {n for n, b in decl.items() if re.search(r'\b[A-Z]\.t\b', b)}
taint, changed = set(direct), True
while changed:
    changed = False
    for n in names:
        if n not in taint and deps[n] & taint:
            taint.add(n); changed = True
clo, todo = set(), ['node']
while todo:
    n = todo.pop()
    if n not in clo:
        clo.add(n); todo += list(deps.get(n, ()))
print('types in the group', len(decl), '; naming a carrier', sorted(direct))
print('closure of node', len(clo), sorted(clo))
print('carrier types in the closure', sorted(clo & taint))
