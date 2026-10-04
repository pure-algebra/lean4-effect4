import re, sys, os
from functools import lru_cache
roots = {'Effect4': 'src', 'OCaml5': 'src', 'Test': '.', 'Tools': 'tools', 'Effect4Gen': 'tools', 'ProofGraph': 'tools', 'Conform': 'tools'}
def path_of(mod):
    top = mod.split('.')[0]
    if top not in roots: return None
    p = os.path.join(roots[top], *mod.split('.')) + '.lean'
    return p if os.path.exists(p) else None
imp = re.compile(r'^\s*(?:public\s+|meta\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)')
@lru_cache(None)
def direct(mod):
    p = path_of(mod)
    if not p: return ()
    out = []
    for line in open(p, encoding='utf-8'):
        m = imp.match(line)
        if m: out.append(m.group(1))
        elif line.strip().startswith(('/-', 'namespace', 'section', 'set_option', '@[', 'def ', 'theorem')): break
    return tuple(out)
def closure(mod, extra=None):
    seen = set(); stack = [mod]
    while stack:
        m = stack.pop()
        if m in seen: continue
        seen.add(m)
        ds = list(direct(m))
        if extra and m in extra: ds += extra[m]
        stack.extend(d for d in ds if path_of(d))
    return seen
mod = sys.argv[1]
add = {}
for a in sys.argv[2:]:
    k, v = a.split('+=')
    add.setdefault(k, []).append(v)
before = closure(mod); after = closure(mod, add)
print(mod, 'Effect4 modules in closure:', len([m for m in before if m.startswith('Effect4')]), '->', len([m for m in after if m.startswith('Effect4')]))
print('new:', sorted(after - before))
