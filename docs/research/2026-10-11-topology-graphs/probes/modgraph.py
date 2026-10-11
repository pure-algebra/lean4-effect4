import os, re, sys, collections
root = sys.argv[1]
mods = {}
for base in ["src", "tools"]:
    for dp, dn, fn in os.walk(os.path.join(root, base)):
        for f in fn:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                rel = os.path.relpath(p, os.path.join(root, base))[:-5].replace(os.sep, ".")
                mods[rel] = p
imp_re = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.\']+)', re.M)
G = {}
lines = {}
for m, p in mods.items():
    txt = open(p, encoding="utf-8", errors="replace").read()
    # only header region: imports precede first non-import code; approximate by scanning all import lines before '/-!' or 'namespace'
    head = txt.split("\nnamespace", 1)[0]
    deps = [d for d in imp_re.findall(head) if d in mods]
    G[m] = sorted(set(deps))
    lines[m] = txt.count("\n")
scope = [m for m in G if m.startswith("Effect4")]
print("modules total", len(G), "Effect4.*", len(scope))
# reverse graph
R = collections.defaultdict(set)
for m, ds in G.items():
    for d in ds: R[d].add(m)
# transitive dependents count (rebuild fan-out), restricted to Effect4.* and Test excluded
from functools import lru_cache
sys.setrecursionlimit(100000)
def closure(start, adj):
    seen = set(); st = [start]
    while st:
        x = st.pop()
        for y in adj.get(x, ()):
            if y not in seen: seen.add(y); st.append(y)
    return seen
fan = {m: closure(m, R) for m in scope}
fanl = {m: sum(lines[x] for x in fan[m]) for m in scope}
print("\nTop rebuild fan-out (modules depending transitively; lines rebuilt):")
for m in sorted(scope, key=lambda m: -len(fan[m]))[:25]:
    print(f"{len(fan[m]):5d} {fanl[m]:8d}  {m} ({lines[m]} lines, {len(R[m])} direct)")
# critical path weighted by lines (longest path in DAG of imports) among Effect4.*
order = []
state = {}
def topo(m):
    stack=[(m,0)]
    while stack:
        x,i = stack.pop()
        if i==0:
            if state.get(x)==2: continue
            state[x]=1
        ds=[d for d in G[x]]
        if i < len(ds):
            stack.append((x,i+1))
            d=ds[i]
            if state.get(d) is None: stack.append((d,0))
        else:
            state[x]=2; order.append(x)
for m in G: 
    if state.get(m) is None: topo(m)
best = {}; prev = {}
for m in order:
    b=0; pv=None
    for d in G[m]:
        if best[d] > b: b=best[d]; pv=d
    best[m] = b + lines[m]; prev[m]=pv
for target in ["Effect4.Laws", "Effect4", "Effect4.Laws.Program.Typed.Commands.Clauses.All"]:
    if target not in best: continue
    path=[]; x=target
    while x: path.append(x); x=prev[x]
    print(f"\nLongest import chain (by lines) to {target}: {best[target]} lines over {len(path)} modules")
    for x in reversed(path): print(f"   {lines[x]:6d}  {x}")
# depth (unweighted) 
dep = {}
for m in order:
    dep[m] = 1 + max([dep[d] for d in G[m]], default=0)
print("\nImport DAG height:", max(dep[m] for m in scope))
# dominators of the import DAG from root Effect4.Laws: modules that every import path from the root to a leaf passes through? Use reachability: a module d dominates set S if removing it disconnects. Compute articulation-like: for each module, how many modules become unreachable from root when it is removed.
root_ = "Effect4.Laws"
reach0 = closure(root_, G)
print("\nModules reachable from Effect4.Laws:", len(reach0))
# immediate dominators via iterative algorithm on DAG (root -> imports)
idx = {}
rpo = [m for m in reversed(order) if m in reach0 or m==root_]
# order is post-order of DFS over deps (children first). reversed = parents first: proper for dominators with edges m->dep
preds = collections.defaultdict(list)
for m in rpo:
    for d in G[m]:
        if d in reach0: preds[d].append(m)
pos = {m:i for i,m in enumerate(rpo)}
idom = {root_: root_}
def intersect(a,b):
    while a!=b:
        while pos[a] > pos[b]: a = idom[a]
        while pos[b] > pos[a]: b = idom[b]
    return a
changed=True
while changed:
    changed=False
    for m in rpo:
        if m==root_: continue
        ps=[p for p in preds[m] if p in idom]
        if not ps: continue
        new=ps[0]
        for p in ps[1:]: new=intersect(p,new)
        if idom.get(m)!=new: idom[m]=new; changed=True
# dominator subtree sizes: modules whose only route from the root passes through x
kids=collections.defaultdict(list)
for m,d in idom.items():
    if m!=d: kids[d].append(m)
def size(x):
    s=1; st=[x]
    cnt=0
    while st:
        y=st.pop(); cnt+=1; st.extend(kids[y])
    return cnt
print("\nImport-graph dominators from Effect4.Laws (modules reached only through x):")
for x in sorted(idom, key=lambda x:-size(x))[:20]:
    print(f"{size(x)-1:5d}  {x}")
