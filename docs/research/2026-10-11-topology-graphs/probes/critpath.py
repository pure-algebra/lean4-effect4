import sys, os, re, collections
root = sys.argv[1]; drop = [tuple(x.split("->")) for x in sys.argv[2:]]
mods = {}
for base in ["src", "tools"]:
    for dp, dn, fn in os.walk(os.path.join(root, base)):
        for f in fn:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                mods[os.path.relpath(p, os.path.join(root, base))[:-5].replace(os.sep, ".")] = p
imp_re = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.\']+)', re.M)
G = {}; L = {}
for m, p in mods.items():
    t = open(p, encoding="utf-8", errors="replace").read()
    G[m] = sorted(set(d for d in imp_re.findall(t.split("\nnamespace", 1)[0]) if d in mods))
    L[m] = t.count("\n")
for a, b in drop:
    G[a] = [d for d in G[a] if d != b]
memo = {}
sys.setrecursionlimit(100000)
def best(m):
    if m in memo: return memo[m]
    b, arg = 0, None
    for d in G[m]:
        v = best(d)[0]
        if v > b: b, arg = v, d
    memo[m] = (b + L[m], arg); return memo[m]
def anc(x):
    seen=set(); st=[x]
    while st:
        y=st.pop()
        for z in G[y]:
            if z not in seen: seen.add(z); st.append(z)
    return seen
for t in ["Effect4.Laws", "Effect4.Laws.Program.Typed.Commands.Clauses.All", "Effect4.Laws.Program.Typed.Results"]:
    v, _ = best(t); chain=[]; x=t
    while x: chain.append(x); x = best(x)[1]
    print(f"{t}: critical path {v} lines over {len(chain)} modules; depends on {len(anc(t))} modules; Codegen in cone: {sum(1 for y in anc(t) if y.startswith('Effect4.Codegen'))}")
