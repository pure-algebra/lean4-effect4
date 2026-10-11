import sys, os, re, collections
root = sys.argv[1]; uses_path = sys.argv[2]
uses = {}
for line in open(uses_path):
    m, us = line.rstrip("\n").split("\t")
    uses[m] = set(x for x in us.split(",") if x)
mods = {}
for base in ["src", "tools"]:
    for dp, dn, fn in os.walk(os.path.join(root, base)):
        for f in fn:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                mods[os.path.relpath(p, os.path.join(root, base))[:-5].replace(os.sep, ".")] = p
imp_re = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.\']+)', re.M)
G = {}
for m, p in mods.items():
    head = open(p, encoding="utf-8", errors="replace").read().split("\nnamespace", 1)[0]
    G[m] = sorted(set(imp_re.findall(head)))
def closure(start):
    seen=set(); st=[start]
    while st:
        x=st.pop()
        for y in G.get(x, []):
            if y not in seen: seen.add(y); st.append(y)
    return seen
cl = {}
def C(m):
    if m not in cl: cl[m] = closure(m) | {m}
    return cl[m]
# an import edge m -> n is "unused by constants" when no module m's constants name lies in
# C(n) minus the union of C(other imports of m)
cands = []
for m in G:
    if not m.startswith("Effect4") or m not in uses: continue
    imps = [n for n in G[m] if n in mods]
    for n in imps:
        others = set()
        for o in imps:
            if o != n: others |= C(o)
        excl = C(n) - others
        hit = uses[m] & excl
        if not hit:
            cands.append((len(excl), m, n))
cands.sort(reverse=True)
print("import edges whose exclusive cone no constant of the importer names (top by cone size):")
for k, m, n in cands[:25]:
    print(f"  {k:4d}  {m}  ->  {n}")
# the specific edge
m, n = "Effect4.Laws.Program.Means", "Effect4.Api"
imps = G[m]; others=set()
for o in imps:
    if o != n: others |= C(o)
excl = C(n) - others
print("\nMeans -> Api: exclusive cone", len(excl), "modules; named:", sorted(uses.get(m, set()) & excl))
