import sys, os, re
root=sys.argv[1]; uses_path=sys.argv[2]
uses={}
for line in open(uses_path):
    m, us = line.rstrip("\n").split("\t"); uses[m]=set(x for x in us.split(",") if x)
mods={}
for base in ["src","tools"]:
    for dp,dn,fn in os.walk(os.path.join(root,base)):
        for f in fn:
            if f.endswith(".lean"):
                p=os.path.join(dp,f); mods[os.path.relpath(p,os.path.join(root,base))[:-5].replace(os.sep,".")]=p
imp_re=re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.\']+)', re.M)
G={m: sorted(set(d for d in imp_re.findall(open(p,encoding="utf-8",errors="replace").read().split("\nnamespace",1)[0]) if d in mods)) for m,p in mods.items()}
def cone(x):
    seen={x}; st=[x]
    while st:
        y=st.pop()
        for z in G[y]:
            if z not in seen: seen.add(z); st.append(z)
    return seen
target="Effect4.Laws.Program.Typed.Commands.Clauses.All"
C=cone(target)
cg={m for m in C if m.startswith("Effect4.Codegen") or m in ("Effect4.Api","Effect4.Store.Domain.Derived.Program")}
print("Codegen-side modules in the typed chain's cone:", len(cg))
# edges from non-codegen modules into the codegen side
for m in sorted(C):
    if m in cg or m.startswith("Effect4.Codegen"): continue
    for n in G[m]:
        if n in cg:
            used = sorted(uses.get(m,set()) & cone(n) & cg)
            print(f"  {m} -> {n}; names from the codegen side: {used[:6]}")
