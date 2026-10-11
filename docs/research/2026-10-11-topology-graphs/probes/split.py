import sys, os, re
root=sys.argv[1]
mods={}
for base in ["src","tools"]:
    for dp,dn,fn in os.walk(os.path.join(root,base)):
        for f in fn:
            if f.endswith(".lean"):
                p=os.path.join(dp,f); mods[os.path.relpath(p,os.path.join(root,base))[:-5].replace(os.sep,".")]=p
imp_re=re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.\']+)', re.M)
G={}; L={}
for m,p in mods.items():
    t=open(p,encoding="utf-8",errors="replace").read()
    G[m]=sorted(set(d for d in imp_re.findall(t.split("\nnamespace",1)[0]) if d in mods)); L[m]=t.count("\n")
def stats(G, label):
    memo={}
    sys.setrecursionlimit(100000)
    def best(m):
        if m in memo: return memo[m]
        b=0
        for d in G[m]: b=max(b,best(d))
        memo[m]=b+L[m]; return memo[m]
    def cone(x):
        seen={x}; st=[x]
        while st:
            y=st.pop()
            for z in G[y]:
                if z not in seen: seen.add(z); st.append(z)
        return seen
    for t in ["Effect4.Laws.Program.Typed.Commands.Clauses.All","Effect4.Laws.Program.RuntimeR","Effect4.Laws"]:
        c=cone(t)
        print(f"{label:>10} {t}: critical {best(t)} lines; cone {len(c)} modules, {sum(L[x] for x in c)} lines; codegen-side {sum(1 for x in c if x.startswith('Effect4.Codegen') or x=='Effect4.Store.Domain.Derived.Program')}")
    # who rebuilds when Codegen.Print changes
    R={}
    for m,ds in G.items():
        for d in ds: R.setdefault(d,set()).add(m)
    def up(x):
        seen=set(); st=[x]
        while st:
            y=st.pop()
            for z in R.get(y,()):
                if z not in seen: seen.add(z); st.append(z)
        return seen
    for x in ["Effect4.Codegen.Print","Effect4.Codegen.Read"]:
        u=up(x)
        print(f"{label:>10} edit {x}: rebuilds {len(u)} modules, of them {sum(1 for y in u if y.startswith('Effect4.Laws.Program.Typed'))} typed-state law modules, {sum(1 for y in u if y.startswith('Effect4.Laws.Program.Simulation'))} simulation modules")
stats(G, "as is")
# hypothetical split: Effect4.Api.Machine = Api's imports that are not codegen/schema/wire/authoring
codegenish=lambda d: d.startswith("Effect4.Codegen") or d.startswith("Effect4.Schema") or d in ("Effect4.Store.Domain.ProgramWire","Effect4.Store.Domain.Cascade")
H={m:list(ds) for m,ds in G.items()}
H["Effect4.Api.Machine"]=[d for d in G["Effect4.Api"] if not codegenish(d)]
L["Effect4.Api.Machine"]=L["Effect4.Api"]//2
lawsUsingApi=[m for m in G if m.startswith("Effect4.Laws") and "Effect4.Api" in G[m]]
for m in lawsUsingApi:
    H[m]=[("Effect4.Api.Machine" if d=="Effect4.Api" else d) for d in G[m]]
print("law modules importing Effect4.Api:", len(lawsUsingApi))
stats(H, "split")
print("Api.Machine would import:", H["Effect4.Api.Machine"])
