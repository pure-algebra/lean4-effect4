"""Graph analysis of the proof dump (scratch, not part of the tree).

Input: proofgraph.tsv from ProofDump.lean: name, kind, module, theorem deps, statement defs,
definition-value defs. And proofgraph.tsv.uses: module, modules its constants name.
"""
import sys, collections, os, re

path = sys.argv[1]
root_dir = sys.argv[2]
rows = {}
for line in open(path, encoding="utf-8"):
    parts = line.rstrip("\n").split("\t")
    if len(parts) < 6:
        continue
    n, k, m, td, sd, vd = parts
    rows[n] = (k, m, [x for x in td.split(",") if x], [x for x in sd.split(",") if x],
               [x for x in vd.split(",") if x])

kinds = collections.Counter(r[0] for r in rows.values())
print("constants by kind:", dict(kinds))
T = {n: [d for d in r[2] if d in rows] for n, r in rows.items() if r[0] == "thm"}
print("theorems:", len(T), "edges:", sum(len(v) for v in T.values()))

# tops: the claims named in docs/STATE.md and the system map
tops_wanted = ["m7_proved", "exitHandles_valid", "session_eq_ref", "run_eq_ref", "run_eq_ref_table",
    "denoteRows_eq_session", "denoteRows_eq_session_host", "h8_loopedRows",
    "denoteRowsB_eq_session_host", "run_eq_meaning", "loopAgreement", "check_sound",
    "check_complete", "explain_none_iff", "read_print", "read_exact", "replay_unique",
    "journal_replays", "typedState_load", "runWith_denotes", "invoke_arm", "param_arm",
    "exits_hasTy", "m7_of_ledger", "drive_seg", "frontier_empty_iff_deadlocked",
    "compiled_region_bracket", "runWith_layer_denotes", "fits_sub", "lay_good",
    "holes_conservative", "refusals_nil_iff"]
tops = []
for w in tops_wanted:
    hits = [n for n in T if n == w or n.endswith("." + w)]
    tops += hits
print("tops found:", len(tops))
for t in tops:
    pass

# reachability from tops
def reach(starts, adj):
    seen = set(starts); st = list(starts)
    while st:
        x = st.pop()
        for y in adj.get(x, ()):
            if y not in seen:
                seen.add(y); st.append(y)
    return seen

R = reach(tops, T)
print("theorems under the tops:", len(R))

# longest dependency chain (DAG height) under the tops
sys.setrecursionlimit(1000000)
height = {}
order = []
state = {}
for s in R:
    if s in state: continue
    stack = [(s, 0)]
    while stack:
        x, i = stack.pop()
        if i == 0:
            if state.get(x) == 2: continue
            state[x] = 1
        ds = T.get(x, [])
        if i < len(ds):
            stack.append((x, i + 1))
            d = ds[i]
            if state.get(d) is None: stack.append((d, 0))
            elif state.get(d) == 1:
                print("cycle through", d)
        else:
            state[x] = 2; order.append(x)
nxt = {}
for x in order:
    best, arg = 0, None
    for d in T.get(x, []):
        if height.get(d, 0) > best: best, arg = height[d], d
    height[x] = best + 1; nxt[x] = arg
print("\nproof height (longest chain of theorems) per top:")
for t in sorted(tops, key=lambda t: -height.get(t, 0)):
    print(f"  {height.get(t,0):4d}  {t}")
t0 = max(tops, key=lambda t: height.get(t, 0))
chain = []; x = t0
while x: chain.append(x); x = nxt.get(x)
print(f"\nlongest chain from {t0} ({len(chain)} theorems), modules along it:")
lastm = None
for c in chain:
    m = rows[c][1]
    if m != lastm:
        print("   ", m, "::", c.split(".")[-1]); lastm = m

# dominators from a virtual root over tops (Cooper-Harvey-Kennedy on reverse postorder)
VR = "<root>"
succ = {VR: tops}
for x in R: succ[x] = T.get(x, [])
# postorder from VR
po = []; st = [(VR, 0)]; vis = {VR}
while st:
    x, i = st.pop()
    ss = succ.get(x, [])
    if i < len(ss):
        st.append((x, i + 1))
        y = ss[i]
        if y not in vis:
            vis.add(y); st.append((y, 0))
    else:
        po.append(x)
rpo = list(reversed(po)); pos = {x: i for i, x in enumerate(rpo)}
preds = collections.defaultdict(list)
for x in rpo:
    for y in succ.get(x, []):
        preds[y].append(x)
idom = {VR: VR}
def inter(a, b):
    while a != b:
        while pos[a] > pos[b]: a = idom[a]
        while pos[b] > pos[a]: b = idom[b]
    return a
changed = True
while changed:
    changed = False
    for x in rpo[1:]:
        ps = [p for p in preds[x] if p in idom]
        if not ps: continue
        new = ps[0]
        for p in ps[1:]: new = inter(p, new)
        if idom.get(x) != new:
            idom[x] = new; changed = True
kids = collections.defaultdict(list)
for x, d in idom.items():
    if x != d: kids[d].append(x)
size = {}
for x in reversed(rpo):  # children before parents in reverse of rpo? compute iteratively
    pass
def subtree(x):
    c = 0; st = [x]
    while st:
        y = st.pop(); c += 1; st.extend(kids[y])
    return c
dom_sizes = {x: subtree(x) - 1 for x in idom if x != VR}
print("\nnarrow waists: theorems that dominate the most theorems (reached from the tops only through them)")
for x in sorted(dom_sizes, key=lambda x: -dom_sizes[x])[:30]:
    top_or_not = " (top)" if x in tops else ""
    print(f"  {dom_sizes[x]:5d}  {x}{top_or_not}  [{rows[x][1]}]")
# non-top waists: exclude the tops themselves and their immediate subtrees
print("\nwaists that are not tops, dominating >= 40:")
for x in sorted(dom_sizes, key=lambda x: -dom_sizes[x]):
    if x in tops or dom_sizes[x] < 40: continue
    print(f"  {dom_sizes[x]:5d}  {x}  [{rows[x][1]}]  idom={idom[x]}")

# statement interface: how many theorem statements name each definition
stmt_in = collections.Counter()
for n, r in rows.items():
    if r[0] == "thm":
        for d in set(r[3]): stmt_in[d] += 1
print("\ninterface pressure: definitions named by the most theorem statements")
for d, c in stmt_in.most_common(30):
    print(f"  {c:6d}  {d}  [{rows[d][1] if d in rows else '?'}]")

# in-degree joints under the tops
indeg = collections.Counter()
for x in R:
    for d in T.get(x, []): indeg[d] += 1
print("\njoints: theorems used by the most theorems under the tops")
for d, c in indeg.most_common(15):
    print(f"  {c:5d}  {d}")
