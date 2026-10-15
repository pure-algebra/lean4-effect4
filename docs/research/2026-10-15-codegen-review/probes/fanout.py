import os, re, sys, collections
root = '/Users/pooks/Dev/lean4-effect4'
mods = {}
for base in ['src', 'tools', '.']:
    top = os.path.join(root, base)
    for dp, dn, fn in os.walk(top):
        if '.lake' in dp or 'node_modules' in dp or '/docs' in dp or '/vendor' in dp or '/harness' in dp or '/apps' in dp: dn[:] = []; continue
        if base == '.' and not dp.startswith(os.path.join(root, 'Test')): 
            if dp != top: dn[:] = []
            continue
        for f in fn:
            if f.endswith('.lean'):
                p = os.path.join(dp, f)
                m = os.path.relpath(p, top)[:-5].replace('/', '.')
                mods.setdefault(m, p)
imp = {}
pat = re.compile(r'^\s*(?:public\s+)?import\s+(.+)$')
for m, p in mods.items():
    s = []
    for line in open(p, encoding='utf-8', errors='replace'):
        mm = pat.match(line)
        if mm: s += [x for x in mm.group(1).split() if x in mods]
    imp[m] = s
rev = collections.defaultdict(set)
for m, s in imp.items():
    for x in s: rev[x].add(m)
def closure(m):
    seen, st = set(), [m]
    while st:
        x = st.pop()
        for y in rev[x]:
            if y not in seen: seen.add(y); st.append(y)
    return seen
for m in sys.argv[1:]:
    c = closure(m)
    laws = sum(1 for x in c if x.startswith('Effect4.Laws'))
    core = sum(1 for x in c if x.startswith('Effect4.') and not x.startswith('Effect4.Laws'))
    tools = sum(1 for x in c if x.split('.')[0] in ('Tools','Drivers','Conform','ProofGraph','Effect4Gen'))
    test = sum(1 for x in c if x.startswith('Test'))
    print(f"{m}\t{len(c)}\tcore {core}\tlaws {laws}\ttools {tools}\ttest {test}" if m in mods else f"{m}\tNOT FOUND")
print('total modules', len(mods))

def path(a, b):
    from collections import deque
    q = deque([[a]]); seen = {a}
    while q:
        p = q.popleft()
        if p[-1] == b: return p
        for y in imp.get(p[-1], []):
            if y not in seen: seen.add(y); q.append(p + [y])
if os.environ.get('PATHS'):
    for pair in os.environ['PATHS'].split(','):
        a, b = pair.split(':'); print(' -> '.join(path(a, b) or ['none']))
if os.environ.get('CUT'):
    for pair in os.environ['CUT'].split(','):
        a, b = pair.split(':')
        if b in imp.get(a, []): imp[a].remove(b); rev[b].discard(a)
        else: print('no edge', a, b)
    for m in os.environ.get('AFTER', '').split(','):
        if m:
            c = closure(m); print('after cut', m, len(c), 'laws', sum(1 for x in c if x.startswith('Effect4.Laws')))
    if os.environ.get('PATHS2'):
        for pair in os.environ['PATHS2'].split(','):
            a, b = pair.split(':'); print(' -> '.join(path(a, b) or ['none']))
