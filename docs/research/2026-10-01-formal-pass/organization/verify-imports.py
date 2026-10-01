# Verifier of seat ORGANIZATION: walk the import headers of tracked .lean files.
# Reports reachability of src/Effect4 from the two roots, whether Effect4 reaches Laws,
# Test reachability from Test/All.lean, and which core modules import the `Effects` package.
import re, subprocess, os
os.chdir('/Users/pooks/Dev/lean4-effect4')
files = [f for f in subprocess.check_output(['git','ls-files','*.lean']).decode().split('\n') if f]
def mod_of(path):
    for pre in ('src/','tools/',''):
        if path.startswith(pre) and pre:
            return path[len(pre):-5].replace('/','.')
    return path[:-5].replace('/','.')
modpath = {mod_of(f): f for f in files}
imp = {}
for m, f in modpath.items():
    out = []
    for line in open(f, encoding='utf-8'):
        s = line.strip()
        if s.startswith('import '): out += s[len('import '):].split()
        elif s.startswith('prelude') or s == '' or s.startswith('--') or s.startswith('module') or s.startswith('public import'):
            if s.startswith('public import'): out += s[len('public import '):].split()
            continue
        elif s.startswith('/-') or s.startswith('set_option'): break
        else: break
    imp[m] = out
def reach(roots):
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m in seen: continue
        seen.add(m)
        stack += [x for x in imp.get(m, [])]
    return seen
core = reach(['Effect4']); laws = reach(['Effect4.Laws'])
srcmods = [m for m,f in modpath.items() if f.startswith('src/Effect4')]
print(f"src/Effect4 modules (incl. Effect4.lean): {len(srcmods)}")
unreached = [m for m in srcmods if m not in core and m not in laws]
print(f"unreached from Effect4 or Effect4.Laws: {unreached}")
print(f"Effect4 reaches Laws modules: {sorted(m for m in core if m.startswith('Effect4.Laws'))}")
testmods = [m for m,f in modpath.items() if f.startswith('Test/')]
t = reach(['Test.All'])
print(f"Test modules: {len(testmods)}; unreached from Test.All: {[m for m in testmods if m not in t]}")
eff_in_core = sorted(m for m in core if any(x.startswith('Effects') for x in imp.get(m, [])) and m.startswith('Effect4'))
print(f"core-root modules importing the Effects package directly: {eff_in_core}")
for m in eff_in_core: print('  ', m, [x for x in imp[m] if x.startswith('Effects')])
eff_in_laws = sorted(m for m in laws if m not in core and any(x.startswith('Effects') for x in imp.get(m, [])) and m.startswith('Effect4'))
print(f"Laws-only modules importing Effects directly: {len(eff_in_laws)} {eff_in_laws}")
print(f"external (non-tracked) modules reached from Effect4: {sorted(set(x.split('.')[0] for x in core if x not in modpath))}")
