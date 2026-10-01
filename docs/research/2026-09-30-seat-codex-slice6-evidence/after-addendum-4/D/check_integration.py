#!/usr/bin/env python3
"""Read-only import/diagnostic scan. Overlay contains repo-relative proposed files."""
from pathlib import Path
import argparse, json, re
ap=argparse.ArgumentParser()
ap.add_argument('--repo',type=Path,default=Path('/Users/pooks/Dev/lean4-effect4-slice6'))
ap.add_argument('--overlay',type=Path)
ap.add_argument('--deleted',action='append',default=[])
a=ap.parse_args()
files={str(p.relative_to(a.repo)):p.read_text() for base in ('src','Test') for p in (a.repo/base).rglob('*.lean')}
if a.overlay:
    for base in ('src','Test'):
        if (a.overlay/base).exists():
            for p in (a.overlay/base).rglob('*.lean'):
                files[str(p.relative_to(a.overlay))]=p.read_text()
for p in a.deleted:
    files.pop(p,None)
def module(path):
    s=path.removesuffix('.lean')
    if s.startswith('src/'): s=s[4:]
    return s.replace('/','.')
def strip_comments(s):
    # Lean nested block comments; preserve newlines for locations.
    out=[]; i=0; depth=0
    while i<len(s):
        if s.startswith('/-',i): depth+=1;out.extend('  ');i+=2
        elif depth and s.startswith('-/',i): depth-=1;out.extend('  ');i+=2
        elif depth: out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s.startswith('--',i):
            end=s.find('\n',i)
            if end<0: break
            out.extend(' '*(end-i));i=end
        else: out.append(s[i]);i+=1
    return ''.join(out)
mods={module(p):p for p in files}
imports={}
errors=[]
diag=[]
for p,s in files.items():
    clean=strip_comments(s)
    names=[]
    for match in re.finditer(r'^import\s+([^\n]+)',clean,re.M):
        names.extend(match.group(1).split())
    imports[module(p)]=names
    for name in names:
        if name.startswith(('Effect4.','Test.')) and name not in mods:
            errors.append([p,'missing import',name])
        if p.startswith('src/') and name.startswith('Test.'):
            errors.append([p,'library imports Test',name])
    if p.startswith('src/'):
        for match in re.finditer(r'\b(?:forkedOf|AgreesUpdates)\b|TraceFacts\.(?:Agrees|M1Trace)',clean):
            diag.append([p,clean.count('\n',0,match.start())+1,match.group()])
# Reachability and cycle test limited to local module edges.
vis=set();active=[];cycles=[]
def walk(m):
    if m in active: cycles.append(active[active.index(m):]+[m]);return
    if m in vis:return
    vis.add(m);active.append(m)
    for n in imports.get(m,[]):
        if n in mods:walk(n)
    active.pop()
for root in ('Effect4','Effect4.Laws','Test.All'):walk(root)
print(json.dumps({'errors':errors,'diagnostic_symbols_in_library':diag,'cycles':cycles,'unreachable':[p for m,p in mods.items() if m not in vis]},indent=2))
raise SystemExit(bool(errors or diag or cycles))
