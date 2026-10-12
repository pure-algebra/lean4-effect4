import subprocess, re, json, sys
from pathlib import Path
base = 'c31acf15b'
head = sys.argv[1] if len(sys.argv) > 1 else None
paths = [
    'src/Effect4/Laws/Data/ListRel.lean',
    'src/Effect4/Laws/Data/ListRelConnectors.lean',
    'src/Effect4/Laws/Step/Reading.lean',
    'src/Effect4/Laws/Step/Checking.lean',
    'src/Effect4/Laws/Library/Pool/Ops.lean',
]
def declarations(s):
 out={}
 pat=re.compile(r'^(?:protected |private |noncomputable )?(theorem|def|abbrev|inductive|structure|proof_goal|class|instance)\s+([A-Za-z_][A-Za-z_0-9.\']*)',re.M)
 matches=list(pat.finditer(s))
 for i,m in enumerate(matches):
  if m.group(1)=='instance' and m.group(2) not in {'algebraCore','algebraEvaluator','wakeEvaluator','MaskKept.decidable','MaskRuns.decidable'}:continue
  end=matches[i+1].start() if i+1<len(matches) else len(s)
  raw=s[m.start():end]
  depth=0; stop=len(raw)
  for j,c in enumerate(raw):
   if c in '({[⦃':depth+=1
   elif c in ')}]⦄':depth-=1
   if depth!=0:continue
   if raw[j:j+2]==':=':
    line=raw[raw.rfind('\n',0,j)+1:j]
    if re.search(r'\bletI?\b',line):continue
    stop=j;break
   if raw[j:j+5]=='where' and (j==0 or raw[j-1].isspace()):stop=j;break
   if c=='|' and raw[raw.rfind('\n',0,j)+1:j].strip()=='':stop=j;break
  raw=raw[:stop]
  out[m.group(2)]=dict(kind=m.group(1),header=' '.join(raw.split()))
 return out
report = {}
for path in paths:
    before = subprocess.check_output(['git', 'show', base + ':' + path], text=True)
    after = subprocess.check_output(['git', 'show', head + ':' + path], text=True) if head else Path(path).read_text()
    a, b = declarations(before), declarations(after)
    changes = []
    for name in sorted(a.keys() & b.keys()):
        if a[name] != b[name]:
            expected = a[name]['header'].replace('Modules.Pointwise ', '_root_.Effect4.ListRel ').replace('Pointwise ', 'ListRel ')
            assert expected == b[name]['header'], (path, name, expected, b[name])
            changes.append(dict(name=name, before=a[name]['header'], after=b[name]['header']))
    removed = sorted(a.keys() - b.keys())
    assert not removed or removed == ['Pointwise'], (path, removed)
    assert not b.keys() - a.keys()
    report[path] = dict(beforeLines=len(before.splitlines()), afterLines=len(after.splitlines()),
        existingNamedHeaders=len(a), unchangedNamedHeaders=len(a.keys() & b.keys()) - len(changes),
        changedHeaders=changes, removedNames=removed)
print(json.dumps(report, indent=2))
