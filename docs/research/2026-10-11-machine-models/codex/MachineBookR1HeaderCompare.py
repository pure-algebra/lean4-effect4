import subprocess,re,json
from pathlib import Path
base=Path.cwd()
profile={'src/Effect4/Machine/Integers.lean','src/Effect4/Machine/Term.lean','Test/Counterexamples/Machine/Semantics/MulOutsideProfile.lean'}
paths=[p for p in subprocess.check_output(['git','diff','--name-only','18cd908b9','268b9051b'],cwd=base,text=True).splitlines() if p not in profile]
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
report={}
for p in paths:
 if not p.endswith('.lean'):continue
 before=subprocess.check_output(['git','show','18cd908b9:'+p],cwd=base,text=True)
 after=subprocess.check_output(['git','show','268b9051b:'+p],cwd=base,text=True);a=declarations(before);b=declarations(after)
 changed=[dict(name=k,before=a[k]['header'],after=b[k]['header']) for k in a.keys() & b.keys() if a[k]!=b[k]]
 report[p]=dict(beforeLines=len(before.splitlines()),afterLines=len(after.splitlines()),existingNamedHeaders=len(a),unchangedNamedHeaders=len(a.keys() & b.keys())-len(changed),changedHeaders=sorted(changed,key=lambda x:x['name']),removedHeaders=[dict(name=k,**a[k]) for k in a.keys()-b.keys()],newHeaders=[dict(name=k,**b[k]) for k in b.keys()-a.keys()])
Path('/private/tmp/MachineBookR1Headers.json').write_text(json.dumps(report,indent=2)+'\n')
for p,r in report.items():
 print(p)
 for h in r['changedHeaders']:print('  amended:',h['name'])
 for h in r['removedHeaders']:print('  redirected:',h['name'])
print('Measured existing named headers:',sum(r['existingNamedHeaders'] for r in report.values()))
print('Unchanged text:',sum(r['unchangedNamedHeaders'] for r in report.values()))
print('Amended text:',sum(len(r['changedHeaders']) for r in report.values()))
print('Removed local names:',sum(len(r['removedHeaders']) for r in report.values()))
