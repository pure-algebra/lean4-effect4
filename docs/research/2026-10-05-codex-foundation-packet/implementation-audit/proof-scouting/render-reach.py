from pathlib import Path
from collections import deque
import json,hashlib,sys
root=Path('/Users/pooks/Dev/lean4-effect4')
p=root/'.lake/gen/semantics-report/semantics.json'
r=json.loads(p.read_text())
def limited(nodes,tops):
 todo=list(tops);reach=[]
 for _ in range(len(nodes)+1):
  if not todo:break
  n=todo.pop(0)
  if n in reach:continue
  reach.append(n);todo.extend(nodes[n])
 return reach,todo
def complete(nodes,tops):
 todo=deque(tops);seen=set();reach=[]
 while todo:
  n=todo.popleft()
  if n in seen:continue
  seen.add(n);reach.append(n);todo.extend(nodes[n])
 return reach
nodes={n['name']:n['broughtIn']['nearest'] for n in r['plan']['nodes']}
live=[]
for q in r['plan']['requirements']:
 tops=[n['name'] for n in q['top']+q['placed']]
 got,todo=limited(nodes,tops);want=complete(nodes,tops)
 live.append({'requirement':q['id'],'visited':len(got),'expected':len(want),'omitted':[x for x in want if x not in got],'pending':len(todo)})
shared={'T':['A','B','C'],'A':['D'],'B':['D'],'C':['D'],'D':['L'],'L':[]}
chain={'T':['A'],'A':['B'],'B':['C'],'C':['D'],'D':['L'],'L':[]}
witness=[]
for label,ns in [('positive chain',chain),('shared descendant',shared)]:
 got,pending=limited(ns,['T']);want=complete(ns,['T'])
 witness.append({'label':label,'nodes':ns,'limited':got,'complete':want,'pending':pending,'omitted':[x for x in want if x not in got]})
assert witness[0]['omitted']==[]
assert witness[1]['omitted']==['L']
out={'python':sys.version,'source':'tools/Tools/Semantics.lean renderPlan','sourceSha256':hashlib.sha256((root/'tools/Tools/Semantics.lean').read_bytes()).hexdigest(),'reportSha256':hashlib.sha256(p.read_bytes()).hexdigest(),'algorithm':'Mirror of renderPlan queue loop capped at nodes.size+1, compared with full visited-set traversal','scope':'Finite Python mirror, not executed Lean renderer. Synthetic graph could represent shared proof dependencies. Actual retained report comparison listed separately.','liveReport':live,'witnesses':witness}
Path('/private/tmp/codex-effect4-overnight-monitor/2026-10-05-proof-scouting/render-reach.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'liveReport':live,'witnesses':witness},indent=2))
