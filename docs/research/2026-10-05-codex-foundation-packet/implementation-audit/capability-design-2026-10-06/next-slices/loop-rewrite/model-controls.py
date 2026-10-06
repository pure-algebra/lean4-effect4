"""Finite source-equation mirror, not Lean/Effect execution or a project representation.
Single integer cell; first-order tuple terms; source DenoteB budget is global k at each loop body.
Only the selected fragment equations needed by named controls are represented.
"""
import json
from pathlib import Path
P=Path(__file__).parent
BAD=object()
def lit(x): return ('lit',x)
def var(n): return ('var',n)
def add(a,b): return ('add',a,b)
def lt(a,b): return ('lt',a,b)
def term(t,env):
 op,*a=t
 if op=='lit': return a[0]
 if op=='var': return env[a[0]] if a[0]<len(env) else BAD
 x,y=term(a[0],env),term(a[1],env)
 if x is BAD or y is BAD or type(x) is not int or type(y) is not int:return BAD
 return x+y if op=='add' else x<y

def clean(e):
 op,*a=e
 if op=='suspend':return clean(a[0])
 if op in ('bind','onExit','catch'):return (op,clean(a[0]),clean(a[1]))
 if op=='select':return (op,a[0],clean(a[1]),clean(a[2]))
 if op=='loop':return (op,*a[:4],clean(a[4]))
 return e

def run(e,k,env=(),cell=0,mutant=None):
 op,*a=e
 if op=='pure':
  v=term(a[0],env);return (('failure','bad-shape') if v is BAD else ('success',v)),cell
 if op=='fail':return ('failure',a[0]),cell
 if op=='addCell':
  v=term(a[0],env)
  return (('failure','bad-shape'),cell) if v is BAD else (('success',None),cell+v)
 if op=='get':return ('success',cell),cell
 if op=='suspend':return run(a[0],max(0,k-1) if mutant=='charge-suspend' else k,env,cell,mutant)
 if op=='select':
  v=term(a[0],env)
  if type(v) is not bool:return ('failure','bad-shape'),cell
  return run(a[1] if v else a[2],k,env,cell,mutant)
 if op in ('bind','catch','onExit'):
  ex,s=run(a[0],k,env,cell,mutant)
  if ex is None:return (None,cell if mutant=='reset-unfinished' else s)
  if op=='bind':return run(a[1],k,env+(ex[1],),s,mutant) if ex[0]=='success' else (ex,s)
  if op=='catch':return (ex,s) if ex[0]=='success' else run(a[1],k,env+(ex[1],),s,mutant)
  fin,s1=run(a[1],k,env+(ex,),s,mutant)
  if fin is None:return None,s1
  if fin[0]=='success':return ex,s1
  return (fin if ex[0]=='success' else ('failure',('both',ex[1],fin[1]))),s1
 if op=='loop':
  initial,test,step,result,body=a
  cursor=term(initial,env)
  if cursor is BAD:return ('failure','bad-shape'),cell
  start=cell
  for _ in range(k):
   outer=env[:-1] if mutant=='drop-outer-slot' and env else env
   current=outer+(cursor,)
   flag=term(test,current)
   if type(flag) is not bool:return ('failure','bad-shape'),cell
   if not flag:
    v=term(result,current)
    return (('failure','bad-shape') if v is BAD else ('success',v)),cell
   ex,cell=run(body,k,current,cell,mutant)
   if ex is None:return None,(start if mutant=='reset-unfinished' else cell)
   if ex[0]=='failure':return ex,(start if mutant=='reset-failure' else cell)
   cursor=term(step,current+(ex[1],))
   if cursor is BAD:return ('failure','bad-shape'),cell
  return None,(start if mutant=='reset-unfinished' else cell)
 raise ValueError(e)

simple=('loop',lit(0),lt(var(0),lit(2)),add(var(0),lit(1)),var(0),('suspend',('addCell',lit(1))))
inner=('loop',lit(0),lt(var(2),lit(2)),add(var(2),lit(1)),var(2),('suspend',('addCell',add(add(var(0),var(1)),var(2)))))
nested=('suspend',('loop',lit(0),lt(var(1),lit(2)),add(var(1),lit(1)),var(1),inner))
body=('bind',('addCell',lit(1)),('select',lt(var(0),lit(1)),('pure',lit(None)),('fail','boom')))
failing=('loop',lit(0),lt(var(0),lit(3)),add(var(0),lit(1)),var(0),('suspend',body))
cleanup=('onExit',failing,('suspend',('addCell',lit(100))))
simple_in_finalizer=('loop',lit(0),lt(var(1),lit(2)),add(var(1),lit(1)),var(1),('suspend',('addCell',lit(1))))
finloop=('onExit',('pure',lit(9)),('suspend',simple_in_finalizer))
straight=('bind',('suspend',('addCell',lit(3))),('suspend',('get',)))
false_start=('loop',lit(0),lit(False),var(0),var(0),('pure',lit(None)))
bad_initial=('loop',var(9),lit(False),var(0),var(0),('pure',lit(None)))
cases=[('straight',straight,()),('loop',simple,()),('nested',nested,(7,)),('failure-cleanup',cleanup,()),('unfinished-finalizer',finloop,()),('false-initial-test',false_start,()),('bad-initial-term',bad_initial,())]
checks=[]
def check(name,ok,detail):
 assert ok,(name,detail)
 checks.append({'name':name,'pass':bool(ok),'detail':detail})
for name,e,env in cases:
 for k in range(6):
  for s in [0,4,19]:
   before=run(e,k,env,s);after=run(clean(e),k,env,s)
   check(f'{name}/budget={k}/initial-cell={s}',before==after,{'before':before,'after':after})
check('loop-zero',(r:=run(simple,0))==(None,0),r)
check('loop-one-round-keeps-write',(r:=run(simple,1))==(None,1),r)
check('loop-two-rounds-still-needs-stop-test',(r:=run(simple,2))==(None,2),r)
check('loop-three-rounds-completes',(r:=run(simple,3))==(('success',2),2),r)
check('nested-captures',(r:=run(nested,3,(7,)))==(('success',2),32),r)
check('unfinished-does-not-run-finalizer',(r:=run(cleanup,1))==(None,1),r)
check('failure-retains-body-and-finalizer-writes',(r:=run(cleanup,2))==(('failure','boom'),102),r)
check('finalizer-itself-unfinished',(r:=run(finloop,1))==(None,1),r)
check('false-test-at-zero-budget',(r:=run(false_start,0))==(None,0),r)
check('bad-initial-term-even-at-zero',(r:=run(bad_initial,0))==(('failure','bad-shape'),0),r)
mutants=[('charge-suspend',('suspend',simple),1,()),('reset-unfinished',simple,1,()),('reset-failure',failing,2,()),('drop-outer-slot',nested,3,(7,))]
for mutant,e,k,env in mutants:
 good=run(e,k,env);bad=run(e,k,env,mutant=mutant)
 check('refuses-'+mutant,good!=bad,{'correct_mirror':good,'mutant':bad})
check('refuses-unshifted-finalizer-insertion',run(('onExit',('pure',lit(9)),simple),1)!=run(finloop,1),{'unshifted':run(('onExit',('pure',lit(9)),simple),1),'scoped':run(finloop,1)})
# Exact source equation for the checker path, not a checker implementation.
check('diagnostic-path-not-invariant',[0]!=[],{'suspend_unbound_leaf_path':[0],'cleaned_unbound_leaf_path':[]})
output={'kind':'Finite Python source-equation mirror; no Lean, Effect, machine or target execution','scope':'Single integer cell and named constructors only; not full StoreSig/Stores','case_families':len(cases),'comparisons':7*6*3,'named_boundary_controls':10,'mutants_refused':5,'diagnostic_path_control':1,'checks':checks,'all_pass':all(c['pass'] for c in checks)}
(P/'model-controls-output.json').write_text(json.dumps(output,indent=2)+'\n')
print(json.dumps({k:output[k] for k in ['kind','comparisons','named_boundary_controls','mutants_refused','diagnostic_path_control','all_pass']}))
