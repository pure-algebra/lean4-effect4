"""Small independent models. They execute neither Lean nor an Effect runtime."""
import json
from dataclasses import dataclass
from pathlib import Path

@dataclass(frozen=True)
class Sleep: ms: int
@dataclass(frozen=True)
class Seq: parts: tuple
@dataclass(frozen=True)
class Loop: visits: int; body: object
@dataclass(frozen=True)
class Choose: choice: bool; yes: object; no: object

def syntax_sleeps(x):
    if isinstance(x,Sleep): return [x.ms]
    if isinstance(x,Seq): return sum((syntax_sleeps(p) for p in x.parts),[])
    if isinstance(x,Loop): return syntax_sleeps(x.body)
    if isinstance(x,Choose): return syntax_sleeps(x.yes)+syntax_sleeps(x.no)
    raise TypeError(x)

def visited_sleeps(x):
    if isinstance(x,Sleep): return [x.ms]
    if isinstance(x,Seq): return sum((visited_sleeps(p) for p in x.parts),[])
    if isinstance(x,Loop): return visited_sleeps(x.body)*x.visits
    if isinstance(x,Choose): return visited_sleeps(x.yes if x.choice else x.no)
    raise TypeError(x)

def sequential_timer_run(sleeps,adjustments):
    now=0; remaining=list(sleeps); deadline=(remaining.pop(0) if remaining else None)
    wakes=[]; finished_at=(0 if deadline is None else None)
    for delta in adjustments:
        assert delta>=0
        target=now+delta
        while deadline is not None and deadline<=target:
            now=deadline;wakes.append(now)
            if remaining: deadline=now+remaining.pop(0)
            else: deadline=None;finished_at=now
        now=target
    return {'finished_at':finished_at,'clock':now,'wakes':wakes,'next_deadline':deadline}

results=[]
def check(name,condition,inputs,observed):
    assert condition,name
    results.append({'name':name,'inputs':inputs,'observed':observed,'passed':True})
linear=Seq((Sleep(5),Sleep(5)))
loop=Loop(3,Sleep(5))
zero=Loop(0,Sleep(5))
conditional=Choose(True,Sleep(5),Sleep(20))
for name,p in [('linear_positive',linear),('repeated_loop',loop),('zero_visit_loop',zero),('selected_branch',conditional)]:
    static=syntax_sleeps(p);dynamic=visited_sleeps(p)
    expected={'linear_positive':True,'repeated_loop':False,'zero_visit_loop':False,'selected_branch':False}[name]
    check(name,(static==dynamic)==expected,repr(p),{'syntax':static,'visits':dynamic,'same':static==dynamic})
r=sequential_timer_run(visited_sleeps(linear),syntax_sleeps(linear))
check('linear_plan_finishes',r=={'finished_at':10,'clock':10,'wakes':[5,10],'next_deadline':None},{'sleeps':[5,5],'adjustments':[5,5]},r)
r=sequential_timer_run(visited_sleeps(loop),syntax_sleeps(loop))
check('loop_syntax_plan_leaves_wait',r=={'finished_at':None,'clock':5,'wakes':[5],'next_deadline':10},{'sleeps':[5,5,5],'adjustments':[5]},r)
r=sequential_timer_run(visited_sleeps(loop),[15])
check('one_advance_includes_newly_registered_due_sleeps',r=={'finished_at':15,'clock':15,'wakes':[5,10,15],'next_deadline':None},{'sleeps':[5,5,5],'adjustments':[15]},r)
r=sequential_timer_run([100,50],[1000])
check('root_time_differs_from_final_clock',r=={'finished_at':150,'clock':1000,'wakes':[100,150],'next_deadline':None},{'sleeps':[100,50],'adjustments':[1000]},r)
r=sequential_timer_run(visited_sleeps(conditional),syntax_sleeps(conditional))
check('unvisited_branch_can_advance_final_clock',r=={'finished_at':5,'clock':25,'wakes':[5],'next_deadline':None},{'chosen_sleeps':[5],'syntax_adjustments':[5,20]},r)
xs=[0,1,17,2**31,2**53,10**30]
check('ms_ns_additive_exact_integer_model',all((a+b)*10**6==a*10**6+b*10**6 for a in xs for b in xs),{'domain':xs,'pairs':36},'all36pairs')
check('ms_ns_order_exact_integer_model',all((a<=b)==(a*10**6<=b*10**6) for a in xs for b in xs),{'domain':xs,'pairs':36},'all36pairs')
check('unchanged_numeric_sleep_is_bad_migration_mutant',1*10**6 != 1,{'legacy_sleep_ms':1,'bad_new_ns':1},{'required_ns':1000000,'bad_ns':1})
check('same_source_point_not_same_loop_activation',len({(0,) for i in range(3)})==1 and len({('fiber0',(0,),i) for i in range(3)})==3,{'source_path':[0],'visits':3},{'source_points':1,'activation_observations':3})
out={'evidence':'finite independent Python models; not Lean evaluation, Effect execution, concurrency proof, target agreement, or a new defect classification','checks':len(results),'results':results}
Path(__file__).with_name('finite-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'passed':len(results),'scope':out['evidence']}))
