"""Finite Python mirrors of four selected Queue.Model branches, not a Lean check.
No repository code is executed. Unsupported poll branches fail explicitly.
"""
from dataclasses import dataclass,field,replace,asdict
from pathlib import Path
import json,hashlib
@dataclass
class State:
    messages:list=field(default_factory=list)
    capacity:int|None=1
    strategy:str='suspend'
    takers:list=field(default_factory=list) # (id,min,max)
    peekers:list=field(default_factory=list)
    offers:list=field(default_factory=list) # (id,batch,rest)
    awaiters:list=field(default_factory=list)
    phase:str='opened'
@dataclass
class Run:
    s:State
    signalled:list=field(default_factory=list)
    ok:bool=True
    named:bool=True

def room(s):return None if s.capacity is None else max(s.capacity-len(s.messages),0)
def threshold(s,n):return 1 if s.phase=='closing' else n if s.capacity is None else min(n,1 if s.capacity==0 else s.capacity)
def rendezvous(s):return s.capacity==0 and s.phase!='done' and bool(s.offers)
def ready(s,n):return bool(s.messages) and threshold(s,n)<=len(s.messages) or rendezvous(s)
def front(s):return s.messages[0] if s.messages else (s.offers[0][2][0] if rendezvous(s) and s.offers[0][2] else None)
def within(s):return s.capacity is None or len(s.messages)<=s.capacity
def tidy(s):
    phase_ok=not(s.messages or s.takers or s.peekers or s.offers or s.awaiters) if s.phase=='done' else bool(s.messages or s.offers) if s.phase=='closing' else True
    return phase_ok and (not s.offers or room(s)==0)
def quiet(s,signalled):return (not s.takers or not ready(s,s.takers[0][1]) or s.takers[0][0] in signalled) and (front(s) is None or all(i in signalled for i in s.peekers))
def waiting(s):return [t[0] for t in s.takers]+s.peekers+[o[0] for o in s.offers]+s.awaiters
def accounted(before,after,self_id,signals):return all(i in waiting(after) or self_id==i or any(j==i for j,_ in signals) for i in waiting(before))
def wake(s):return ([(s.takers[0][0],'again')] if s.takers and ready(s,s.takers[0][1]) else [])+([(i,'again') for i in s.peekers] if front(s) is not None else [])
def bump(r,s,self_id,signals):
    kept=[i for i in r.signalled if i!=self_id] if self_id is not None else r.signalled
    now=kept+[i for i,n in signals if n=='again']
    return Run(s,now,r.ok and within(s) and tidy(s) and quiet(s,now),r.named and accounted(r.s,s,self_id,signals))
def first_profile(s):
    ti=[t[0] for t in s.takers];oi=[o[0] for o in s.offers]
    return s.phase=='opened' and s.strategy=='suspend' and s.capacity is not None and s.capacity>0 and all(t[1:]==(1,1) for t in s.takers) and all(not o[1] and len(o[2])==1 for o in s.offers) and not s.peekers and not s.awaiters and len(ti)==len(set(ti)) and len(oi)==len(set(oi)) and not(set(ti)&set(oi))
def first_op(op):return op in ['dropTake','poll'] # only operations implemented below

def step(r,op,arg=99,fault='none'):
    s=r.s
    if op=='dropTake':
        nxt=replace(s,takers=[t for t in s.takers if t[0]!=arg])
        return bump(r,nxt,arg,wake(nxt))
    if op=='poll':
        assert s.phase=='done' or not ready(s,1) or s.takers, 'Only the exact no-op poll arm is mirrored'
        return bump(r,s,None,[])
    if op=='close':
        assert s.phase=='opened'
        nxt=replace(s,phase='closing');signals=[]
        if not(s.messages or s.offers):
            nxt=replace(nxt,phase='done',takers=[],peekers=[],awaiters=[])
            signals=[(t[0],'again') for t in s.takers]+[(i,'again') for i in s.peekers]+[(i,'over') for i in s.awaiters]
        signals+=wake(nxt)
        return bump(r,nxt,None,[] if fault=='closing' else signals)
    if op=='shutdown':
        assert s.phase!='done'
        nxt=replace(s,messages=[],offers=[],takers=[],peekers=[],awaiters=[],phase='done')
        signals=[(t[0],'again') for t in s.takers]+[(i,'again') for i in s.peekers]+[(o[0],'left' if o[1] else 'offered') for o in s.offers]+[(i,'over') for i in s.awaiters]
        return bump(r,nxt,None,[] if fault=='shutdown' else signals)
    raise ValueError(op)

def observe(r):return dict(firstProfile=first_profile(r.s),within=within(r.s),tidy=tidy(r.s),quiet=quiet(r.s,r.signalled),ok=r.ok,named=r.named)
results=[]
def control(name,red,positive,op,missing):
    assert first_op(op) and first_profile(red.s) and first_profile(positive.s)
    before=observe(red);out=step(red,op);good=step(positive,op)
    assert before[missing] is False and all(before[k] for k in before if k!=missing)
    assert not(out.ok and out.named) and good.ok and good.named
    results.append(dict(name=name,kind='omitted premise finite branch mirror',operation=op,argument=99,input=asdict(red),input_observation=before,result=asdict(out),positive_input=asdict(positive),positive_result=asdict(good),missing=missing,requested=True))
control('within is independent',Run(State(messages=[7,8],capacity=1)),Run(State(messages=[7],capacity=1)),'dropTake','within')
control('tidy is independent',Run(State(capacity=2,offers=[(2,False,[8])])),Run(State(messages=[7,9],capacity=2,offers=[(2,False,[8])])),'dropTake','tidy')
control('quiet is independent',Run(State(messages=[7],takers=[(5,1,1)])),Run(State(messages=[7],takers=[(5,1,1)]),signalled=[5]),'poll','quiet')
control('old ok flag is sticky',Run(State(),ok=False),Run(State()),'dropTake','ok')
control('old named flag is sticky',Run(State(),named=False),Run(State()),'dropTake','named')
for op,r,flag in [('close',Run(State(messages=[7],capacity=2,takers=[(5,2,2)])),'ok'),('shutdown',Run(State(messages=[7],offers=[(2,False,[8])])),'named')]:
    before=observe(r);assert all(before[k] for k in ['within','tidy','quiet','ok','named'])
    good=step(r,op,fault='none');bad=step(r,op,fault='closing' if op=='close' else 'shutdown')
    assert good.ok and good.named and not getattr(bad,flag) and not first_op(op)
    results.append(dict(name=op+' omitted signal control',kind='broader operation domain, not firstOp',operation=op,input=asdict(r),input_observation=before,positive_result=asdict(good),mutant_result=asdict(bad),failed_flag=flag,firstOp=False))
p=Path(__file__).parent
out=dict(evidence='Finite Python mirrors of selected source branches; no Lean elaboration, repository model execution, or universal preservation proof',source_model_sha256=hashlib.sha256((p/'source/src/Effect4/Laws/Modules/Queue/Model.lean').read_bytes()).hexdigest(),source_profile_sha256=hashlib.sha256((p/'source/src/Effect4/Laws/Modules/Queue/Profile.lean').read_bytes()).hexdigest(),cases=results)
(p/'witness-results.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: 5 omitted-premise witnesses and 2 out-of-profile fault controls; every case has a passing positive control.')
