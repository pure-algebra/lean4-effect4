"""Finite mirror of the opened, positive-capacity, singleton suspend Queue profile.
No Lean execution, wrapper evaluation or host scheduling is performed.
"""
from dataclasses import dataclass, asdict, replace
from pathlib import Path
import json, platform

@dataclass(frozen=True)
class State:
    cap: int
    messages: tuple=()
    takers: tuple=()
    offers: tuple=()  # (request id, singleton message)

def wake(s):
    return [{'id':s.takers[0],'note':'again'}] if s.messages and s.takers else []

def offer(s,i,a):
    if s.offers:
        return replace(s,offers=s.offers+((i,a),)), 'wait', []
    if len(s.messages)<s.cap:
        s=replace(s,messages=s.messages+(a,))
        return s,'accepted true',wake(s)
    s=replace(s,offers=s.offers+((i,a),))
    return s,'wait',wake(s)

def take(s,i):
    earlier=s.takers[:s.takers.index(i)] if i in s.takers else s.takers
    if not s.messages or earlier:
        return (s if i in s.takers else replace(s,takers=s.takers+(i,))), 'wait', []
    got=s.messages[0]
    s=replace(s,messages=s.messages[1:],takers=tuple(t for t in s.takers if t!=i))
    answers=[]
    while s.offers and len(s.messages)<s.cap:
        oi,m=s.offers[0]
        s=replace(s,messages=s.messages+(m,),offers=s.offers[1:])
        answers.append({'id':oi,'note':'offered true'})
    return s, {'got':[got]},answers+wake(s)

def probe_post_order(signals):
    # QueueSteps.take posts the taker-hint list before the accepted-offer-answer list.
    return [x for x in signals if x['note']=='again']+[x for x in signals if x['note']=='offered true']

def corrected_post_order(signals):
    return [x for x in signals if x['note']=='offered true']+[x for x in signals if x['note']=='again']

checks=[]
def check(name,condition):
    assert condition,name
    checks.append(name)

s=State(1); prefix=[]
for op,args in [('take',(1,)),('take',(2,)),('offer',(100,1)),('offer',(101,2))]:
    s,reply,signals=(take if op=='take' else offer)(s,*args)
    prefix.append({'op':op,'args':args,'reply':reply,'signals':signals,'state':asdict(s)})
check('reachable prefix has ready first taker and one pending offer',s==State(1,(1,),(1,2),((101,2),)))
next_s,reply,signals=take(s,1)
check('consuming reply is one',reply=={'got':[1]})
check('acceptance keeps message two and the second taker',next_s==State(1,(2,),(2,),()))
check('model signals offer answer before taker wake',signals==[{'id':101,'note':'offered true'},{'id':2,'note':'again'}])
check('existing probe helper order differs',probe_post_order(signals)!=signals)
check('swapped postAll groups match model for this first profile',corrected_post_order(signals)==signals)
# Positive: taker hint only; both orders coincide.
p,_,_=take(State(1),1); p,r,taker_only=offer(p,100,1)
check('single taker hint positive',taker_only==[{'id':1,'note':'again'}] and probe_post_order(taker_only)==taker_only)
# Positive: acceptance answer only; the R4 shape has no second waiting taker.
p,_,_=offer(State(1),100,1); p,_,_=offer(p,101,2); p,r,offer_only=take(p,1)
check('single offer answer positive',offer_only==[{'id':101,'note':'offered true'}] and probe_post_order(offer_only)==offer_only)
# The probe's pending offer branch returns no taker hint, unlike the model's first full-buffer branch.
def concrete_offer_signals(s, a=2):
    if len(s.messages)<s.cap and not s.offers:
        return wake(replace(s,messages=s.messages+(a,)))
    return []
full=State(1,(1,),(1,2),())
_,_,full_signals=offer(full,101,2)
check('model repeats ready head hint on first full-buffer offer',full_signals==[{'id':1,'note':'again'}])
check('research pending offer omits this signal',concrete_offer_signals(full)==[] and concrete_offer_signals(full)!=full_signals)
no_takers=State(1,(1,),(),())
check('full buffer with no taker positive',offer(no_takers,101,2)[2]==concrete_offer_signals(no_takers)==[])
already_pending=State(1,(1,),(1,2),((101,2),))
check('earlier pending offer positive',offer(already_pending,102,3)[2]==concrete_offer_signals(already_pending)==[])
result={'evidence':'Finite Python mirror plus source comparison; no Lean run or host scheduling','python':platform.python_version(),'checked':checks,'reachable_prefix':prefix,'consuming_step':{'request':1,'reply':reply,'state':asdict(next_s),'model_signal_order':signals,'research_probe_post_order':probe_post_order(signals),'corrected_group_order':corrected_post_order(signals)},'full_buffer_offer':{'model':full_signals,'probe':concrete_offer_signals(full)},'positive_controls':{'taker_only':taker_only,'offer_only':offer_only}}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'checks_passed':len(checks),'model_signal_order':signals,'probe_post_order':probe_post_order(signals),'positive_controls':result['positive_controls'],'python':result['python']}))
