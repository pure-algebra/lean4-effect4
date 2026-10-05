"""Small literal mirrors of the named QueueContract transition fragments.
No Lean execution; no whole-model equivalence claim.
"""
from dataclasses import dataclass, replace
import hashlib, json, platform
from pathlib import Path

CAP = 1_000_000
CHECKS = 0

def check(condition, message):
    global CHECKS
    CHECKS += 1
    assert condition, message

@dataclass(frozen=True)
class Offer:
    id: int
    batch: bool
    rest: tuple

@dataclass(frozen=True)
class State:
    messages: tuple = ()
    capacity: int | None = None
    strategy: str = 'suspend'
    takers: tuple = ()  # (id, min, max)
    peekers: tuple = ()
    offers: tuple = ()
    awaiters: tuple = ()
    phase: tuple = ('opened',)

def room(s):
    return CAP if s.capacity is None else max(0, s.capacity-len(s.messages))

def front(s):
    if s.messages:
        return s.messages[0]
    if s.capacity == 0 and s.phase[0] != 'done' and s.offers:
        return s.offers[0].rest[0] if s.offers[0].rest else None
    return None

def ready(s, minimum):
    threshold = 1 if s.phase[0] == 'closing' else minimum if s.capacity is None else min(minimum, 1 if s.capacity == 0 else s.capacity)
    return bool(s.messages and len(s.messages) >= threshold) or bool(s.capacity == 0 and s.phase[0] != 'done' and s.offers)

def wake(s):
    sig = [(s.takers[0][0], ('again',))] if s.takers and ready(s, s.takers[0][1]) else []
    if front(s) is not None:
        sig += [(i, ('again',)) for i in s.peekers]
    return sig

def answer(o, rest):
    return ('left', rest) if o.batch else ('offered', not rest)

def offer(s, id, a):
    if s.phase[0] != 'opened': return s, ('accepted', False), []
    if s.strategy == 'suspend' and s.offers:
        return replace(s, offers=s.offers+(Offer(id, False, (a,)),)), ('wait',), []
    if room(s) > 0:
        n = replace(s, messages=s.messages+(a,))
        return n, ('accepted', True), wake(n)
    assert s.strategy == 'suspend'  # Only the branch used by this bounded probe.
    n = replace(s, offers=s.offers+(Offer(id, False, (a,)),))
    return n, ('wait',), wake(n)

def offer_all(s, id, ms):
    if not ms: return s, ('left', ()), []
    if s.phase[0] != 'opened': return s, ('left', ms), []
    assert s.strategy == 'suspend'
    if s.offers:
        return replace(s, offers=s.offers+(Offer(id, True, ms),)), ('wait',), []
    k = min(room(s), len(ms)); rest = ms[k:]
    n = replace(s, messages=s.messages+ms[:k])
    if not rest: return n, ('left', ()), wake(n)
    n = replace(n, offers=n.offers+(Offer(id, True, rest),))
    return n, ('wait',), wake(n)

def accept(s):
    budget = room(s); msgs = s.messages; offers = list(s.offers); sig=[]
    while offers and budget:
        o = offers[0]; k = min(budget, len(o.rest))
        msgs += o.rest[:k]; left = o.rest[k:]; budget -= k
        if left:
            offers[0] = replace(o, rest=left); break
        offers.pop(0); sig.append((o.id, answer(o, ())))
    return replace(s, messages=msgs, offers=tuple(offers)), sig

def settle(s):
    if s.phase[0] == 'closing' and not s.messages and not s.offers:
        e=s.phase[1]
        sig=[(t[0], ('again',)) for t in s.takers]+[(p, ('again',)) for p in s.peekers]+[(a, ('over', e)) for a in s.awaiters]
        return replace(s, phase=('done',e), takers=(), peekers=(), awaiters=()), sig
    return s, []

def pull(s, maximum):
    if s.messages:
        return s.messages[:maximum], replace(s, messages=s.messages[maximum:]), []
    if not s.offers: return (), s, []
    o, *others=s.offers
    if not o.rest: return (), replace(s, offers=tuple(others)), []
    m, *more=o.rest
    if not more: return (m,), replace(s, offers=tuple(others)), [(o.id, answer(o, ()))]
    return (m,), replace(s, offers=(replace(o, rest=tuple(more)),)+tuple(others)), []

def clear(s):
    if s.phase[0] == 'done':
        return s, ('got',()) if s.phase[1]=='ended' else ('stopped',s.phase[1]), []
    if s.takers or front(s) is None: return s, ('got',()), []
    got, p, a = pull(s,CAP)
    q, b=accept(p); r,c=settle(q)
    return r, ('got',got), a+b+c+wake(r)

def shutdown(s):
    if s.phase[0]=='done': return s, False, []
    end=s.phase[1] if s.phase[0]=='closing' else 'interrupted'
    sig=[(t[0],('again',)) for t in s.takers]+[(p,('again',)) for p in s.peekers]+[(o.id,answer(o,o.rest)) for o in s.offers]+[(a,('over',end)) for a in s.awaiters]
    return replace(s,messages=(),offers=(),takers=(),peekers=(),awaiters=(),phase=('done',end)), True, sig

def within(s): return s.capacity is None or len(s.messages)<=s.capacity

def tidy(s):
    phase_ok=(not(s.messages or s.offers or s.takers or s.peekers or s.awaiters) if s.phase[0]=='done' else bool(s.messages or s.offers) if s.phase[0]=='closing' else True)
    return phase_ok and (not s.offers or room(s)==0)

def quiet(s, signalled):
    return (not s.takers or not ready(s,s.takers[0][1]) or s.takers[0][0] in signalled) and (front(s) is None or all(p in signalled for p in s.peekers))

def abstract_check(s, signals):
    signalled=[id for id,note in signals if note[0]=='again']
    return within(s) and tidy(s) and quiet(s,signalled)

# Literal boundary; explicit unbounded state has no stated input-length restriction.
ms=tuple(range(CAP+1))
small, reply, _=offer_all(State(),100,ms[:CAP])
check(reply==('left',()) and len(small.messages)==CAP and not small.offers, 'boundary positive control')
large, reply, _=offer_all(State(),100,ms)
check(reply==('wait',) and len(large.messages)==CAP and large.offers[0].rest==(CAP,), 'unbounded batch artificial wait')
check(not tidy(large) and room(large)==CAP, 'reachable tidy violation')
# Same buffer length reached entirely through immediately accepted offers.
large_buffer, single, _=offer(small,101,CAP)
check(single==('accepted',True) and tidy(large_buffer), 'reachable buffer positive control')
cleared_small, sr, _=clear(small)
check(sr==('got',ms[:CAP]) and not cleared_small.messages, 'clear positive control')
cleared_large, lr, _=clear(large_buffer)
check(len(lr[1])==CAP and cleared_large.messages==(CAP,), 'clear truncation')

# Capacity-zero clear: empty control versus one pending offer.
empty, empty_reply, empty_sig=clear(State(capacity=0))
check(empty_reply==('got',()) and empty_sig==[], 'empty rendezvous clear control')
waiting, waiting_reply, _=offer(State(capacity=0),100,10)
check(waiting_reply==('wait',) and not waiting.messages and len(waiting.offers)==1, 'rendezvous offer enrolls')
cleared, cr, cs=clear(waiting)
check(cr==('got',(10,)) and cs==[(100,('offered',True))] and not cleared.offers, 'clear accepts rendezvous message')

# Reachable empty queue: take(1,1,1), peek(5), awaitQ(7), then shutdown.
# Each enrollment only appends that request when front is empty.
terminal_input=State(takers=((1,1,1),),peekers=(5,),awaiters=(7,))
check(tidy(terminal_input) and quiet(terminal_input,[]), 'reachable enrollment state')
done, _, signals=shutdown(terminal_input)
check(signals==[(1,('again',)),(5,('again',)),(7,('over','interrupted'))], 'terminal positive control names every request')
check(abstract_check(done, signals), 'terminal positive control satisfies search properties')
check(abstract_check(done, []), 'deliberate signal-deletion mutant escapes all three search properties')

source=Path('/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-05-claude-lead/queue-contract/QueueContract.lean')
text=source.read_text()
check(sum(11**i for i in range(6))==177156, 'search-prefix count')
check(sum(line.startswith('#guard ') for line in text.splitlines())==32, 'source guard count')
output={
 'evidence':'Finite Python mirrors of named transition fragments; no Lean execution or mirror equivalence theorem',
 'python':platform.python_version(),'checks':CHECKS,'modelSHA256':hashlib.sha256(source.read_bytes()).hexdigest(),
 'unboundedBatch':{'inputCount':len(ms),'reply':reply,'bufferCount':len(large.messages),'pendingCounts':[len(o.rest) for o in large.offers],'room':room(large),'tidy':tidy(large)},
 'clear':{'inputCount':len(large_buffer.messages),'outputCount':len(lr[1]),'remaining':cleared_large.messages,'positiveInputCount':len(small.messages),'positiveRemaining':len(cleared_small.messages)},
 'rendezvousClear':{'initialBuffer':waiting.messages,'initialPending':waiting.offers[0].rest,'reply':cr,'signals':cs,'remainingOffers':len(cleared.offers)},
 'terminalSearchLimit':{'reachablePrefix':['take 1 1 1','peek 5','awaitQ 7','shutdown'],'actualSignals':signals,'positiveSearchCheck':abstract_check(done,signals),'mutantSignals':[],'mutantSearchCheck':abstract_check(done,[])},
 'searchScope':{'sourceGuardCommands':32,'namedControlsBeforeExploration':28,'searchConfigurationGuards':3,'redControlGuards':1,'operations':11,'maximumDepth':5,'prefixCountPerConfiguration':sum(11**i for i in range(6)),'configurations':8,'note':'Count and retained outputs inspected; exploration not rerun. Fixed IDs and fixed take/offer parameters. No awaitQ/dropPeek/dropAwait operation; closed reason only ended.'}
}
print(json.dumps(output,indent=2))
