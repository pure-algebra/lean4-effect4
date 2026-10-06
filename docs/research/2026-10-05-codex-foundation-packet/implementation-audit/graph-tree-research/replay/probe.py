"""Finite list-algebra mirrors of storeReply and retire, not a session runner."""
import itertools,json
from pathlib import Path

def store_reply(slots, key, value):
    return [(k,value if k==key else old) for k,old in slots]

def retire(active,pending,old_retired,live):
    dead=[k for k in active if k not in live]
    def read(k):
        return next((v for key,v in pending if key==k),None)
    return ([k for k in active if k in live],[(k,v) for k,v in pending if k not in dead],old_retired+[(k,read(k)) for k in dead])

results=[]
def check(name, value):
    assert value,name
    results.append(name)

slots=[(0,None),(1,None),(2,None)]
answers=[(0,'a'),(1,'b'),(2,'c')]
for order in itertools.permutations(answers):
    got=slots
    for k,v in order: got=store_reply(got,k,v)
    check('distinct receipt permutation '+str([k for k,_ in order]),got==answers)
check('same key different payload does not commute',store_reply(store_reply(slots,0,'a'),0,'b') != store_reply(store_reply(slots,0,'b'),0,'a'))
def mutant(slots,k,v): return [(key,v) for key,_ in slots]
check('write-all-slots mutation fails distinct receipt commutation',mutant(mutant(slots,0,'a'),1,'b') != mutant(mutant(slots,1,'b'),0,'a'))
for mask in range(8):
    live={k for k in range(3) if mask & (1<<k)}
    for payloads in itertools.product([None,'reply'],repeat=3):
        initial=([0,1,2],list(zip(range(3),payloads)),[(9,'previous')])
        once=retire(*initial,live)
        twice=retire(*once,live)
        check('retire idempotence live='+str(mask)+' payloads='+str(payloads),once==twice)
        assert len(once[0])+len(once[2])-1==3
        assert once[2][0]==(9,'previous')
        assert once[2][1:]==[(k,payloads[k]) for k in range(3) if k not in live]
initial=([0],[(0,'reply')],[])
once=retire(*initial,set())
mutated=(initial[0],once[1],once[2])
check('keeping dead active bindings defeats retirement idempotence',retire(*mutated,set())!=mutated)
out={'checks':len(results),'all_passed':True,'scope':'Finite direct mirrors of list update and retirement only; no preflight, admission, machine execution, Lean proof or target execution. Raw input states, not asserted reachable runs.','results':results}
Path(__file__).with_name('probe-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='results'},indent=2))
