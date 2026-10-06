"""Finite opacity-definition controls; neither runtime probe nor a general checker."""
import itertools, json

def legal_order(order, transactions, before=()):
    if any(order.index(a) >= order.index(b) for a,b in before): return False
    store={'x':0,'y':0}
    for name in order:
        ops,commit=transactions[name]
        local=store.copy()
        for op,key,value in ops:
            if op=='write': local[key]=value
            elif local[key]!=value: return False
        if commit: store=local
    return True

def serializations(ts,before=()):
    return [list(o) for o in itertools.permutations(ts) if legal_order(o,ts,before)]
writer=([('write','x',1),('write','y',1)],True)
cases=[]
def check(name,ts,expected,before=()):
    orders=serializations(ts,before)
    assert bool(orders)==expected,(name,orders)
    cases.append({'name':name,'legal_serial_order_exists':bool(orders),'orders':orders})
check('mixed read across writer, then abort',{'C':writer,'T':([('read','x',0),('read','y',1)],False)},False)
check('coherent read before writer, then abort',{'C':writer,'T':([('read','x',0),('read','y',0)],False)},True)
check('coherent read after writer, then abort',{'C':writer,'T':([('read','x',1),('read','y',1)],False)},True)
check('own tentative write may break x=y while visible to self',{'T':([('write','x',1),('read','x',1),('read','y',0)],False)},True)
check('aborted write is not visible to next transaction',{'A':([('write','x',1)],False),'T':([('read','x',1)],True)},False)
check('aborted write discarded positive',{'A':([('write','x',1)],False),'T':([('read','x',0)],True)},True)
check('real time prohibits old read after writer completes',{'C':writer,'T':([('read','x',0)],False)},False,(('C','T'),))
check('real time allows new read after writer completes',{'C':writer,'T':([('read','x',1)],False)},True,(('C','T'),))
print(json.dumps({'kind':'finite history model, not Effect execution or Lean proof','cases':cases,'passed':len(cases)},indent=2))
