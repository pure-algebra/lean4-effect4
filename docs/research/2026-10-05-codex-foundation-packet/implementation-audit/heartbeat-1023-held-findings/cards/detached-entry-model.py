from copy import deepcopy
import json

def leave_current_only(state, stamp):
    for e in state['entries']:
        if e['stamp'] == stamp:
            e['awaiters'] -= 1
            return e['awaiters'] == 0 and e['pending']
    return None  # the card supplies no detached-entry owner

def leave_retained(state, stamp):
    e = state['live'][stamp]
    e['awaiters'] -= 1
    return e['awaiters'] == 0 and e['pending']

rows=[]
for detach in ['none', 'evict', 'invalidate', 'replace']:
    for readers in [1,2,3]:
        old={'stamp':0,'awaiters':readers,'pending':True}
        s={'entries':[old.copy()], 'live':{0:old.copy()}}
        if detach != 'none': s['entries']=[]
        if detach == 'replace':
            s['entries']=[{'stamp':1,'awaiters':1,'pending':True}]
            s['live'][1]=s['entries'][0].copy()
        expected=[False]*(readers-1)+[True]
        current=[leave_current_only(s,0) for _ in range(readers)]
        retained=[leave_retained(s,0) for _ in range(readers)]
        assert retained==expected
        assert current==(expected if detach=='none' else [None]*readers)
        if detach=='replace': assert s['live'][1]['awaiters']==1 and s['entries'][0]['awaiters']==1
        rows.append({'detach':detach,'readers':readers,'expected_interrupts':expected,'current_only':current,'retained_entry':retained})
# A completed lookup needs no interruption when its last reader leaves.
s={'live':{0:{'awaiters':1,'pending':False}}}
assert leave_retained(s,0) is False
print(json.dumps({'evidence':'finite design model; not Lean or Effect execution','cases':rows,'completed_lookup_positive':True},indent=2))
