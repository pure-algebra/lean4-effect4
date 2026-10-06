"""Finite Python mirrors of named source branches. No Effect execution or Lean proof."""
import json
from collections import OrderedDict
checks=[]
def check(name, condition, observation):
    assert condition, (name,observation)
    checks.append({'name':name,'pass':True,'observation':observation})
# Selection occurs when the posted task runs, before callbacks resume.
waiters=['A','B']; waiters.append('C'); selected=waiters[:2]
check('snapshot-hint-selection-positive', selected==['A','B'], {'notifications':selected,'resource_grants':[]})
# A removes B and enrols D during resumed code; a previously selected B still has a delivery.
live=['A','B']; fixed=live[:2]; delivered=[]
for x in fixed:
    delivered.append(x)
    if x=='A': live[:]=['D']
check('snapshot-not-live-mutant',delivered==['A','B'] and delivered!=['A','D'],delivered)
pre=['A']; post=pre+['B'];check('selection-time-positive',post[:2]==['A','B'],post[:2])
check('selection-at-post-mutant',pre[:2]!=post[:2],{'post':pre[:2],'task':post[:2]})
# Healthy return only adjusts lease accounting; invalidated last return destroys item.
def release(refs,invalid):
    after=refs-1
    return after, bool(invalid and after==0)
check('healthy-lease-return',release(1,False)==(0,False),release(1,False))
check('invalidated-last-return',release(1,True)==(0,True),release(1,True))
check('invalidated-held-positive',release(2,True)==(1,False),release(2,True))
# Explicit recency order differs from lexical order and from write-recency.
def touch(m,k):
    v=m.pop(k); m[k]=v
m=OrderedDict([('a',1),('z',2)]);touch(m,'a');m['b']=3;oldest=next(iter(m))
check('read-touch-vs-lexical',oldest=='z' and sorted(m)[0]=='a',{'recency':list(m),'lexical':sorted(m)})
n=OrderedDict([('z',1),('a',2)]);n['z']=9;n['b']=3
check('existing-write-no-touch',next(iter(n))=='z',list(n))
check('sorted-map-mutant',sorted(n)[0]!=next(iter(n)),{'canonical':sorted(n)[0],'insertion':next(iter(n))})
p=OrderedDict([('z',1),('a',2)]);_='z' in p;check('has-no-touch',list(p)==['z','a'],list(p))
# Old cleanup must compare entry identity. Key equality alone deletes a replacement.
entries={'k':'new'};old='old'
if entries.get('k')==old:entries.pop('k')
check('old-cleanup-preserves-replacement',entries=={'k':'new'},entries.copy())
mutant=entries.copy();mutant.pop('k',None)
check('key-only-cleanup-mutant',mutant!=entries,mutant)
entries={'k':'old'}
if entries.get('k')=='old':entries.pop('k')
check('matching-cleanup-positive',entries=={},entries)
# Capacity removes membership, not pending work owned by existing awaiters.
cache=OrderedDict([('a','lookup-A')]);running={'lookup-A'};cache['b']='lookup-B';running.add('lookup-B');cache.popitem(last=False)
check('eviction-keeps-old-lookup',list(cache)==['b'] and running=={'lookup-A','lookup-B'},{'keys':list(cache),'running':sorted(running)})
print(json.dumps({'evidence':'finite Python source mirrors; not runtime evidence','checks':checks,'count':len(checks)},indent=2))
