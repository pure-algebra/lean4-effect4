"""Finite independent mirrors; no Lean, host engine, or compiler is executed."""
from dataclasses import dataclass
from itertools import product
import json

@dataclass(frozen=True)
class S:
    machine: int = 0
    pending: int | None = None
    journal: tuple = ()

def row(s,c):
    # The tape uses the pre-row decision; a frontier may already mutate the machine.
    phase,d,reads,m,p='ok',None,True,s.machine,s.pending
    if c=='step': d=1;m+=1
    elif c=='receive': p=7
    elif c=='apply':
        if p is not None: d=p;m+=p;p=None
    elif c=='frontier': phase='frontier';m+=100
    elif c=='unread': d=1000;reads=False;m+=1000
    elif c=='conditional':
        if m%2: phase='frontier';m+=10
        else: d=2;m+=2
    elif c!='skip': raise AssertionError(c)
    return phase,d,reads,S(m,p,s.journal+(c,))

def play(s,cs):
    for c in cs:s=row(s,c)[3]
    return s

def tape(s,cs):
    if not cs:return (),()
    c,*rest=cs;rest=tuple(rest)
    phase,d,reads,after=row(s,c)
    if phase=='frontier' or (d is not None and not reads):return (),tuple(cs)
    ps,left=tape(after,rest)
    return (((d,after),)+ps if d is not None else ps),left

def raw(s,ps):return s.machine+sum(d for d,_ in ps)

alphabet=('step','receive','apply','frontier','unread','conditional','skip')
count=0;split_count=0
for initial in (S(),S(1),S(2,5,('older',))):
 for n in range(5):
  for cs in product(alphabet,repeat=n):
   ps,left=tape(initial,cs);done=cs[:len(cs)-len(left)]
   assert cs==done+left and tape(initial,done)==(ps,())
   assert play(initial,done).machine==raw(initial,ps)
   # Every position, even if a later row stops, is the corresponding replay prefix.
   for i,(_,after) in enumerate(ps):assert after.machine==raw(initial,ps[:i+1])
   for k in range(n+1):
    a,b=cs[:k],cs[k:];pa,la=tape(initial,a)
    if not la:
     pb,lb=tape(play(initial,a),b);want=(pa+pb,lb)
    else:want=(pa,la+b)
    assert tape(initial,cs)==want
    split_count+=1
   count+=1
# Red controls: include stopped row or its mutated state, skip session receipt when applying.
s=S();ps,left=tape(s,('step','frontier','step'));done=('step',)
assert play(s,done).machine != play(s,done+left[:1]).machine
assert raw(s,ps) != play(s,done+left[:1]).machine
assert tape(s,('receive','apply'))[0] != tape(s,('apply',))[0]
assert play(s,('step','frontier')).machine != play(s,('step',)).machine

@dataclass(frozen=True)
class N:
    kind:str='layer'
    children:tuple=()
    target:tuple=()

def ref(t):return N('ref',(),tuple(t))
def branch(*xs):return N('layer',tuple(xs))
def at(root,path):
 for i in path:
  if i>=len(root.children):return None
  root=root.children[i]
 return root

def sites(root,p=()):
 out=[(p,root.target)] if root.kind=='ref' else []
 for i,c in enumerate(root.children):out+=sites(c,p+(i,))
 return out

def proper(a,b):return len(a)<len(b) and b[:len(a)]==a

def wf(root):return all(t<s and not proper(t,s) and at(root,t) is not None and at(root,t).kind!='ref' for s,t in sites(root))
def round_(orig,n):
 if n.kind=='ref':return at(orig,n.target) or n
 return N(n.kind,tuple(round_(orig,c) for c in n.children),n.target)
def rounds(root,n):
 result=root
 for _ in range(n):result=round_(root,result)
 return result
leaf=branch()
fixtures={
 'empty':branch(leaf),
 'one':branch(leaf,ref((0,))),
 'nested':branch(leaf,branch(ref((0,))),branch(ref((1,))),ref((2,))),
 'diamond_count_growth':branch(leaf,branch(ref((0,)),ref((0,)),ref((0,))),ref((1,)),ref((1,)),ref((1,))),
 'nested_sibling_target':branch(branch(leaf,branch(ref((0,0))),ref((0,1))),ref((0,)))
}
exp=[]
for name,root in fixtures.items():
 assert wf(root)
 refs=sites(root);n=len(refs)
 # Each referenced target's nested ref site occurs earlier than the original caller site.
 for s,t in refs:
  for q,_ in sites(at(root,t),t):assert q<s
 assert not sites(rounds(root,n))
 assert not sites(rounds(root,n+1))
 counts=[len(sites(rounds(root,i))) for i in range(n+2)]
 exp.append({'name':name,'original_sites':n,'counts':counts})
assert exp[3]['counts'][:3]==[6,9,0]
invalid={
 'enclosing_self':branch(branch(ref((0,)))),
 'forward':branch(ref((1,)),leaf),
 'ref_target':branch(leaf,ref((0,)),ref((1,))),
 'missing':branch(ref((7,)))
}
assert all(not wf(r) for r in invalid.values())
assert sites(rounds(invalid['enclosing_self'],8))
print(json.dumps({'evidence':'finite independent Python mirrors; not a Lean proof','tape_lists':count,'append_splits':split_count,'tape_laws':'all passed','red_controls':'stopped row/post-state and receipt omission rejected','expansion':exp,'rejected_reference_shapes':list(invalid)},indent=2))
