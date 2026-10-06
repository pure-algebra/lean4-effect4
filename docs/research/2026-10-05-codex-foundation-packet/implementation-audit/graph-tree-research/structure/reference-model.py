"""Bounded abstract mirror of Refs paths/WF/expansion; not Lean or Effect execution."""
from itertools import product
import json
from pathlib import Path

# All constructors here stand for layer constructors. Child indices retain source order.
def leaf(): return ('leaf',)
def ref(path): return ('ref',tuple(path))
def pair(a,b): return ('pair',a,b)
def wrap(a): return ('wrap',a)
def children(n): return [] if n[0] in ('leaf','ref') else list(n[1:])
def at(n,p):
    for i in p:
        cs=children(n)
        if i>=len(cs): return None
        n=cs[i]
    return n
def sites(n,p=()):
    return [(p,n[1])] if n[0]=='ref' else [x for i,c in enumerate(children(n)) for x in sites(c,p+(i,))]
def paths(n,p=()): return [p]+[q for i,c in enumerate(children(n)) for q in paths(c,p+(i,))]
def prefix(a,b): return len(a)<len(b) and b[:len(a)]==a
def wf(n,guard_ancestor=True):
    return all(t<s and (not guard_ancestor or not prefix(t,s)) and at(n,t) is not None and at(n,t)[0]!='ref' for s,t in sites(n))
def expand_round(n,orig):
    if n[0]=='ref': return at(orig,n[1]) or n
    if n[0]=='leaf': return n
    return (n[0],*(expand_round(c,orig) for c in children(n)))
def expand(n):
    r=n
    for _ in range(len(sites(n))+1): r=expand_round(r,n)
    return r
def replace_leaves(n,choices,it=None):
    if it is None: it=iter(choices)
    if n[0]=='leaf':
        p=next(it);return leaf() if p is None else ref(p)
    return (n[0],*(replace_leaves(c,choices,it) for c in children(n)))

shapes=[pair(pair(leaf(),leaf()),pair(leaf(),leaf())),pair(leaf(),wrap(pair(leaf(),leaf())))]
counts={'candidates':0,'well_formed':0,'failed_reference_elimination':0}
for s in shapes:
    leaves=sum(at(s,p)[0]=='leaf' for p in paths(s))
    for assignments in product([None]+paths(s),repeat=leaves):
        n=replace_leaves(s,assignments);counts['candidates']+=1
        if wf(n):
            counts['well_formed']+=1
            counts['failed_reference_elimination']+=bool(sites(expand(n)))
assert counts['well_formed']>0 and counts['failed_reference_elimination']==0
# Independent inhabited positive: two references to the same earlier definition.
shared=pair(leaf(),pair(ref((0,)),ref((0,))))
assert wf(shared) and not sites(expand(shared))
# A later definition containing a reference can itself be referenced.
nested=pair(pair(leaf(),wrap(ref((0,0)))),ref((0,)))
assert wf(nested) and not sites(expand(nested))
# A true dependency diamond: later target D refers to B and C, both of which refer to A.
diamond=('many',leaf(),wrap(ref((0,))),wrap(ref((0,))),pair(ref((1,)),ref((2,))),ref((3,)))
assert wf(diamond) and not sites(expand(diamond))
# Copying one target three times grows occurrence count in the first round.
multiplicity=('many',leaf(),('many',ref((0,)),ref((0,)),ref((0,))),ref((1,)),ref((1,)),ref((1,)))
assert wf(multiplicity) and not sites(expand(multiplicity))
assert len(sites(expand_round(multiplicity,multiplicity)))>len(sites(multiplicity))
def dependency_control(n):
    original=sites(n)
    source_paths=sorted(s for s,t in original)
    ranks={s:i for i,s in enumerate(source_paths)}
    edges=[]
    depth={}
    for source,target in sorted(original):
        dependencies=[source_path for source_path,_ in sites(at(n,target),target)]
        assert all(d in ranks and ranks[d]<ranks[source] for d in dependencies)
        depth[source]=1+max([depth[d] for d in dependencies],default=0)
        edges.extend([[list(source),list(d)] for d in dependencies])
    bound=max(depth.values(),default=0)
    expanded=n
    counts=[len(sites(expanded))]
    for _ in range(bound):
        expanded=expand_round(expanded,n)
        counts.append(len(sites(expanded)))
    assert not sites(expanded) and bound<=len(original)
    return {'original_sites':len(original),'edges_from_dependent_to_original_source':edges,
            'dependency_depth_bound':bound,'round_reference_counts':counts}
controls={name:dependency_control(n) for name,n in [('shared',shared),('nested',nested),('diamond',diamond),('multiplicity',multiplicity)]}
# Removing the non-enclosing condition admits self-dependency through a non-ref ancestor.
cycle=pair(leaf(),wrap(ref((1,))))
assert not wf(cycle) and wf(cycle,False) and sites(expand(cycle))
# Lex order on arbitrary finite paths is not well founded in its descending direction.
chain=[(0,)*i+(1,) for i in range(8)]
assert all(b<a for a,b in zip(chain,chain[1:]))
result={'scope':'abstract layer-only Python mirror; no repository runtime or Lean execution',
 'counts':counts,'shared_target_positive':True,'nested_definition_positive':True,'diamond_positive':True,'dependency_controls':controls,
 'ancestor_guard_mutant':{'passes_weakened_wf':wf(cycle,False),'passes_current_wf':wf(cycle),'remaining_refs':sites(expand(cycle))},
 'strict_lex_descending_chain':chain,'claims':'finite controls only; proposed Lean theorem remains unproved'}
Path(__file__).with_name('reference-model-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
