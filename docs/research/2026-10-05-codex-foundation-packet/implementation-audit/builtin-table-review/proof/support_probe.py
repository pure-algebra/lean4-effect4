"""Finite mirror of the named-call/closure branches in Target.evalT/applyT/applyNamed.

This is not execution of Lean or OCaml. It checks concrete proposed assembly assumptions.
"""
import json
from pathlib import Path

def V(x): return ('value',x)
FUEL=('outOfFuel',)
def find(env,n):
    for k,v in env:
        if k==n: return v
    return None
def ev(prog,fuel,env,e):
    if not fuel: return FUEL
    fuel-=1
    op=e[0]
    if op in ('int','bool'): return V(e[1])
    if op=='fail': return ('exn',e[1])
    if op=='if':
        c=ev(prog,fuel,env,e[1])
        return ev(prog,fuel,env,e[2] if c[1] else e[3]) if c[0]=='value' else c
    if op=='var':
        v=find(env,e[1])
        if v is not None: return V(v)
        if e[1] in prog:
            ps,body=prog[e[1]]
            return ev(prog,fuel,[],body) if not ps else V(('papp',e[1],[]))
        return ('stuck','unbound '+e[1])
    if op=='fn': return V(('closure',e[1],e[2],env,None))
    if op=='letrec':
        ext=env[:]
        for n,ps,b in e[1]: ext=[(n,('closure',ps,b,env,n))]+ext
        return ev(prog,fuel,ext,e[2])
    if op=='app':
        vals=ea(prog,fuel,env,e[2])
        if vals[0]!='value': return vals
        f=e[1]
        if f[0]=='var':
            v=find(env,f[1])
            return ap(prog,fuel,v,vals[1]) if v is not None else an(prog,fuel,f[1],vals[1])
        fv=ev(prog,fuel,env,f)
        return ap(prog,fuel,fv[1],vals[1]) if fv[0]=='value' else fv
    raise ValueError(op)
def ea(prog,fuel,env,es):
    if not fuel: return FUEL
    if not es: return V([])
    a=ev(prog,fuel-1,env,es[0])
    if a[0]!='value': return a
    rest=ea(prog,fuel-1,env,es[1:])
    return V([a[1]]+rest[1]) if rest[0]=='value' else rest
def ap(prog,fuel,f,vs):
    if not fuel: return FUEL
    fuel-=1
    if not vs: return V(f)
    if f[0]=='papp': return an(prog,fuel,f[1],f[2]+vs)
    _,ps,b,captured,selfname=f
    selfbind=[(selfname,f)] if selfname else []
    if len(vs)==len(ps): return ev(prog,fuel,list(zip(ps,vs))+selfbind+captured,b)
    if len(vs)<len(ps): return V(('closure',ps[len(vs):],b,list(zip(ps,vs))+selfbind+captured,None))
    g=ev(prog,fuel,list(zip(ps,vs))+selfbind+captured,b)
    return ap(prog,fuel,g[1],vs[len(ps):]) if g[0]=='value' else g
def an(prog,fuel,n,vs):
    if not fuel: return FUEL
    fuel-=1
    if n not in prog: return ('stuck','unbound '+n)
    ps,b=prog[n]
    if len(ps)==len(vs): return ev(prog,fuel,list(zip(ps,vs)),b)
    if len(vs)<len(ps): return V(('papp',n,vs))
    g=ev(prog,fuel,list(zip(ps,vs)),b)
    return ap(prog,fuel,g[1],vs[len(ps):]) if g[0]=='value' else g
I=lambda n:('int',n)
N=lambda n:('var',n)
A=lambda f,*xs:('app',N(f),list(xs))
checks=[]
def check(name,got,expected):
    assert got==expected,(name,got,expected)
    checks.append({'name':name,'actual':got,'expected':expected,'passed':True})
check('inline caller global',ev({},30,[('max_int',63)],N('max_int')),V(63))
p={'helper':(['x'],N('max_int'))}
check('named helper drops caller environment',ev(p,30,[('max_int',63)],A('helper',I(0))),('stuck','unbound max_int'))
check('declared profile global restores helper',ev({**p,'max_int':([],I(63))},30,[],A('helper',I(0))),V(63))
check('local closure captures caller global',ev({},30,[('max_int',63)],('app',('fn',['x'],N('max_int')),[I(0)])),V(63))
check('inline one unit of fuel',ev({},1,[],I(7)),V(7))
check('named helper same fuel is frontier',ev({'helper':(['x'],I(7))},1,[],A('helper',I(0))),FUEL)
check('named helper enough fuel',ev({'helper':(['x'],I(7))},10,[],A('helper',I(0))),V(7))
local=('letrec',[('f',['x'],A('g',N('x'))),('g',['y'],N('y'))],A('f',I(7)))
check('local mutual helper has no sibling binding',ev({},30,[],local),('stuck','unbound g'))
check('top level helper graph resolves sibling',ev({'f':(['x'],A('g',N('x'))),'g':(['y'],N('y'))},30,[],A('f',I(7))),V(7))
check('strict call retains failing unused argument',ev({},30,[],('app',('fn',['x'],I(7)),[('fail','boom')])),('exn','boom'))
check('affine zero use drops failing argument',ev({},30,[],I(7)),V(7))
conditional=('if',('bool',False),N('x'),I(7))
check('strict call evaluates argument before branch',ev({},30,[],('app',('fn',['x'],conditional),[('fail','boom')])),('exn','boom'))
check('one affine use in unselected branch skips argument',ev({},30,[],('if',('bool',False),('fail','boom'),I(7))),V(7))
check('total value argument positive control',ev({},30,[],('app',('fn',['x'],conditional),[I(99)])),V(7))
Path(__file__).with_suffix('.json').write_text(json.dumps({'scope':'finite Python mirror; not Lean or OCaml execution','checks':checks},indent=2)+'\n')
print(json.dumps({'passed':len(checks),'scope':'finite named-call/closure mirror'}))
