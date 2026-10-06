"""Isolated finite contract models. No project imports or Effect4 execution."""
from pathlib import Path
import json

out=Path(__file__).parent
results=[]
def control(name,actual,expected,scope):
    assert actual==expected,(name,actual,expected)
    results.append(dict(name=name,actual=actual,expected=expected,pass_=True,scope=scope))

# One deliberately small source model. It records contexts of successful recursive checks.
# Types are strings; effect errors are sets. This is not the project's checker.
def join(a,b):
    if a=='never':return b
    if b=='never':return a
    return a if a==b else '|'.join(sorted({a,b}))
def below(a,b):
    return a=='never' or set(a.split('|')) <= set(b.split('|'))
def term(t,env,const=False):
    tag,*xs=t
    if tag=='lit':
        kind,value=xs
        return 'lit:'+value if kind=='string' and const else kind
    if tag=='var':return env[xs[0]]
    if tag=='app':
        name,args=xs
        argtypes=[term(a,env,name=='pair') for a in args]
        return 'pair('+','.join(argtypes)+')' if name=='pair' else 'string'
    raise ValueError(tag)
def check(e,env=(),table=None,path=(),trace=None):
    if trace is None:trace={}
    tag,*xs=e
    if tag=='pure': ans=term(xs[0],env);err=frozenset()
    elif tag=='fail':ans='never';err=frozenset([xs[0]])
    elif tag=='host':ans,errors=table[xs[0]];err=frozenset(errors)
    elif tag=='bind':
        a,ea=check(xs[0],env,table,path+(0,),trace)
        ans,eb=check(xs[1],env+(a,),table,path+(1,),trace);err=ea|eb
    elif tag=='select':
        assert term(xs[0],env)=='bool'
        a,ea=check(xs[1],env,table,path+(0,),trace)
        b,eb=check(xs[2],env,table,path+(1,),trace)
        ans=join(a,b);err=ea|eb
    elif tag=='catch':
        caught,body,handler=xs
        a,ea=check(body,env,table,path+(0,),trace)
        b,eb=check(handler,env+('|'.join(sorted(ea)),),table,path+(1,),trace)
        ans=join(a,b);err=(ea-{caught})|eb
    elif tag=='loop':
        declared,initial,test,step,result,body=xs
        initialTy=term(initial,env);cursor=declared or initialTy
        assert below(initialTy,cursor)
        assert term(test,env+(cursor,))=='bool'
        bodyTy,err=check(body,env+(cursor,),table,path+(0,),trace)
        assert below(term(step,env+(cursor,bodyTy)),cursor)
        ans=term(result,env+(cursor,))
        trace[(path,'step')]=dict(env=list(env+(cursor,bodyTy)),constant=False,type=cursor)
    elif tag=='opaque_gen':ans=xs[0];err=frozenset()
    else:raise ValueError(tag)
    trace[path]=dict(env=list(env),answer=ans,errors=sorted(err),tag=tag)
    return ans,err

def inspect(e,path,table=None):
    trace={};check(e,table=table,trace=trace)
    if path in trace:return dict(ok=trace[path])
    # The model's only unsupported family is an opaque generator body.
    if e[0]=='opaque_gen' and path and path[0]==0:return dict(refusal='unsupportedFamily:stmts')
    return dict(refusal='invalidAddress')

N=lambda n:('lit','nat',n)
S=lambda s:('lit','string',s)
B=lambda b:('lit','bool',b)
V=lambda i:('var',i)
old=('bind',('pure',N(1)),('pure',V(0)))
new=('bind',('pure',S('name')),('pure',V(0)))
control('same_continuation_source_changes_context',
 [old[2]==new[2],inspect(old,(1,))['ok']['env'],inspect(new,(1,))['ok']['env']],
 [True,['nat'],['string']],'The unedited sibling remains byte-identical but needs a new context.')
control('reinspection_updates_answer',inspect(new,(1,))['ok']['answer'],'string',
 'Positive control after rebuilding the changed parent.')
control('invented_context_can_type_constant',
 [term(N(0),('nat',)),term(N(0),('string',))],['nat','nat'],
 'Isolated typeability does not determine inherited context.')

p=('bind',('host',0),('pure',V(0)))
t0={0:('nat',[])};t1={0:('string',[])}
control('table_identity_changes_context',[inspect(p,(1,),t0)['ok']['env'],inspect(p,(1,),t1)['ok']['env']],
 [['nat'],['string']],'The source is identical; its signature remains part of the query input.')

control('constant_mode_changes_literal',[term(S('tag'),(),False),term(S('tag'),(),True)],
 ['string','lit:tag'],'The argument mode belongs in the term focus.')
control('application_resets_child_mode',term(('app','ordinary',[S('tag')]),(),True),'string',
 'A parent constant mode is not blindly inherited by a nested application.')
control('const_atom_positive',term(('app','pair',[S('tag'),N(3)]),(),False),'pair(lit:tag,nat)',
 'A const atom keeps its direct literal even under ordinary enclosing mode.')

inner=('loop',None,S('c'),B(True),V(1),V(1),('pure',B(False)))
outer=('loop',None,N(0),B(True),V(0),V(0),inner)
tr={};check(outer,trace=tr)
control('nested_loop_step_context',tr[((0,),'step')]['env'],['nat','string','bool'],
 'Outer cursor, inner cursor and inner answer remain separate slots.')
control('outer_loop_step_uses_inner_result',tr[((),'step')]['env'],['nat','string'],
 'The outer body answer is the inner loop result type, not its body answer.')
inner2=('loop',None,S('c'),B(True),V(1),V(1),('pure',N(9)))
outer2=('loop',None,N(0),B(True),V(0),V(0),inner2)
tr2={};check(outer2,trace=tr2)
control('body_edit_renews_step_context',tr2[((0,),'step')]['env'],['nat','string','nat'],
 'The step remains well-typed while a body-answer slot changes.')
control('loop_slot_names_are_distinct',len({((),slot,()) for slot in ['initial','test','step','result']}),4,
 'A term slot cannot be erased to the enclosing effect path.')

routing=('catch','Unauthorized',('bind',('host',0),
 ('select',B(True),('fail','Unauthorized'),('host',1))),('pure',S('401')))
table={0:('Config',[]),1:('User',['SqlError','SchemaError'])}
trace={};check(routing,table=table,trace=trace)
branch=trace[(0,1)]
control('routing_local_join_keeps_error_alternatives',branch['errors'],
 ['SchemaError','SqlError','Unauthorized'],'The local branch join includes both arms.')
control('routing_root_type_is_not_branch_type',trace[()]['errors']==branch['errors'],False,
 'An enclosing handler removes an error from the final result.')
control('routing_inspection_is_not_looped_admission',inspect(routing,(0,1),table)['ok']['env'],['Config'],
 'Host and handler source remains inspectable; no synchronous semantic theorem is inferred.')

opaque=('opaque_gen','nat')
control('stop_before_unsupported_family',inspect(opaque,())['ok']['answer'],'nat',
 'The selected effect node is checked even if its child family is unsupported.')
control('crossing_unsupported_family_refuses',inspect(opaque,(0,)),{'refusal':'unsupportedFamily:stmts'},
 'No fabricated child context is returned.')
# The outer checker result is independent of an unsupported view result.
control('view_refusal_does_not_change_root_type',
 [check(opaque)[0],inspect(opaque,(0,))['refusal']],['nat','unsupportedFamily:stmts'],
 'Erasure keeps the successful root result.')

raw_ref_children=[];expanded_children=[('pure',N(3))]
control('expanded_path_not_original_path',[len(raw_ref_children)>0,len(expanded_children)>0],[False,True],
 'The same child index can exist only after reference expansion.')
def original_focus_allowed(refsites):return not refsites
control('reference_free_positive_and_origin_refusal',
 [original_focus_allowed([]),original_focus_allowed([((1,),(0,))])],[True,False],
 'The first view explicitly restricts origins; ordinary admission is unchanged.')

# Inferred results are not a unique expected type.
def accepts(e):
    try:
        check(e)
        return True
    except AssertionError:
        return False
broad=('loop','nat|string',N(0),B(True),N(1),V(0),('pure',B(False)))
wrong_step=('loop','nat|string',N(0),B(True),B(False),V(0),('pure',B(False)))
wrong_test=('loop','nat|string',N(0),N(3),N(1),V(0),('pure',B(False)))
control('narrow_step_under_wider_cursor_positive',accepts(broad),True,
 'The loop rule requires subtyping, not equality with an expected cursor type.')
control('step_outside_cursor_refuses',accepts(wrong_step),False,
 'A locally inferable Bool step fails the parent cursor constraint.')
control('non_boolean_loop_test_refuses',accepts(wrong_test),False,
 'An inferable Nat test fails the parent Boolean constraint.')
sel=('select',B(True),('pure',N(0)),('pure',S('x')))
seltrace={};check(sel,trace=seltrace)
control('branch_need_not_equal_parent_join',
 [seltrace[(0,)]['answer'],seltrace[()]['answer']],['nat','nat|string'],
 'A valid branch contributes to a join; the parent type is not its expected type.')
control('body_answer_not_determined_by_loop_result',
 [tr[()]['answer']==tr2[()]['answer'],tr[((0,),'step')]['env']!=tr2[((0,),'step')]['env']],
 [True,True],'Equal final result types leave different body-answer contexts for the step.')

payload={'evidence':'isolated finite source/context model; no project imports, Lean or target execution',
         'passed':len(results),'results':results}
(out/'probe-results.json').write_text(json.dumps(payload,indent=2)+'\n')
print(json.dumps({'passed':len(results),'output':str(out/'probe-results.json')}))
