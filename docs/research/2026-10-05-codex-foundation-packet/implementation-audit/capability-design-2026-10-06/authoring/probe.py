"""Finite, independent models of proposed API contracts. No project imports."""
import json
from pathlib import Path

results=[]
def check(name, actual, expected, scope):
    assert actual == expected, (name, actual, expected)
    results.append({'name':name,'actual':actual,'expected':expected,'pass':True,'scope':scope})

# Positional bind: answers append to the environment, as the source denotation does.
def run(e, env=()):
    tag,*args=e
    if tag=='lit': return args[0]
    if tag=='var': return env[args[0]]
    if tag=='bind': return run(args[1],env+(run(args[0],env),))
    if tag=='suspend': return run(args[0],env)
    raise ValueError(tag)
p,q,r=('lit',1),('lit',2),('var',0)
check('raw_bind_reassociation_changes_result',
      [run(('bind',('bind',p,q),r)),run(('bind',p,('bind',q,r)))],[2,1],
      'Pure mirror of absolute variables; no general bind reassociation.')
check('raw_bind_suspension_positive',run(('bind',p,('suspend',('var',0)))),1,
      'Administrative suspension leaves the same selected input.')

old_env=('Ada',); new_env=('trace-7','Ada')
old_types=('string',);new_types=('string','string')
check('same_typed_slot_is_not_same_input',
      [old_types[0]==new_types[0],old_env[0]==new_env[0]],[True,False],
      'Rechecking same-typed stored syntax cannot infer intent.')
check('inserted_slot_shift_positive',new_env[1],old_env[0],
      'A correct one-slot weakening preserves the selected value.')

outer=(100,); cursor=5; answer=7
step_env=outer+(cursor,answer)
check('loop_cursor_and_answer_are_distinct', [step_env[1],step_env[2]],[5,7],
      'Both can be Nat; type equality cannot identify their roles.')
check('loop_inserted_outer_slot_positive',
      (99,)+step_env, (99,100,5,7),
      'Inserting an outer slot moves cursor and answer together.')
loop_parts=('initial','test','step','result')
plain_addresses=[(2,0) for _ in loop_parts]
tagged_addresses=[((2,0),p,()) for p in loop_parts]
check('plain_node_path_aliases_loop_terms',len(set(plain_addresses)),1,
      'Loop pure terms live at the parent node, not distinct Node children.')
check('tagged_term_slots_positive',len(set(tagged_addresses)),4,
      'A separate slot distinguishes the four pure terms.')

# Isolated finite loop approximation. One budget unit observes its test and takes one step.
# Store writes survive a frontier. False test finishes; no project runtime is called.
def body_run(body, store):
    if body[0]=='inc': return store+body[1]
    if body[0]=='suspend': return body_run(body[1],store)
    if body[0]=='noop': return store
    raise ValueError(body[0])

def approx(k, limit, delta, wrapped=False):
    cursor=store=0
    for _ in range(k):
        if cursor>=limit: return {'exit':store,'store':store}
        body=('inc',delta)
        if wrapped: body=('suspend',body)
        store=body_run(body,store)
        cursor+=1
    return {'exit':None,'store':store}
check('equal_finished_loop_results', [approx(3,2,1),approx(3,1,2)],
      [{'exit':2,'store':2},{'exit':2,'store':2}],
      'Two spellings can converge to the same exit and complete store.')
check('equal_finished_results_do_not_imply_budget_equality',
      [approx(1,2,1),approx(1,1,2)],
      [{'exit':None,'store':1},{'exit':None,'store':2}],
      'A completed-result relation does not preserve unfinished stores.')
check('termination_boundary_can_differ', [approx(2,2,1),approx(2,1,2)],
      [{'exit':None,'store':2},{'exit':2,'store':2}],
      'Equal store is not equal completion status at a fixed budget.')
check('suspension_cleanup_budget_positive',
      all(approx(k,n,d)==approx(k,n,d,True) for k in range(5) for n in range(4) for d in (1,2)),
      True,'Finite control of a budget-transparent rewrite; not a proof for Effect4.')

# Runtime frame arrows carry more than lexical context. An empty type at w0 is not
# empty after allocation. Checking only w0 vacuously accepts a bad continuation.
def contract(allocated, continuation):
    incoming=range(allocated)
    return all(isinstance(continuation(i),int) and not isinstance(continuation(i),bool) for i in incoming)
bad=lambda _:'not-a-number'; good=lambda _:0
check('one_world_frame_contract_can_be_vacuous', [contract(0,bad),contract(1,bad)], [True,False],
      'Finite allocation mirror of the need for later-world quantification.')
check('later_world_positive',all(contract(n,good) for n in (0,1,2)),True,
      'A good continuation meets each sampled later-world demand.')

# Identical program syntax does not identify the operation table used to type it.
program=('perform-external',0)
tables=(('nat',),('string',))
check('program_identity_without_signature_is_insufficient',
      [program==program,tables[0][program[1]]==tables[1][program[1]]],[True,False],
      'A typed focus must bind both source and signature.')
check('program_and_signature_positive',len({(program,t) for t in tables}),2,
      'Including the signature distinguishes the two typing inputs.')

# Structural reference expansion duplicates occurrences, while a target identity remains one.
target=(0,);sites=((1,),(2,));relative=(0,)
check('reference_definition_is_not_occurrence_identity',len({target for _ in sites}),1,
      'A target-only address loses which expanded occurrence was selected.')
check('reference_occurrence_positive',len({(s,target,relative) for s in sites}),2,
      'Explicit occurrence origin can retain both selections without new program syntax.')

out=Path(__file__).with_name('probe-results.json')
out.write_text(json.dumps({'kind':'isolated finite Python model controls; no Lean or project runtime',
  'passed':len(results),'results':results},indent=2)+'\n')
print(json.dumps({'passed':len(results),'result':str(out)}))
