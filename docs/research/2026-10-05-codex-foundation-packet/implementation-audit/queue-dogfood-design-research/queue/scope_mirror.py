# Pure Python mirror of Names.resolve, Env.push and two QueueSteps helper bodies.
# It is not a Lean elaboration or a machine run.
import json
def resolve(names,x):
    acc=None
    for i,y in enumerate(names):
        if y==x: acc=i
    return acc
def enrolled(outer_name,outer_id,items,internal="e_t"):
    names=[outer_name,"e_acc",internal]
    level=resolve(names,outer_name)
    answer=False
    for item in items:
        env=[{"id":outer_id},answer,{"id":item}]
        answer=answer or env[2]["id"]==env[level]["id"]
    return answer,level
def remove(outer_name,outer_id,items,internal="r_t"):
    names=[outer_name,"r_acc",internal]
    level=resolve(names,outer_name)
    kept=[]
    for item in items:
        env=[{"id":outer_id},kept,{"id":item}]
        if env[2]["id"] != env[level]["id"]: kept=kept+[item]
    return kept,level
cases=[
 ("enrolled_collision",enrolled("e_t",1,[2]),(True,2)),
 ("enrolled_plain_control",enrolled("caller",1,[2]),(False,0)),
 ("enrolled_matching_control",enrolled("caller",2,[2]),(True,0)),
 ("enrolled_reserved_control",enrolled("e_t",1,[2],"_%foldItem1"),(False,0)),
 ("remove_collision",remove("r_t",1,[2,3]),([],2)),
 ("remove_plain_control",remove("caller",1,[2,3]),([2,3],0)),
 ("remove_matching_control",remove("caller",2,[2,3]),([3],0)),
 ("remove_reserved_control",remove("r_t",1,[2,3],"_%foldItem1"),([2,3],0))
]
for name,actual,expected in cases:
    assert actual==expected,(name,actual,expected)
intended={"enrolled_collision":False,"enrolled_plain_control":False,"enrolled_matching_control":True,"enrolled_reserved_control":False,"remove_collision":[2,3],"remove_plain_control":[2,3],"remove_matching_control":[3],"remove_reserved_control":[2,3]}
print(json.dumps({"evidence":"Python name-resolution mirror; not Lean elaboration", "checks":len(cases),"results":[{"name":n,"actual":a,"expected_current_behavior":e,"intended_semantics":intended[n]} for n,a,e in cases],"collision_witnesses_differ_from_intended":["enrolled_collision","remove_collision"]},indent=2))
