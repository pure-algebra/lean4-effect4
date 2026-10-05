"""Exercise the actual report validator without builds or repository writes."""
import copy,json,pathlib,sys
sys.dont_write_bytecode=True
sys.path.insert(0,'/Users/pooks/Dev/lean4-effect4/scripts/lib')
from conform_report import validate,InvalidReport

out=pathlib.Path(__file__).parent
def subject(n): return {'kind':'fixture','path':[n]}
def cid(n): return {'check':'scout.example','subject':subject(n)}
base={'format':'conform-report-v2','tool':'scout','pins':[{'name':'profile','value':'p1'}],
      'inputs':[{'name':'source','sha256':'0'*64}], 'expected':2,'required':[cid('a'),cid('b')],
      'rows':[{**cid(n),'outcome':'pass','evidence':'tested','message':'ok','detail':None} for n in ['a','b']],
      'summary':{'rows':2,'pass':2,'refused':0,'counterexample':0,'unresolved':0,'complete':True,'exit':0}}
checks=[]
def check(name,report,accepted,**options):
    try: verdict=validate(report,0,**options); result={'accepted':True,'exit':verdict}
    except InvalidReport as e: result={'accepted':False,'diagnostic':str(e)}
    assert result['accepted']==accepted,(name,result)
    checks.append({'name':name,'input':report,'options':options,'result':result})
ids=[('scout.example','fixture',(n,)) for n in ['a','b']]
check('valid independent expectations',copy.deepcopy(base),True,expected_ids=ids,expected_pins={'profile':'p1'},expected_inputs={'source':'0'*64})
r=copy.deepcopy(base);r['rows'].pop(); check('missing result without plan deletion',r,False)
r=copy.deepcopy(base);r['rows'].pop();r['required'].pop();r['expected']=1;r['summary']['rows']=r['summary']['pass']=1
check('plan and result shrink together without caller expectation',r,True)
check('caller expected identities detect shrink',r,False,expected_ids=ids)
r=copy.deepcopy(base);r['pins'][0]['value']='p2'
check('changed pin without caller expectation',r,True)
check('caller expected pin detects change',r,False,expected_pins={'profile':'p1'})
r=copy.deepcopy(base);r['inputs'][0]['sha256']='1'*64
check('changed digest without caller expectation',r,True)
check('caller expected digest detects change',r,False,expected_inputs={'source':'0'*64})
r=copy.deepcopy(base);r['rows'][0]['evidence']='proved';r['rows'][0]['detail']={'theorem':'NoSuchTheorem','proposition':'False','axioms':[]}
check('proof-shaped invented metadata passes schema',r,True)
r['rows'][0]['detail']['axioms']=['sorryAx'];check('disallowed axiom string rejected',r,False)
r['rows'][0]['detail']=None;check('missing proof metadata rejected',r,False)
ob={'kind':'made.up.kind','subject':subject('a'),'status':'unproved','dependsOn':['no-such-obligation'],'profile':'p1','statement':'Open statement','detail':None}
r=copy.deepcopy(base);r['obligations']=[ob]
check('unregistered kind and dangling dependency pass report schema',r,True)
check('present open obligation blocks require_closed',r,False,require_closed=True)
r['obligations']=[ob,copy.deepcopy(ob)];check('duplicate obligations pass schema',r,True)
r.pop('obligations');check('removed obligations pass require_closed',r,True,require_closed=True)
r=copy.deepcopy(base);r['rows'][0]['evidence']='verified';check('unknown evidence word rejected',r,False)
(out/'validator_probe.json').write_text(json.dumps({'scope':'actual scripts/lib/conform_report.py validate calls; schema checks, not Lean proof checking','checks':checks},indent=2)+'\n')
print(json.dumps({'checks':len(checks),'all_expected_results':True}))
