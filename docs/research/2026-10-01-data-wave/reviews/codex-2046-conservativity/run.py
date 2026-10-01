from pathlib import Path
import subprocess,json,hashlib,time
out=Path(__file__).parent
fixture=out/'fixture'
fixture.mkdir(exist_ok=True)
def git(*args):
 return subprocess.check_output(['git','-C',str(fixture),*args],stderr=subprocess.STDOUT,text=True).strip()
git('init','-q')
files={'Makefile':'GENERATED_PATHS := tools/Effect4Gen/wire-tags.json\n','tools/Effect4Gen/wire-tags.json':'{"families":{"T":{"active":{"a":0},"retired":{}}}}\n','Test/fixtures/baseline/66ee4657-supplement-v1.policy.json':'{}\n','Test/fixtures/baseline/66ee4657/families.json':'{"families":{}}\n','ocaml/eff/goldens/example.json':'{"retained":true}\n'}
for name,value in files.items():
 p=fixture/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(value)
git('add',*files)
git('-c','user.name=Independent Review','-c','user.email=review@localhost','commit','-qm','Isolated compatibility fixture')
base=git('rev-parse','HEAD')
(fixture/'ocaml/eff/goldens/example.json').write_text('{"retained":false}\n')
git('add','ocaml/eff/goldens/example.json')
git('-c','user.name=Independent Review','-c','user.email=review@localhost','commit','-qm','Deliberate golden drift')
changed=git('rev-parse','HEAD')
checks=[('valid-same',[base,base],0),('golden-drift',[base,changed],1),('invalid-both',['no-such-review-base','no-such-review-candidate'],None),('invalid-both-strict',['no-such-review-base','no-such-review-candidate','--strict'],None)]
results=[]
for name,args,want in checks:
 start=time.monotonic()
 r=subprocess.run(['python3',str(out/'conservativity.py'),*args],cwd=fixture,capture_output=True,text=True,timeout=20)
 (out/(name+'.log')).write_text(r.stdout+r.stderr)
 results.append({'name':name,'command':['python3',str(out/'conservativity.py'),*args],'cwd':str(fixture),'exit':r.returncode,'seconds':round(time.monotonic()-start,3),'expected':want})
 print(name,r.returncode,r.stdout.splitlines()[-1] if r.stdout else r.stderr[-200:])
 if want is not None:assert r.returncode==want,(name,r.stdout,r.stderr)
assert all(x['exit']==0 for x in results if x['name'].startswith('invalid-both')),results
(out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
