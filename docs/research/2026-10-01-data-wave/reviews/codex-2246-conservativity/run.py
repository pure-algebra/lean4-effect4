from pathlib import Path
import subprocess,json,time,sys
out=Path(__file__).resolve().parent
fixture=out/'fixture'
fixture.mkdir(exist_ok=True)
def git(*args):
    return subprocess.check_output(['git','-C',str(fixture),*args],stderr=subprocess.STDOUT,text=True).strip()
def commit(message):
    git('-c','user.name=Independent Review','-c','user.email=review@localhost','commit','-qm',message)
    return git('rev-parse','HEAD')
git('init','-q')
files={'Makefile':'GENERATED_PATHS := tools/Effect4Gen/wire-tags.json\n','tools/Effect4Gen/wire-tags.json':'{"families":{"T":{"active":{"a":0},"retired":{}}}}\n','Test/fixtures/baseline/66ee4657-supplement-v1.policy.json':'{}\n','Test/fixtures/baseline/66ee4657/families.json':'{"families":{"T":{"constructors":["a"]}}}\n','ocaml/eff/goldens/example.json':'{"retained":true}\n'}
for name,value in files.items():
    p=fixture/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(value)
git('add',*files)
base=commit('Isolated compatibility fixture')
(fixture/'ocaml/eff/goldens/example.json').write_text('{"retained":false}\n')
git('add','ocaml/eff/goldens/example.json')
changed=commit('Deliberate golden drift')
(fixture/'ocaml/eff/goldens/example.json').write_text(files['ocaml/eff/goldens/example.json'])
(fixture/'ocaml/eff/goldens/added.json').write_text('{"new":true}\n')
git('add','ocaml/eff/goldens/example.json','ocaml/eff/goldens/added.json')
restored=commit('Restore golden and add previously absent vector')
checks=[('valid-same',[base,base],0,None),('valid-same-strict',[base,base,'--strict'],0,None),('golden-drift',[base,changed],1,'C1 goldens: REFUSE')]
for label,args,names in [('invalid-base',['no-such-review-base',base],['no-such-review-base']),('invalid-candidate',[base,'no-such-review-candidate'],['no-such-review-candidate']),('invalid-both',['no-such-review-base','no-such-review-candidate'],['no-such-review-base','no-such-review-candidate'])]:
    for strict in (False,True):
        checks.append((label+('-strict' if strict else ''),args+(['--strict'] if strict else []),1,names))
checks.append(('restored-and-absent-historical-addition',[base,restored,'--strict'],0,None))
results=[]
for name,args,want,reason in checks:
    start=time.monotonic()
    cmd=[sys.executable,str(out/'conservativity.py'),*args]
    p=subprocess.run(cmd,cwd=fixture,capture_output=True,text=True,timeout=20)
    text=p.stdout+p.stderr
    (out/(name+'.log')).write_text(text)
    good=p.returncode==want
    if isinstance(reason,list):good=good and all(repr(n) in text for n in reason) and 'resolve to a commit' in text and 'PASS' not in text
    elif reason:good=good and reason in text
    results.append({'name':name,'command':cmd,'cwd':str(fixture),'exit':p.returncode,'expected':want,'correct_reason':good,'seconds':round(time.monotonic()-start,3)})
    print(name,p.returncode,'ok' if good else 'WRONG')
(out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
assert all(x['correct_reason'] for x in results),results
