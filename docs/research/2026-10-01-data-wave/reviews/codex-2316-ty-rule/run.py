from pathlib import Path
import subprocess,json,os,sys,time
out=Path(__file__).resolve().parent
script=out/'scripts/check-ty-rule.py'
green=(out/'Test/fixtures/ty-rule/census-green.log').read_text()
results=[]
def run(name,args,want,env=None):
    cmd=[sys.executable,str(script),*map(str,args)]
    start=time.monotonic()
    p=subprocess.run(cmd,cwd=out,capture_output=True,text=True,env=env,timeout=15)
    (out/(name+'.log')).write_text(p.stdout+p.stderr)
    result={'name':name,'command':cmd,'expected_exit':want,'actual_exit':p.returncode,'seconds':round(time.monotonic()-start,3)}
    if env:result['fake_lake_mode']=env['PROBE_LAKE_MODE']
    results.append(result)
    print(name,'expected',want,'actual',p.returncode)
for name,text,want in [('green',green,0),('deliberate-violation',green.replace('  fold\t','  structural\t',1),1),('empty','',2),('compiler-error-only','error: unknown module prefix Effect4\n',2),('missing-gate-section',green.split('#exhaustive_gate',1)[0],2)]:
    path=out/(name+'.input.log');path.write_text(text)
    run(name,[path],want)
run('self-test',['--self-test'],0)
for mode,want in [('ok',0),('main-fails-after-output',2),('one-mirror-fails-silently',2)]:
    env=dict(os.environ, PATH=str(out/'fake-bin')+os.pathsep+os.environ['PATH'],PROBE_LAKE_MODE=mode)
    run('tree-'+mode,['--tree','--logs',out/('tree-'+mode)],want,env)
(out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
assert all(x['actual_exit']==x['expected_exit'] for x in results[:7]),results
assert [x['actual_exit'] for x in results[-2:]]==[0,0],results
