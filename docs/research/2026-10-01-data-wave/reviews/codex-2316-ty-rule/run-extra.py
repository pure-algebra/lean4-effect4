from pathlib import Path
import subprocess,sys,os,json,time
out=Path(__file__).resolve().parent
script=out/'scripts/check-ty-rule.py'
fixture=out/'Test/fixtures/ty-rule/CensusMirrorsToolsVariances.lean'
suppressed=out/'temporarily-omitted-CensusMirrorsToolsVariances.lean'
results=json.loads((out/'results.json').read_text())
env=dict(os.environ,PATH=str(out/'fake-bin')+os.pathsep+os.environ['PATH'],PROBE_LAKE_MODE='ok')
def run(name,want):
    cmd=[sys.executable,str(script),'--tree','--logs',str(out/name)]
    p=subprocess.run(cmd,cwd=out,env=env,capture_output=True,text=True,timeout=15)
    (out/(name+'.log')).write_text(p.stdout+p.stderr)
    results.append({'name':name,'command':cmd,'expected_exit':want,'actual_exit':p.returncode,'fake_lake_mode':'ok','omitted_fixture':str(fixture) if want==2 else None})
    print(name,'expected',want,'actual',p.returncode)
    return p.returncode
fixture.rename(suppressed)
try:
    missing=run('tree-missing-one-mirror-fixture',2)
finally:
    suppressed.rename(fixture)
restored=run('tree-restored-mirror-fixture',0)
(out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
assert missing==0 and restored==0
