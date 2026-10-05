"""Exercise actual fresh_run in scratch; the producer is a tiny Python fixture."""
import json,pathlib,sys
sys.dont_write_bytecode=True
sys.path.insert(0,'/Users/pooks/Dev/lean4-effect4/scripts/lib')
from conform_report import fresh_run,InvalidReport
out=pathlib.Path(__file__).parent;checks=[]
for mode,accepted in [('both',True),('removed-report-tag',True),('bad-report-tag',False),('missing-file',False)]:
    cmd=[sys.executable,str(out/'producer_fixture.py'),'{out}',mode]
    try:
        code=fresh_run(cmd,out/'runs'/f'{mode}.json',['one.json','two.json'],cwd=out,input_snapshot=lambda:{'fixture-input':'fixed'})
        r={'accepted':True,'exit':code}
    except InvalidReport as e:r={'accepted':False,'diagnostic':str(e)}
    assert r['accepted']==accepted,(mode,r)
    checks.append({'mode':mode,'result':r})
(out/'fresh_run_probe.json').write_text(json.dumps({'scope':'actual fresh_run; only Python producers in scratch','checks':checks},indent=2)+'\n')
print(json.dumps({'checks':len(checks),'all_expected_results':True}))
