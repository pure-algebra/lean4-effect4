from pathlib import Path
import hashlib,json,subprocess,time
repo=Path('/Users/pooks/.codex/worktrees/unguard/lean4-effect4')
out=Path('/private/tmp/codex-unguard/p2b-row/metadata-control');out.mkdir(exist_ok=True)
checker=repo/'tools/target/checker.ts';original=checker.read_text()
s=original.replace('../../ts/eff/node_modules/',str(repo/'ts/eff/node_modules')+'/').replace('"./oracle.ts"',json.dumps(str(repo/'tools/target/oracle.ts')))
needle='const measuredTypes = checker.getTypeAtLocation(typeNodes)'
assert s.count(needle)==1
replacement=needle+'''.map((type, index) => {
      const node = typeNodes[index]!
      const file = node.getSourceFile().fileName
      const binding = node.getText()
      // Fault injection at the API response boundary; positive q0 remains actual.
      return (file.endsWith("/q1.ts") && binding === "__A_actual") ||
        (file.endsWith("/q2.ts") && binding === "__A_expected") ? undefined : type
    })'''
s=s.replace(needle,replacement)
script=out/'checker-api-missing.ts';script.write_text(s)
source='Test/fixtures/target/controls.ts'
base={'source':source,'imports':['import type * as C from '+json.dumps(str(repo/source))],
 'subject':'typeof C.program','kind':'effect','expected':{'A':'number','E':'"E1"','R':'C.R1'}}
request=out/'request.json';request.write_text(json.dumps({'repo':str(repo),'profile':'finite API metadata absence control',
 'queries':[{**base,'id':name} for name in ['real-positive','missing-actual-type','missing-expected-type']]},indent=2)+'\n')
response=out/'report.json'
command=['node',str(script),str(request),str(response)]
start=time.monotonic();result=subprocess.run(command,cwd=repo,text=True,capture_output=True,timeout=300)
(out/'compiler.log').write_text(result.stdout+result.stderr)
metadata={'command':command,'cwd':str(repo),'exit':result.returncode,'elapsedSeconds':time.monotonic()-start,
 'compiler':'@typescript/native-preview','version':json.loads((repo/'ts/eff/node_modules/@typescript/native-preview/package.json').read_text())['version'],
 'injection':'Only q1 actual A and q2 expected A API results become undefined. q0 retains the real compiler types.',
 'checkerSHA256':hashlib.sha256(checker.read_bytes()).hexdigest(),'controlSourceSHA256':hashlib.sha256(script.read_bytes()).hexdigest()}
(out/'command.json').write_text(json.dumps(metadata,indent=2)+'\n')
assert result.returncode==0,(result.stdout,result.stderr)
r=json.loads(response.read_text());observations=r['observations']
assert observations[0]['status']=='agree' and observations[0]['diagnostics']==[]
for observation,side in zip(observations[1:],['actual','expected']):
 assert observation['status']=='refused' and observation['diagnostics']==[]
 assert observation['columns']['A']['agreement'] is None
 assert observation['columns']['A']['actualToExpected'] is None
 assert any(issue['code']=='missing-type-metadata' and issue['axis']=='A' and side in issue['message'] for issue in observation['issues'])
assert r['conforms'] is False and r['globalDiagnostics']==[]
summary={'compiler':metadata['version'],'realPositive':observations[0]['status'],
 'missingActual':observations[1]['status'],'missingExpected':observations[2]['status'],'allDiagnosticsEmpty':True,'conforms':r['conforms']}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
