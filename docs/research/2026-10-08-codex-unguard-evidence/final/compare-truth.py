import json,hashlib
from pathlib import Path
root=Path('/Users/pooks/.codex/worktrees/unguard/lean4-effect4')
baseline=Path('/private/tmp/codex-unguard/pre-final-truth')
checks=[]
for filename,key,identity in [('corpus.json','programs','name'),('result.json','rows','program')]:
 old=json.loads((baseline/filename).read_text()); new=json.loads((root/'harness/truth'/filename).read_text())
 previous={row[identity]:row for row in old[key]}; current={row[identity]:row for row in new[key]}
 checks.append(dict(check=filename+' original identities retained',passed=set(previous)<=set(current)))
 added=set(current)-set(previous)
 checks.append(dict(check=filename+' exactly four additions',passed=added=={'pJoinedFirstNumber','pJoinedFirstString','pJoinedModifyNumber','pJoinedModifyString'},added=sorted(added)))
 for name,row in previous.items():
  checks.append(dict(check=filename+' unchanged '+name,passed=current.get(name)==row))
 if filename=='result.json':
  for name in sorted(added):
   row=current[name]
   checks.append(dict(check=name+' exit schedule sync agreement',passed=all(row.get(k) is True for k in ['exitAgree','scheduleAgree','runSyncAgree'])))
for oldfile,newfile in [('corpus-index.tsv','generated/corpus-index.tsv'),('corpus-results.tsv','harness/truth/corpus-results.tsv'),('tsdiag-agreement.tsv','generated/tsdiag-agreement.tsv')]:
 a=(baseline/oldfile).read_bytes(); b=(root/newfile).read_bytes()
 checks.append(dict(check=newfile+' frozen bytes',passed=a==b,sha256=hashlib.sha256(b).hexdigest()))
failed=[r for r in checks if not r['passed']]
result=dict(checks=checks,passed=len(checks)-len(failed),failed=len(failed))
Path('/private/tmp/codex-unguard/final-checks/truth-comparison.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(passed=result['passed'],failed=failed),indent=2))
raise SystemExit(bool(failed))
