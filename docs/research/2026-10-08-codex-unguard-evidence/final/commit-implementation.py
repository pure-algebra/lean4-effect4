import hashlib, json, subprocess
from pathlib import Path
r=Path('/Users/pooks/.codex/worktrees/unguard/lean4-effect4')
o=Path('/private/tmp/codex-unguard/final-checks')
required=['test-final','proof-status-final','printer-final','check-cases','check-proof-style','check-ts-reader','check-truth','check-target-final','check-corpus','check-tsdiag','check-ingest']
for name in required:
 record=json.loads((o/(name+'.json')).read_text())
 assert record['exit_code']==0 and record['protected_unchanged'], name
 assert hashlib.sha256((o/(name+'.log')).read_bytes()).hexdigest()==record['log_sha256'], name
for row in json.loads(Path('/private/tmp/codex-unguard/protected-baseline.json').read_text())['paths']:
 assert hashlib.sha256((r/row['path']).read_bytes()).hexdigest()==row['base_sha256'],row['path']
rows=json.loads(Path('/private/tmp/codex-unguard/final-implementation-files.json').read_text())
paths=[row['path'] for row in rows]
for row in rows:
 assert hashlib.sha256((r/row['path']).read_bytes()).hexdigest()==row['sha256'],row['path']
def git(*args):return subprocess.check_output(['git',*args],cwd=r,text=True).strip()
assert git('branch','--show-current')=='codex/unguard'
assert git('rev-parse','HEAD')=='6c18faf47fcab4e3cf4cb6e8210dbaf9fe69073c'
assert not git('diff','--cached','--name-only')
actual=git('diff','--name-only','HEAD','--').splitlines()+git('ls-files','--others','--exclude-standard').splitlines()
assert set(actual)==set(paths),(set(actual)-set(paths),set(paths)-set(actual))
subprocess.run(['git','diff','--check'],cwd=r,check=True)
subprocess.run(['git','add','--',*paths],cwd=r,check=True)
assert set(git('diff','--cached','--name-only').splitlines())==set(paths)
subprocess.run(['git','commit','-m','Prove typed-print reconstruction and verify approved joins'],cwd=r,check=True)
head=git('rev-parse','HEAD')
Path('/private/tmp/codex-unguard/implementation-head.txt').write_text(head+'\n')
print(json.dumps(dict(head=head,files=len(paths),required_checks=len(required))))
