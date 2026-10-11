import hashlib,json,pathlib,subprocess
base=pathlib.Path('/Users/pooks/Dev/lean4-effect4')
archive=base/'docs/research/2026-10-11-machine-models/codex/worktrees/archives'
rows=json.loads((archive/'manifest.json').read_text())
def git(root,*args): return subprocess.check_output(['git','-C',str(root),*args])
results=[]
for row in rows:
 root=pathlib.Path(row['worktree'])
 assert not git(root,'status','--porcelain=v1','-z'),(str(root),'dirty')
 assert git(root,'rev-parse','HEAD').decode().strip()==row['head']
 assert not any(x.startswith('+') for x in git(root,'cherry','refactor/phase1-phase3').decode().splitlines())
 files=[p.decode() for p in git(root,'ls-files','--others','--ignored','--exclude-standard','-z','--','docs/research').split(b'\0') if p]
 assert sorted(files)==sorted(f['path'] for f in row['files'])
 assert hashlib.sha256(pathlib.Path(row['archive']).read_bytes()).hexdigest()==row['archive_sha256']
 for f in row['files']:
  p=root/f['path']
  if 'link' in f: assert p.is_symlink() and p.readlink().as_posix()==f['link']
  else: assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256']
 ancestor=subprocess.run(['git','-C',str(base),'merge-base','--is-ancestor',row['head'],'refactor/phase1-phase3']).returncode==0
 subprocess.run(['git','-C',str(base),'worktree','remove',str(root)],check=True)
 branch='retained: matching patches, head is not an ancestor'
 if ancestor:
  branch=git(base,'branch','-d',row['branch']).decode().strip()
 result={k:row[k] for k in ['worktree','head','branch','archive','archive_sha256']}
 result.update({'removed':True,'branch_result':branch,'preserved_entries':len(row['files'])})
 results.append(result)
 (archive/'removed.json').write_text(json.dumps(results,indent=2)+'\n')
 print(json.dumps(result),flush=True)
