import hashlib, json, pathlib, subprocess, tarfile
base=pathlib.Path('/Users/pooks/Dev/lean4-effect4')
archive=base/'docs/research/2026-10-11-machine-models/codex/worktrees/archives'
archive.mkdir(parents=True,exist_ok=True)
names=['live-graph-index','module-authoring','module-field-inference','module-folds','module-semaphore','prepared-run-view']
def git(root,*args):
 return subprocess.check_output(['git','-C',str(root),*args])
results=[]
for name in names:
 root=pathlib.Path('/Users/pooks/.codex/worktrees')/name/'lean4-effect4'
 status=git(root,'status','--porcelain=v1','-z')
 assert not status,(name,'dirty')
 cherry=git(root,'cherry','refactor/phase1-phase3').decode()
 assert not any(x.startswith('+') for x in cherry.splitlines()),(name,'unmatched patch')
 paths=[p.decode() for p in git(root,'ls-files','--others','--ignored','--exclude-standard','-z','--','docs/research').split(b'\0') if p]
 manifest=[]
 for p in paths:
  f=root/p
  if f.is_symlink():
   manifest.append({'path':p,'bytes':0,'link':f.readlink().as_posix()})
  else:
   assert f.is_file(),(name,p,'not a regular file')
   manifest.append({'path':p,'bytes':f.stat().st_size,'sha256':hashlib.sha256(f.read_bytes()).hexdigest()})
 target=archive/(name+'.tar.gz')
 if not target.exists():
  with tarfile.open(target,'w:gz',dereference=False) as out:
   for p in paths: out.add(root/p,arcname=p,recursive=False)
 with tarfile.open(target,'r:gz') as saved:
  assert sorted(saved.getnames())==sorted(paths)
  for m in manifest:
   if 'link' in m:
    member=saved.getmember(m['path'])
    assert member.issym() and member.linkname==m['link']
   else:
    content=saved.extractfile(m['path']).read()
    assert len(content)==m['bytes'] and hashlib.sha256(content).hexdigest()==m['sha256']
 row={'worktree':str(root),'head':git(root,'rev-parse','HEAD').decode().strip(),'branch':git(root,'branch','--show-current').decode().strip(),'patch_comparison':cherry,'archive':str(target),'archive_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'files':manifest}
 (archive/(name+'.json')).write_text(json.dumps(row,indent=2)+'\n')
 results.append(row)
 print(json.dumps({'name':name,'files':len(paths),'bytes':sum(m['bytes'] for m in manifest),'archive_verified':True}),flush=True)
(archive/'manifest.json').write_text(json.dumps(results,indent=2)+'\n')
