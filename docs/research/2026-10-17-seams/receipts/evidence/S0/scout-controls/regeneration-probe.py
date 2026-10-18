from pathlib import Path
import subprocess, tempfile, shutil, hashlib, json
out=Path('/private/tmp/seams-s0-scout'); work=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4')
case=out/'regeneration'; case.mkdir(exist_ok=True)
op=['opam','exec','--switch=effect4','--']
incs=sum([['-I',str(work/'ocaml/_build/default'/p)] for p in ['eff/.effect4_eff.objs/byte','clock/.effect4_clock.objs/byte','lcnf/.effect4_lcnf.objs/byte']],[])
manifest=json.loads((out/'engine-root-names.json').read_text())
roots=manifest['roots']+manifest['prelude']+['program_interp_of','step_decision_state_at_program_replay_checked_from_spec_1']
def run(label,cmd,cwd,expected=0):
 r=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (out/(label+'.log')).write_text(r.stdout); (out/(label+'.json')).write_text(json.dumps(dict(command=cmd,cwd=str(cwd),exit=r.returncode,expected=expected),indent=2)+'\n')
 print(label,r.returncode,r.stdout[-500:],flush=True)
 if r.returncode!=expected: raise RuntimeError(label)
 return r.stdout
source=(work/'ocaml/engine/api_engine.ml').read_text()
(case/'api_engine.ml').write_text(source)
(case/'api_engine.mli').write_text('val api_run : int\n')
run('regenerate-stale-interface',op+['ocamlc',*incs,'-c','api_engine.mli'],case)
run('regenerate-stale-implementation-red',op+['ocamlc',*incs,'-c','api_engine.ml'],case,2)
def stage(source,label,expect=0):
 with tempfile.TemporaryDirectory(dir=out,prefix='s0-stage-') as tmp:
  tmp=Path(tmp); (tmp/'api_engine.ml').write_text(source)
  status=run(label+'-infer-implementation',op+['ocamlc','-bin-annot',*incs,'-c','api_engine.ml'],tmp,expect)
  if expect:return False
  interface=run(label+'-infer-interface',op+[str(out/'sig_seal.exe'),'api_engine.cmt',','.join(roots),''],tmp)
  (tmp/'api_engine.mli').write_text(interface)
  # Remove the unsealed cmi, then build the sealed implementation in the same temporary directory.
  (tmp/'api_engine.cmi').unlink()
  run(label+'-check-interface',op+['ocamlc',*incs,'-c','api_engine.mli'],tmp)
  run(label+'-check-implementation',op+['ocamlc',*incs,'-c','api_engine.ml'],tmp)
  for name in ['api_engine.ml','api_engine.mli']:
   shutil.copyfile(tmp/name,case/name)
  return True
assert stage(source,'regenerate-green')
previous={name:hashlib.sha256((case/name).read_bytes()).hexdigest() for name in ['api_engine.ml','api_engine.mli']}
assert not stage(source+'\nlet root_type_mismatch : int = "bad"\n','regenerate-mismatch-red',2)
assert previous=={name:hashlib.sha256((case/name).read_bytes()).hexdigest() for name in previous}
(out/'regenerate-publication.json').write_text(json.dumps({'old_interface_ignored':True,'positive_compiles':True,'bad_stage_published':False,'retained_sha256':previous},indent=2)+'\n')
print('Regeneration replaces a stale interface; refusal retains both published files.',flush=True)
