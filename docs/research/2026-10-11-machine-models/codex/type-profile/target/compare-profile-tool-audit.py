from pathlib import Path
import os, subprocess, sys, re, json
root=Path('/Users/pooks/.codex/worktrees/last-planned-goals/lean4-effect4')
stage=Path('/private/tmp/profile-tool-baseline');stage.mkdir(exist_ok=True)
base='9d7d4e5ef12528985a78f19352004fa2ef6e427f'
modules=['OCaml5.Lcnf.Externs','OCaml5.Lcnf.Builtins','OCaml5.Lcnf.Translate','OCaml5.Tools.LcnfGen','Effect4Gen.PreludeAtoms']
# Lean selects a search root by the top-level module directory. Populate every
# untouched sibling with read-only symlinks; never compile through a target link.
build=root/'.lake/build/lib/lean'
owned=[mod.replace('.','/') for mod in modules]
for namespace in ['OCaml5','Effect4Gen']:
    for artifact in (build/namespace).rglob('*'):
        if not artifact.is_file(): continue
        rel=artifact.relative_to(build)
        if any(str(rel).startswith(stem+'.') for stem in owned): continue
        target=stage/rel
        target.parent.mkdir(parents=True,exist_ok=True)
        if not target.exists(): target.symlink_to(artifact)
for mod in modules:
    source=('tools/' if mod.startswith('Effect4Gen.') else 'src/')+mod.replace('.','/')+'.lean'
    out=stage/(mod.replace('.','/')+'.lean');out.parent.mkdir(parents=True,exist_ok=True)
    out.write_bytes(subprocess.check_output(['git','show',base+':'+source],cwd=root))
current_env=json.loads(subprocess.check_output(['lake','env','python3','-c','import os,json;print(json.dumps(dict(os.environ)))'],cwd=root))
current_env['LEAN_NUM_THREADS']='3'
env=current_env.copy();env['LEAN_PATH']=str(stage)+':'+env.get('LEAN_PATH','')
log=Path('/private/tmp/profile-target-tool-baseline-build.log')
with log.open('w') as out:
    for mod in modules:
        source=stage/(mod.replace('.','/')+'.lean')
        args=['lean','--root='+str(stage),'-DwarningAsError=true','-o',str(source.with_suffix('.olean')),str(source)]
        print('COMMAND:', ' '.join(args),file=out,flush=True)
        r=subprocess.run(args,cwd=root,env=env,stdout=out,stderr=subprocess.STDOUT)
        if r.returncode: print(log.read_text());sys.exit(r.returncode)
for label, runenv in [('baseline',env),('current',current_env)]:
    log=Path('/private/tmp/profile-target-tool-'+label+'-audit.log')
    with log.open('w') as out:
        r=subprocess.run(['lean','-DwarningAsError=true','/private/tmp/ProfileToolAudit.lean'],cwd=root,env=runenv,stdout=out,stderr=subprocess.STDOUT)
    print(label,r.returncode,flush=True)
    if r.returncode not in [0,1]: raise RuntimeError('audit execution failed')
def findings(label):
    text=Path('/private/tmp/profile-target-tool-'+label+'-audit.log').read_text()
    return text.splitlines()[0],set(re.findall(r'^  (.+) reaches \[(.+)\]$',text,re.M))
before, old=findings('baseline');after,new=findings('current')
assert not any('fieldCarrierIn?' in name for name, _ in old), 'baseline resolves current module'
assert any('fieldCarrierIn?' in name for name, _ in new), 'current module lacks the new helper'
report={'base':base,'baseline_summary':before,'current_summary':after,'unchanged_count':len(old&new),'new_findings':sorted(new-old),'removed_findings':sorted(old-new)}
Path('/private/tmp/profile-target-tool-audit-comparison.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
