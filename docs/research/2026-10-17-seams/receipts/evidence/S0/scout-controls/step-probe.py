from pathlib import Path
import json,subprocess,time
out=Path('/private/tmp/seams-s0-scout');work=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4')
leanpath=':'.join([str(out),*[str(work/'.lake/packages'/name/'.lake/build/lib/lean') for name in ['batteries','effects','typescript','hash','whatwg','aesop']],str(work/'.lake/build/lib/lean')])
def run(label,args):
 command=['python3','/private/tmp/seams-lean-one.py','lake','env','env','LEAN_PATH='+leanpath,'lean',*args]
 start=time.time();p=subprocess.run(command,cwd=work,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (out/(label+'.log')).write_text(p.stdout);(out/(label+'.json')).write_text(json.dumps(dict(command=command,exit=p.returncode,seconds=time.time()-start),indent=2)+'\n')
 print(label,p.returncode,p.stdout[-5000:],flush=True)
 if p.returncode:raise SystemExit(p.returncode)
run('step-build',['--root='+str(out),'-DwarningAsError=true','-o',str(out/'SeamsS0Step.olean'),str(out/'SeamsS0Step.lean')])
run('step-lower',['-M4096','--run','src/OCaml5/Tools/LcnfGen.lean','--out',str(out/'step_gen.ml'),'--import','SeamsS0Step','--cap','4000','--types','Effect4.Program.DefRole','Effect4.Program.stepChecked'])
