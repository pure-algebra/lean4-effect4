from pathlib import Path
import subprocess,json,time
out=Path('/private/tmp/seams-s0-scout');work=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4')
leanpath=':'.join([str(out),*[str(work/'.lake/packages'/n/'.lake/build/lib/lean') for n in ['batteries','effects','typescript','hash','whatwg','aesop']],str(work/'.lake/build/lib/lean')])
def run(label,args):
 cmd=['python3','/private/tmp/seams-lean-one.py','lake','env','env','LEAN_PATH='+leanpath,'lean',*args]
 start=time.time();p=subprocess.run(cmd,cwd=work,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (out/(label+'.log')).write_text(p.stdout);(out/(label+'.json')).write_text(json.dumps(dict(command=cmd,exit=p.returncode,seconds=time.time()-start),indent=2)+'\n')
 print(label,p.returncode,p.stdout[-4000:],flush=True)
 if p.returncode:raise SystemExit(p.returncode)
for name in ['SeamsS0Check']:
 run('nominal-build-'+name,['--root='+str(out),'-DwarningAsError=true','-o',str(out/(name+'.olean')),str(out/(name+'.lean'))])
roots=['run','Oracle.uncached','Checked.pure\'','Checked.bind\'','Checked.ask','Checked.readVerdict','Memo.empty','Memo.learn','Memo.oracle','HitRule.exact','HitRule.or']
full=['Effect4.Program.Check.'+x for x in roots]
run('nominal-lower',['-M4096','--run',str(out/'SeamsS0Driver.lean'),'--out',str(out/'checker_nominal.ml'),'--import','SeamsS0Check','--cap','6000','--types','Effect4.Program.Check.Checked,Effect4.Program.Check.Memo,Effect4.Program.Check.Oracle,Effect4.Program.Check.HitRule,Effect4.Program.DefRole','--nominal-roots',','.join(full),*full])
