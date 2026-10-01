from pathlib import Path
import subprocess,os,time,json,hashlib
out=Path(__file__).resolve().parent
cache=Path('/private/tmp/codex-second-eyes-2026-10-01')
lean='/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean'
env=os.environ.copy();env.update(LEAN_NUM_THREADS='1',LEAN_PATH=str(cache/'lib'))
for name,h in json.loads((out/'inputs.json').read_text()).items():
    assert hashlib.sha256((out/name).read_bytes()).hexdigest()==h
(out/'DefinitiveSchemaAudit.lean').write_bytes((out/'DefinitiveSchemaProbe.lean').read_bytes()+(out/'ExtraSchemaChecks.txt').read_bytes())
runs=[]
for name,file,cwd in [('hashes','VerifyHashes.lean',cache),('schema','DefinitiveSchemaAudit.lean',out),
                      ('projection','ConstructiveProjectionProbe.lean',out),('union','UnionImageProbe.lean',out)]:
    cmd=[lean,'-j1','-M1536']+(['--run'] if name=='hashes' else ['-DwarningAsError=true'])+[file]
    start=time.monotonic();p=subprocess.run(cmd,cwd=cwd,env=env,text=True,capture_output=True,timeout=30)
    log=p.stdout+p.stderr;(out/f'{name}.log').write_text(log)
    runs.append(dict(name=name,command=cmd,cwd=str(cwd),exit_code=p.returncode,seconds=round(time.monotonic()-start,3),
        environment={'LEAN_NUM_THREADS':'1','LEAN_PATH':env['LEAN_PATH']}))
    (out/'lean-results.json').write_text(json.dumps(runs,indent=2)+'\n')
    print(name,p.returncode,log,flush=True)
    assert p.returncode==0
    assert 'sorryAx' not in log and 'Classical.choice' not in log
