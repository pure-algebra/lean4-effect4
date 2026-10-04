from pathlib import Path
import json, hashlib, subprocess, os, time, sys, signal
ROOT = Path('/Users/pooks/Dev/lean4-effect4-gemini')
OUT = Path(__file__).resolve().parent
REV = 'a8cc886697e173e28a7cf67eca0f49566164b0d8'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args): return subprocess.check_output(['git','-C',str(ROOT),*args],text=True).strip()
assert git('rev-parse','HEAD') == REV
assert not git('status','--porcelain'), 'Active checkout changed; inspect before probing'
script = ROOT/'scripts/check-semantics.py'
ns={'__file__':str(script),'__name__':'probe_import_guard'}
exec(compile(script.read_text(),str(script),'exec'),ns)
ns['TARGETS']=('Tools.Semantics',)
receipt={'revision':REV,'boundary':'Isolated tooling probe; no production proof or generator run','checkerSha256':sha(script),'commands':[]}
ns['verify_saved_outputs'](receipt)
setup=json.loads((ROOT/'.lake/build/ir/Drivers/SemanticsControls.setup.json').read_text())
setup['name']='VisibilityProbe'
setup['plugins']=[]
setup['dynlibs']=[]
sourceChecks={}
for module, artifacts in setup['importArts'].items():
 artifact=Path(artifacts[0][0]); trace=json.loads(artifact.with_suffix('.trace').read_text())
 if module.startswith('Batteries.'):
  source=ROOT/'.lake/packages/batteries'/Path(*module.split('.')).with_suffix('.lean')
 elif module.startswith('Effect4.'):
  source=ROOT/'src'/Path(*module.split('.')).with_suffix('.lean')
 else:
  source=ROOT/'tools'/Path(*module.split('.')).with_suffix('.lean')
 candidates=[v for k,v in trace['inputs'] if isinstance(k,str) and k.endswith('.lean')]
 assert len(candidates)==1,(module,candidates)
 actual=ns['lake_binary_hash'](source.read_bytes())
 assert actual==candidates[0],(module,'source hash mismatch')
 relative=str(source.relative_to(ROOT))
 if not relative.startswith('.lake/'):
  committed=subprocess.check_output(['git','-C',str(ROOT),'show',f'{REV}:{relative}'])
  assert committed==source.read_bytes(),(module,'uncommitted source')
 sourceChecks[module]={'path':relative,'sha256':sha(source),'lakeHash':actual}
receipt['sources']=sourceChecks
setupFile=OUT/'VisibilityProbe.setup.json'; setupFile.write_text(json.dumps(setup,indent=2)+'\n')
probe=OUT/'VisibilityProbe.lean'
lean='/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean'
args=[lean,'-j1','-M4096','-DwarningAsError=true','--setup='+str(setupFile),str(probe)]
start=time.monotonic()
env={**os.environ,'LEAN_NUM_THREADS':'1','GOMAXPROCS':'1','GOMEMLIMIT':'512MiB'}
process=subprocess.Popen(args,cwd=OUT,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,start_new_session=True)
try: output,_=process.communicate(timeout=90)
except subprocess.TimeoutExpired:
 os.killpg(process.pid,signal.SIGTERM); output,_=process.communicate(timeout=5)
receipt['commands'].append({'command':args,'cwd':str(OUT),'exit':process.returncode,'seconds':round(time.monotonic()-start,3),'timeoutSeconds':90})
receipt['probeSha256']=sha(probe)
receipt['headAfter']=git('rev-parse','HEAD');receipt['statusAfter']=git('status','--porcelain')
(OUT/'lean.log').write_text(output)
(OUT/'lean-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(output)
print(f'Checked {len(sourceChecks)} source/import matches and {len(receipt["savedOutputs"])} artifacts; exit {process.returncode}')
sys.exit(process.returncode)
