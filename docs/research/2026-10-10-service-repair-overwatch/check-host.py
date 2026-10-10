from pathlib import Path
import copy,hashlib,json,os,subprocess
r=Path(__file__).resolve().parent;root=r.parents[2];logs=r/'checks'
primary=Path('/Users/pooks/Dev/lean4-effect4');commit='ec08fe863bb336f8d77c2287c811266886ef718e'
previous=r.parent/'2026-10-10-service-client-overwatch'
truth=previous/'snapshot/harness/truth'
prior=json.loads((previous/'pins.json').read_text())
reused={}
for name,wanted in prior['source_sha256'].items():
 if name=='harness/truth/corpus.json':continue
 data=subprocess.check_output(['git','show',commit+':'+name],cwd=primary)
 assert hashlib.sha256(data).hexdigest()==wanted,name
 assert hashlib.sha256((previous/'snapshot'/name).read_bytes()).hexdigest()==wanted,name
 reused[name]=wanted
link=r/'node_modules'
if not link.is_symlink():link.symlink_to(root/'ts/eff/node_modules',target_is_directory=True)
compiler=root/'ts/eff/node_modules/.bin/tsgo'
version=subprocess.check_output([str(compiler),'--version'],text=True).strip()
assert version=='Version 7.0.0-dev.20260629.1',version

def run(name,cmd):
 p=subprocess.run(cmd,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=45,env={**os.environ,'GOMAXPROCS':'3'})
 (logs/(name+'.log')).write_text(p.stdout)
 return p

def types(name,file):
 cmd=[str(compiler),'--noEmit','--strict','--target','es2022','--module','esnext','--moduleResolution','bundler','--allowImportingTsExtensions','--skipLibCheck',str(file)]
 p=run('types-'+name,cmd);assert p.returncode==0,p.stdout
 return {'command':cmd,'exit_code':p.returncode}

# Observe the extra method that the checked reader discards.
(r/'alias-behavior.ts').write_text('''import { Effect } from "effect"
import * as Canonical from "./canonical.ts"
import * as Alias from "./alias.ts"
const keys = await Effect.runPromise(Effect.provide(Effect.map(Alias.S, Object.keys), Alias.SLayer))
const restoredKeys = await Effect.runPromise(Effect.provide(Effect.map(Canonical.S, Object.keys), Canonical.SLayer))
const answer = await Effect.runPromise(Effect.provide(Effect.flatMap(Alias.S, s => s.alias()), Alias.SLayer))
const originalMain = await Effect.runPromise(Canonical.main)
const aliasMain = await Effect.runPromise(Alias.main)
if (JSON.stringify(keys) !== '["get","alias"]' || JSON.stringify(restoredKeys) !== '["get"]' || answer !== 1 || originalMain !== 1 || aliasMain !== 1) throw new Error("alias control failed")
console.log(JSON.stringify({keys,restoredKeys,answer,originalMain,aliasMain}))
''')
typed=[types(name,r/(name+'.ts')) for name in ['canonical','alias','alias-behavior']]
p=run('alias-behavior',['bun','run',str(r/'alias-behavior.ts')]);assert p.returncode==0,p.stdout
alias_result=json.loads(p.stdout)

# Use the landed Semaphore entry and the stronger program emitted by Controls.lean.
manifest=json.loads(subprocess.check_output(['git','show',commit+':harness/truth/corpus.json'],cwd=primary))
entry=next(x for x in manifest['programs'] if x['name']=='pSemaphoreService')
assert entry['run']['exit']==entry['runSync']['exit']=={'success':[1,False,2]}
strong=copy.deepcopy(entry)
strong['decl']=(r/'semaphore-stronger-decl.ts').read_text()
strong['client']=entry['client'].replace('s.take(1)','s.take(2)').replace('s.takeIfAvailable(5)','s.takeIfAvailable(1)')
# Both exits below are independently evaluated by Controls.lean before this script runs.
strong['run']['exit']={'success':[2,False,1]};strong['runSync']['exit']={'success':[2,False,1]}
strong['run']['fibers'][0]['exit']={'success':[2,False,1]}
strong['run']['events']=[x.replace('[1,false,2]','[2,false,1]') for x in strong['run']['events']]

def fresh(e,methods):
 result=copy.deepcopy(e)
 for method,callee in [('take','semaphoreTake'),('release','semaphoreRelease'),('takeIfAvailable','semaphoreTakeIfAvailable')]:
  if method not in methods:continue
  old=f'{method}: (a1: number) => {callee}(pair(a0, a1))'
  new=f'{method}: (a1: number) => Effect.flatMap(semaphoreMake(), fresh => {callee}(pair(fresh, a1)))'
  assert result['decl'].count(old)==1,(method,result['decl'][-2000:])
  result['decl']=result['decl'].replace(old,new)
 return result

cases=[('landed',entry,True),('landed_fresh_each_method',fresh(entry,['take','release','takeIfAvailable']),True),('stronger',strong,True)]
for method in ['take','release','takeIfAvailable']:
 cases.append(('stronger_fresh_'+method,fresh(strong,[method]),False))
cases += [('stronger_fresh_each_method',fresh(strong,['take','release','takeIfAvailable']),False),('stronger_restored',strong,True)]
results=[]
for label,variant,expected_pass in cases:
 out=r/'host-controls'/label;out.mkdir(parents=True,exist_ok=True)
 for dep in truth.glob('*.ts'):
  if not (out/dep.name).is_symlink():(out/dep.name).symlink_to(dep)
 if not (out/'session').is_symlink():(out/'session').symlink_to(truth/'session',target_is_directory=True)
 m={**manifest,'programs':[variant]};mp=out/'corpus.json';mp.write_text(json.dumps(m,indent=2)+'\n')
 cmd=['bun','run',str(truth/'run-truth.ts'),'--manifest',str(mp),'--out',str(out),'--only','pSemaphoreService','--timeout','100']
 p=run('host-'+label,cmd)
 assert (out/'result.json').exists(),p.stdout
 result=json.loads((out/'result.json').read_text());row=result['rows'][0]
 assert (p.returncode==0)==expected_pass and row['clientAgree']==expected_pass,(label,p.stdout)
 assert row['exitAgree'] and row['runSyncAgree'] and row['scheduleAgree'],row
 type_result=types(label,out/'generated/pSemaphoreService.ts')
 observation=out/'client-observation.json'
 observe_cmd=['bun','run',str(truth/'run-truth.ts'),'--observe',str(out/'generated/pSemaphoreService.ts'),'--unit','client','--result',str(observation),'--timeout','100']
 observed=run('observation-'+label,observe_cmd);assert observed.returncode==0,observed.stdout
 actual=json.loads(observation.read_text())
 if expected_pass:assert actual['observation']['exit']==variant['run']['exit'],actual
 results.append({'case':label,'command':cmd,'exit_code':p.returncode,'clientAgree':row['clientAgree'],'client_exit':actual['observation']['exit'],'main_exit':row['host']['exit'],'types':type_result})
(logs/'host-results.json').write_text(json.dumps({'reviewed_commit':commit,'reused_source_sha256':reused,'compiler':version,'effect':result['effect'],'bun':result['bun'],'alias_types':typed,'alias_observation':alias_result,'semaphore':results},indent=2)+'\n')
print(json.dumps({'alias_observation':alias_result,'semaphore':[{'case':x['case'],'clientAgree':x['clientAgree'],'client_exit':x['client_exit']} for x in results]},indent=2))
