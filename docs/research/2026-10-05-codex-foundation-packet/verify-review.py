from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, subprocess
r=Path('/private/tmp/codex-effect4-overnight-monitor/2026-10-05-transactions-task-review')
repo=Path('/Users/pooks/Dev/lean4-effect4')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda n:json.loads((r/n).read_text())
model=load('model/results.json')
assert model['checks_passed']==22 and model['source_unchanged_during_run']
assert sha(repo/'docs/research/2026-10-05-claude-lead/tx-probes/TxModel.lean')==model['source_sha256']
for v in load('atomic/results.json')['results']:
 assert [c['observed'] for c in v['cases']]==[2,1]
 assert all(c['finalValue']==2 and c['scheduled']==0 for c in v['cases'])
for v in load('atomic/clock-results.json')['results']:
 assert all(v['checks'].values())
for n in ['scout/composition.rc112.out','scout/composition.v401.out']:
 p=load(n)['result']
 assert [(v['caught'],v['wholeExit'],v['after']) for v in p['nestedFailure']]==[(True,'Success',1),(False,'Failure',0)]
 assert p['caughtRetry']=={'runs':2,'caught':1,'afterHandler':1,'result':2,'after':2}
 assert [(v['mutate'],v['after'],v['version']) for v in p['payloadRollback']]==[(True,1,0),(False,0,0)]
assert load('scout/alternatives-v3.out')['assertions']=='passed'
inputs=[
'AGENTS.md','docs/core/decisions.md','docs/core/machine-state.md',
'docs/research/2026-10-05-claude-lead/groundwork-plan.md',
'docs/research/2026-10-05-claude-lead/queues-review.md',
'docs/research/2026-10-05-claude-lead/transactions-and-clock.md',
'docs/research/2026-10-05-claude-lead/tx-probes/TxModel.lean',
'src/Effect4/Machine/Fibers.lean','src/Effect4/Machine/Wake.lean',
'src/Effect4/Laws/Machine/Book.lean','src/Effect4/Laws/Program/Typed/Assembly.lean',
'src/Effect4/Laws/Program/RuntimeR.lean','src/Effect4/Data/ClockMillis.lean',
'src/Effect4/Program/Native.lean','src/Effect4/Program/Compile.lean','src/Effect4/Program/Ty.lean']
(r/'inputs').mkdir(exist_ok=True)
for name in inputs[:7]:
 (r/'inputs'/name.replace('/','__')).write_bytes((repo/name).read_bytes())
checks=[]
for link in re.findall(r'\]\(([^)]+)\)',(r/'review.md').read_text()):
 if link.startswith(('https:','http:')): continue
 p=Path(link) if link.startswith('/') else r/link
 if p.name=='receipt.json': continue
 assert p.exists(),str(p)
 checks.append(str(p))
executions=[
 {'command':f'python3 {r}/model/probes.py','exit_code':0,'output':'model/results.json','evidence':'22 finite mirror checks'},
 {'command':f'bun {r}/atomic/inline-reentry.mjs','exit_code':0,'output':'atomic/results.json','evidence':'4 finite host cases with controls'},
 {'command':f'bun {r}/atomic/clock-profile.mjs','exit_code':0,'output':'atomic/clock-results.json','evidence':'2 versioned clock runs with controls'},
]
executions+=load('scout/audit-receipt.json')['executions']
for version,package in [('rc112','/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/effect'),('v401','/Users/pooks/.bun/install/cache/effect@4.0.1@@@1')]:
 executions.append({'command':f'bun {r}/atomic/cancel-return/probe.mjs {package} > {r}/atomic/cancel-return/{version}.json','exit_code':0,'output':f'atomic/cancel-return/{version}.json','evidence':'Five finite host controls; commitment and caller interruption distinguished'})
executions += [
 {'command':f'python3 -B scripts/check-language.py --strict {r}/review.md','exit_code':0,'evidence':'scratch report passes'},
 {'command':f'python3 {r}/verify-review.py','exit_code':0,'evidence':'retained output assertions, source hash and report links checked'},
 {'command':f'python3 {r}/verify-literature.py','exit_code':0,'evidence':'primary downloads, cancellation outputs, and packet links checked'},
]
rec={
'observed_at_utc':datetime.now(timezone.utc).isoformat(),
'head':subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip(),
'branch':subprocess.check_output(['git','-C',str(repo),'branch','--show-current'],text=True).strip(),
'git_status':subprocess.check_output(['git','-C',str(repo),'status','--porcelain'],text=True),
'input_hashes':{n:sha(repo/n) for n in inputs},
'report_sha256':sha(r/'review.md'),
'decision_packet_sha256':sha(r/'contracts-and-literature.md'),
'owner_acceptance':'Latest owner message ratifies final recommendations, asks delivery to Claude, and includes planned future consumers as reasons for design now. Coordinator must enter tracked rulings before dispatch.',
'executions':executions,
'reused_evidence':[
 {'path':'/private/tmp/codex-effect4-overnight-monitor/2026-10-05-deferred-latch-probes/runtime/results.json','kind':'retained finite rc.112 postedWake runs; not rerun'},
 {'path':str(repo/'docs/research/2026-10-05-claude-lead/tx-probes/TxModel.out'),'kind':'Claude recorded Lean output; no independent Lean rerun'}],
'limits':['No monitor repository edits, Git mutation, dependency installation, Lean build, compiler or generator','Finite model and runtime evidence, not proofs or liveness','No new upstream bug classification','Owner ratifies final package; tracked rulings and implementation dispatch remain with coordinator'],
'coordinator':{'title':'Queues plan and design decisions','url':'claude.ai/epitaxy/local_fba6862c-f91c-4a69-8859-ce514ca70b21','ui':'CUA confirms idle research response; no phase handoff','guidance_sent':False},
'local_report_links_checked':len(checks),
'artifact_hashes':{str(p.relative_to(r)):sha(p) for p in r.rglob('*') if p.is_file() and p.name!='receipt.json'}
}
(r/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({'verified':True,'head':rec['head'],'report_sha256':rec['report_sha256'],'model_checks':22,'links_checked':len(checks),'git_status':rec['git_status']}))
