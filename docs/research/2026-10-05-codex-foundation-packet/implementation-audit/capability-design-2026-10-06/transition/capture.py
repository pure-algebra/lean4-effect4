import subprocess,json,hashlib,pathlib,datetime
out=pathlib.Path('/private/tmp/codex-effect4-overnight-monitor/2026-10-06-capability-design/transition')
main='/Users/pooks/Dev/lean4-effect4'
seats={'main':(main,'c22f908def0c2a881ae46040d0dbaaaa57991352'),'lift':(main+'-mask','698390476983fa89ce55e88dc7ef7aa695111cb3'),'check':(main+'-qsteps','7b332a805aa9317a32b882ca6e6aafa15371fa65'),'semw':(main+'-qtypes','11b45d8d66f8df07a4478e494dc61c27a16cdc1b')}
paths={'main':['AGENTS.md','docs/STATE.md','docs/core/decisions.md','docs/core/controlled-english.md','docs/core/semantics.md','docs/core/system-map.md','docs/core/machine-state.md','docs/research/2026-10-05-claude-lead/briefs/seat-lift-brief.md','docs/research/2026-10-05-claude-lead/briefs/seat-check-brief.md','docs/research/2026-10-05-claude-lead/briefs/seat-semw-brief.md','docs/research/2026-10-06-seat-CHECK-receipt.md','src/Effect4/Machine/Timer.lean','src/Effect4/Api/TestClock.lean','vendor/effect-4.0.0-rc.112/src/testing/TestClock.ts','vendor/effect-4.0.1/src/testing/TestClock.ts'], 'lift':['src/Effect4/Laws/Machine/MaskRuns.lean','src/Effect4/Laws/Program/MaskRuns.lean','Test/Machine/MaskRuns.lean','docs/research/2026-10-06-seat-LIFT-design.md'], 'check':['docs/research/2026-10-06-seat-CHECK-receipt.md','src/Effect4/Laws/Api/Codegen.lean'], 'semw':['src/Effect4/Laws/Modules/Waiting.lean','src/Effect4/Laws/Modules/Semaphore/Ops.lean','src/Effect4/Modules/Semaphore/Ops.lean','Test/Program/SemaphoreOps.lean','Test/Program/SemaphoreTraces.lean']}
rows=[]
def retain(b,rel,meta):
 p=out/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 rows.append(dict(meta,copy=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)))
for seat,fs in paths.items():
 root,commit=seats[seat]
 for path in fs:
  b=subprocess.check_output(['git','-C',root,'show',commit+':'+path]);retain(b,pathlib.Path('source')/seat/path,{'kind':'committed-source','repository':root,'commit':commit,'path':path,'source':root+'/'+path})
# Active edits retained as source observations only. They do not change frozen acceptance.
for seat,ps in {'lift':['src/Effect4/Laws/Machine/MaskRuns.lean','Test/Machine/MaskRuns.lean','docs/research/2026-10-06-seat-LIFT-design.md'],'semw':['Test/Program/SemaphoreFaces.lean']}.items():
 root,commit=seats[seat]
 for path in ps:
  p=pathlib.Path(root)/path
  if p.exists():retain(p.read_bytes(),pathlib.Path('active-source')/seat/path,{'kind':'active-source','repository':root,'base_commit':commit,'path':path,'source':str(p),'mtime_ns':p.stat().st_mtime_ns})
base=pathlib.Path('/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/acf2315e-02ac-4acd-9ef9-b0734bd686a7/scratchpad')
for seat,logs in {'check':['stepB-default-again.log','accept-checks.log'],'lift':['final-build.log','stepF-build1.log'],'semw':['build-step3-default.log','build-step5-default.log','build-faces-1.log','truth-elab-3.log','gen-truth-1.log']}.items():
 for name in logs:
  p=base/seat/name
  if p.exists():retain(p.read_bytes(),pathlib.Path('evidence')/seat/name,{'kind':'retained-seat-output','source':str(p),'mtime_ns':p.stat().st_mtime_ns,'not_monitor_execution':True})
(out/'source-evidence-manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
(out/'frozen-heads.json').write_text(json.dumps({'captured_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'seats':seats,'note':'Snapshot committed cuts supplied before capture. Later active file copies are explicitly separate.'},indent=2)+'\n')
checks=[]
for row in rows:
 if row['kind']=='committed-source':
  actual=subprocess.check_output(['git','-C',row['repository'],'show',row['commit']+':'+row['path']])
 else:actual=pathlib.Path(row['source']).read_bytes()
 checks.append({'source':row['source'],'commit':row.get('commit'),'matches_at_recheck':hashlib.sha256(actual).hexdigest()==row['sha256']})
(out/'source-recheck.json').write_text(json.dumps(checks,indent=2)+'\n')
print(json.dumps({'retained':len(rows),'matched':sum(x['matches_at_recheck'] for x in checks),'changed':[x for x in checks if not x['matches_at_recheck']]}))
