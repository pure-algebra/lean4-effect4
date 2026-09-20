#!/usr/bin/env python3
"""Aggregate retained M1 census text; no Lean, writes only this scratch directory."""
from pathlib import Path
import csv, hashlib, json, re

ROOT=Path('/Users/pooks/Dev/lean4-effect4')
E=ROOT/'docs/research/2026-09-20-m1-evidence'
OUT=Path(__file__).resolve().parent
RX=re.compile(r'^(?:info: .*?:\d+:\d+: )?([A-Za-z0-9_.]+): (\d+) of (\d+) theorems closed from their statements; (\d+) source lines they now take$')
DEFAULT='aesop (default rule sets)'
STORES='aesop (rule_sets := [Effect4.Stores])'
CAP='requested 20000; effective Core.Context limit inherited and not recorded'
CAVEAT=('Historical ProofGraph.search set the maxHeartbeats option but did not update Lean 4.33.1 Core.Context.maxHeartbeats. These successful searches remain kernel-checked facts, but their counts do not establish success within the requested 20000-heartbeat cap. Rerun baseline/current and final-bank comparisons with the corrected instrument after placement; do not raise the budget. No claimed final-bank increase is established by this inventory.')
# Order is explicit provenance order, not a filesystem timestamp inference.
SPECS=[
 ('census-before.log','before_original_m1',DEFAULT,'CensusBefore.lean','Original 38-module snapshot, receipt records exit 0; no-theorem commands emitted unreachable-tactic warnings.'),
 ('census-additional.log','before_additional_m1',DEFAULT,'CensusAdditional.lean','Six further Guard consumers measured before editing, per M1 receipt.'),
 ('origin-census-before.log','before_scoped_origin_maintenance',DEFAULT,'OriginCensusBefore.lean','Before the target Book/Clauses/Api.Supervision maintenance; not asserted to be a globally untouched tree.'),
 ('timer-census-before.log','before_scoped_clock_maintenance',DEFAULT,'clock/TimerCensusBefore.lean','Timer 0/17 confirmed as genuine pre-clock census by simulation_scout.'),
 ('reference-origin-seven-before.log','maintained_before_reference_pass',DEFAULT,'ReferenceOriginCensusBefore.lean','Valid then-built modules before seven-module proof maintenance. Core/site source changes already existed; no manifest proves untouched pre-origin oleans. Combined import attempt failed separately.'),
 ('simulation-fibers-before-pending-origin.log','maintained_before_pending_origin',DEFAULT,None,'Fresh Fibers census after earlier M1 maintenance and before pending-origin repair; not an original before count.'),
 ('approximation-census-restored.log','restored_maintained',DEFAULT,None,'Initial olean absent. Coordinator confirms restored/maintained 14/119, before=null.'),
 ('clock/clock-wanted.log','new_module_initial_skeleton',DEFAULT,'clock/ClockWanted.lean','No theorem existed (0/0); useful skeleton fact, not a before denominator for the final eight theorems.'),
 ('clock/clock-decimal-baseline.log','interim_rejected_decimal_route',DEFAULT,'clock/clock-decimal-baseline.lean','Then-built 0/5; same audit exposed Classical.choice in the decimal route, later replaced. Not final trust or baseline evidence.'),
 ('clock/Clock-final-audit.log','after_bank_preplacement',STORES,'clock/Clock-final-audit.lean','Explicit Stores-bank audit before placement and before the search-cap correction.'),
 ('guard/ReturnTasks-census-maintained.log','maintained_after_compile_repair',DEFAULT,'guard/ReturnTasksCensus.lean','Before attempt failed for missing olean; 0/27 is maintained-tree only.'),
 ('guard-clock-maintained-census.log','maintained_after_compile_repair',DEFAULT,'GuardClockMaintainedCensus.lean','Focused clock follow-up failed imports before later repair; Single 0/34 and OuterDriver 0/36 are maintained-tree counts. OuterDriver also has an earlier additional-M1 snapshot.'),
]
FAILS=[
 (E/'reference-origin-census-before-failed.log',[
  'Effect4.Laws.Program.Sched','Effect4.Laws.Program.DenoteR','Effect4.Laws.Program.EvaluateR',
  'Effect4.Laws.Program.Means','Effect4.Laws.Program.Intro.Weight','Effect4.Laws.Program.Intro.Fibers',
  'Effect4.Laws.Program.Intro.Merge','Effect4.Laws.Program.Simulation.Fibers']),
 (E/'approximation-census-before-unavailable.log',['Effect4.Laws.Machine.Approximation']),
 (E/'simulation-pending-before-unavailable.log',['Effect4.Laws.Program.Simulation.Pending']),
 (E/'clock-followup-census-unavailable.log',['Effect4.Laws.Program.Guard.Single','Effect4.Laws.Program.Guard.OuterDriver']),
 (Path('/tmp/m1-clock-followup-census-after-api.log'),['Effect4.Laws.Program.Guard.Single','Effect4.Laws.Program.Guard.OuterDriver']),
 (E/'guard/ReturnTasks-census-before-unavailable.log',['Effect4.Laws.Program.Guard.ReturnTasks']),
 (Path('/tmp/m1-agreement-census-before.log'),['Effect4.Laws.Program.Agreement']),
]

def display(p):
 try:return str(p.relative_to(ROOT))
 except ValueError:return str(p)

def file_info(p):
 data=p.read_bytes()
 return {'path':display(p),'sha256':hashlib.sha256(data).hexdigest()}

observations=[]
for rel,kind,bank,command,note in SPECS:
 p=E/rel
 data=p.read_text(errors='replace')
 hits=[]
 for line_no,line in enumerate(data.splitlines(),1):
  m=RX.match(line)
  if m:
   module,closed,total,source_lines=m.groups()
   event={'module':module,'closed':int(closed),'total':int(total),'source_lines':int(source_lines),
    'kind':kind,'bank':bank,'requested_cap':20000,'effective_cap':None,'inherited_cap_caveat':True,
    'source_log':display(p),'source_line':line_no,'command_source':display(E/command) if command else None,'note':note}
   observations.append(event);hits.append(event)
 assert hits, rel
 # A census count may coexist with axiom findings, but not an unnoticed elaboration error.
 assert not re.search(r'^.*?:\d+:\d+: error:',data,re.M), rel

failures=[]
for p,modules in FAILS:
 assert p.exists(),p
 data=p.read_text(errors='replace')
 assert ': error:' in data,p
 assert not any(RX.match(line) for line in data.splitlines()),p
 failures.append({'modules':modules,**file_info(p),'first_error':next(line for line in data.splitlines() if ': error:' in line),
  'count':None,'contributes_count':False})

prepared=[]
for rel in ['CensusBefore.lean','CensusAdditional.lean','OriginRadiusCensus.lean','ReferenceOriginCensusBefore.lean',
 'GuardClockMaintainedCensus.lean','clock/TimerCensusBefore.lean','clock/Clock-final-audit.lean']:
 prepared.extend(re.findall(r'^#auto_census\s+([\w.]+)',(E/rel).read_text(),re.M))
# New companions belong to the eventual bank radius but a ledger closure is not a census.
new_companions=['Effect4.Laws.Machine.CompletionData','Effect4.Laws.Machine.Refinement','Effect4.Laws.Machine.Clock']
modules=sorted(set(prepared)|{x['module'] for x in observations}|{m for f in failures for m in f['modules']}|set(new_companions))
plan=json.loads(Path('/tmp/m1-tools/placement-plan.json').read_text())
move={x['source_module']:x['destination_module'] for x in plan['moves']}
rows=[]
for mod in modules:
 obs=[o for o in observations if o['module']==mod]
 befores=[o for o in obs if o['kind'].startswith('before_')]
 afters=[o for o in obs if o['kind'].startswith(('maintained_','restored_','after_bank_'))]
 before=befores[0] if befores else None
 after=afters[-1] if afters else None
 failed=[f['path'] for f in failures if mod in f['modules']]
 target='Effect4.TypedState' if '.Typed.' in mod or mod.endswith('.Auto.Frames') else 'Effect4.Stores'
 rows.append({'module':mod,'final_module':move.get(mod,mod),
  'before_count':f"{before['closed']}/{before['total']}" if before else None,
  'before_kind':before['kind'] if before else None,
  'before_bank':before['bank'] if before else None,
  'before_log':f"{before['source_log']}:{before['source_line']}" if before else None,
  'after_count':f"{after['closed']}/{after['total']}" if after else None,
  'after_kind':after['kind'] if after else None,
  'after_bank':after['bank'] if after else None,
  'after_log':f"{after['source_log']}:{after['source_line']}" if after else None,
  'failed_before':bool(failed),'failed_before_logs':failed,
  'inherited_cap_caveat':True,'final_bank_target':target,
  'final_bank_postplacement_count':None,'missing_final_bank_run':True,
  'observation_count':len(obs),
  'notes': 'No census observation; prepared radius or new companion only.' if not obs else
           'Maintained/restored counts are deliberately excluded from before_count.' if not before else ''})

orig=[o for o in observations if o['kind']=='before_original_m1']
assert (len(orig),sum(o['closed'] for o in orig),sum(o['total'] for o in orig))==(38,246,1593)
assert next(r for r in rows if r['module']=='Effect4.Laws.Machine.Approximation')['before_count'] is None
assert next(r for r in rows if r['module']=='Effect4.Laws.Program.Guard.Single')['before_count'] is None
assert next(r for r in rows if r['module']=='Effect4.Laws.Program.Guard.OuterDriver')['before_count']=='0/36'
assert next(r for r in rows if r['module']=='Effect4.Laws.Program.Sched')['before_count'] is None

# List aliases by identical bytes, never count the duplicate /tmp copies twice.
candidate_logs=list(E.rglob('*.log'))+list(Path('/tmp').glob('m1-*.log'))
canonical_hashes={hashlib.sha256((E/rel).read_bytes()).hexdigest():display(E/rel) for rel,*_ in SPECS}
aliases=[]
for p in candidate_logs:
 digest=hashlib.sha256(p.read_bytes()).hexdigest()
 if digest in canonical_hashes and display(p)!=canonical_hashes[digest]:
  aliases.append({'canonical':canonical_hashes[digest],'duplicate':display(p)})

meta={'schema_version':1,'status':'offline evidence inventory; no Lean run; no live source edits',
 'head':'15cb510e2ea747364e1c814e3a92f1e1ac0075eb','working_tree':'uncommitted Phase A maintenance; not a source-identity claim for earlier logs',
 'scope':'Only the retained 2026-09-20-m1-evidence tree and direct /tmp/m1-*.log files, plus the prepared placement map.',
 'search_cap_caveat':CAVEAT,'before_field_policy':'Only original M1, its documented extra Guard snapshot, and explicitly confirmed target-scoped before runs. Maintained, restored, initial-empty and rejected-interim measurements never populate before_count.',
 'after_field_policy':'Latest observed post-initial or maintained count, explicitly labeled; plain aesop is not a final-bank run.',
 'failed_before_policy':'At least one focused attempt failed before search. This does not erase a separate valid earlier result (notably OuterDriver).',
 'original_snapshot':{'modules':38,'closed':246,'total':1593},
 'summary':{'modules':len(rows),'observations':len(observations),'failed_attempts':len(failures),
  'modules_with_before':sum(r['before_count'] is not None for r in rows),
  'modules_with_after_or_maintained':sum(r['after_count'] is not None for r in rows),
  'explicit_bank_observations':sum(o['kind']=='after_bank_preplacement' for o in observations),
  'missing_final_bank_runs':len(rows)},
 'rows':rows,'observations':observations,'failed_attempts':failures,'duplicate_log_copies':aliases,
 'not_counted':['typed_state_obligations ledger totals','narrow build success','proof-wanted snapshots','prepared census commands without output'],
 'planned_phase_b_radius':'World, Arena, connector and handshake final modules must be added once their final paths/statements exist; this table does not invent filenames or baseline counts for them.'}
(OUT/'census-table.json').write_text(json.dumps(meta,indent=2)+'\n')
with (OUT/'census-table.csv').open('w',newline='') as f:
 keys=list(rows[0]);w=csv.DictWriter(f,fieldnames=keys);w.writeheader()
 for row in rows:w.writerow({**row,'failed_before_logs':' | '.join(row['failed_before_logs'])})
(OUT/'missing-final-bank-runs.json').write_text(json.dumps([{'module':r['module'],'final_module':r['final_module'],'bank':r['final_bank_target'],
 'reason':'No post-placement run with corrected search budget exists in inspected evidence.'} for r in rows],indent=2)+'\n')
(OUT/'README.md').write_text(f'''# Census evidence inventory\n\n{len(rows)} module rows; {len(observations)} observations; {len(failures)} failed attempts. The original snapshot is exactly 246/1593 across 38 modules.\n\n{CAVEAT}\n\n`census-table.csv` is the compact comparison. `census-table.json` preserves every observation, precise log line, failed import, and duplicate log copy. Empty before cells are intentional. The latest after cell may be a maintained-tree plain-aesop measurement; its kind and bank columns say so. OuterDriver has an earlier documented additional-M1 0/36 and a later maintained 0/36 despite the intervening failed clock follow-up attempts. The seven reference-origin counts are maintained-tree evidence before that seat's repair pass; no untouched-olean manifest survives. Approximation's restored 14/119 is also maintained, never before.\n\nOnly Data.ClockMillis 0/8 and Store.Clock 1/3 have explicit Stores-bank audits in inspected logs. They predate placement and the budget fix. All {len(rows)} listed modules therefore lack a final post-placement bank run; the exact list, including the Store.Domain.Clock path mapping, is `missing-final-bank-runs.json`. Prepared origin-radius modules with no successful output are retained with empty counts. New Phase B World/Arena/connector/handshake modules must join this list when their final paths exist.\n\nNo ledger totals, build results, generated-rule counts, or failed elaborations are counted as census closures. This script runs no Lean and writes only this directory.\n''')
print(json.dumps(meta['summary'],indent=2))
