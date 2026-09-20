from pathlib import Path
import csv,gzip,hashlib,importlib.util,io,json,tarfile

OUT=Path('/tmp/m1-tools/portable-census-evidence')
EVID=Path('/tmp/m1-tools/phase-b-portable-before-fill-evidence')
RUNNER=Path('/tmp/m1-tools/phase-b-census-runner')
ROOT=Path('/Users/pooks/Dev/lean4-effect4')
sha=lambda b:hashlib.sha256(b).hexdigest()
run=json.loads((EVID/'run.json').read_text())
results=json.loads((EVID/'results.json').read_text())
inputs=json.loads((EVID/'inputs.json').read_text())
plan=json.loads((EVID/'source-plan.json').read_text())
assert run['status']=='complete' and run['results']==results
assert len(results)==run['expected_modules']==218
assert len(run['jobs'])==run['expected_processes']==139
assert run['historical_counts_used'] is False and run['skipped']==[]
assert all(j['status']=='complete' and j['exit_code']==0 for j in run['jobs'])
assert all(r['cap']==20000 and r['tactic']=='aesop' and r['lane']=='before-fill' for r in results)
assert len({r['module'] for r in results})==218

files={p:'before-fill/'+p.relative_to(EVID).as_posix() for p in EVID.rglob('*') if p.is_file()}
for p in sorted(RUNNER.iterdir()):
 if p.is_file():files[p]='provenance/runner/'+p.name
current_plan=Path('/tmp/m1-tools/phase-b-serial-plan/census-plan.json')
old_plan=Path('/tmp/m1-tools/phase-b-serial-plan/census-plan.original214.json')
base_plan=Path('/tmp/m1-tools/phase-b-integration/census-plan.json')
files[current_plan]='provenance/plans/census-plan.current218.json'
files[Path('/tmp/m1-phase-b-portable-census.log')]='provenance/outer-run.log'
files[old_plan]='provenance/plans/census-plan.original214.json'
files[base_plan]='provenance/plans/census-plan.base.json'
assert current_plan.read_bytes()==(EVID/'source-plan.json').read_bytes()
assert sha(old_plan.read_bytes())==plan['extension_provenance']['original214_snapshot']['sha256']
assert sha(base_plan.read_bytes())==plan['extension_provenance']['base_sha256']
by_input={str(Path(f['path']).resolve()):f for f in inputs['files']}
checks=[]
def require_pinned(p,role):
 p=Path(p);pin=by_input[str(p.resolve())]
 digest=sha(p.read_bytes());assert digest==pin['sha256'] and p.stat().st_size==pin['size']
 checks.append({'role':role,'original_path':str(p),'captured_input_path':pin['path'],'sha256':digest,'bytes':pin['size'],'matches_frozen_input':True})
for p in [RUNNER/'run-census.py',RUNNER/'read-census-log.py',RUNNER/'guards.json',current_plan]:require_pinned(p,'runner/guard/plan')
guards=json.loads((RUNNER/'guards.json').read_text())
assert guards==inputs['cap_guards']
for item in guards['reviewed_sources']:
 p=ROOT/item['path'];assert sha(p.read_bytes())==item['sha256'];require_pinned(p,'reviewed instrument/control source');files[p]='provenance/guard-sources/'+item['path']
for item in guards['control_logs']:
 p=Path(item['path']);assert sha(p.read_bytes())==item['sha256'];checks.append({'role':'passed finite instrument control','original_path':str(p),'captured_input_path':'inputs.json cap_guards.control_logs','sha256':item['sha256'],'bytes':p.stat().st_size,'matches_frozen_input':True});files[p]='provenance/guard-logs/'+p.name
for name in ['lean-toolchain','lake-manifest.json','lakefile.toml']:
 p=ROOT/name
 if str(p.resolve()) in by_input:require_pinned(p,'toolchain/package/build settings');files[p]='provenance/toolchain/'+name

# Reparse all reports with the exact frozen parser; no Lean, search, or compilation.
spec=importlib.util.spec_from_file_location('retained_reader',RUNNER/'read-census-log.py')
reader=importlib.util.module_from_spec(spec);spec.loader.exec_module(reader)
for job in run['jobs']:
 assert sha(Path(job['frozen_source']).read_bytes())==job['source_sha256']
 assert sha(Path(job['process_log']).read_bytes())==job['process_log_sha256']
for r in results:
 assert sha(Path(r['module_log']).read_bytes())==r['module_log_sha256']
 parsed=reader.report(Path(r['module_log']).read_text(),r['module'],0)
 assert all(r[k]==v for k,v in parsed.items())
 pr=next(x for x in plan['rows'] if x['module']==r['module'])
 source=ROOT/pr['path'];pin=by_input[str(source.resolve())]
 assert r['source_sha256']==pin['sha256']

blobs={m:p.read_bytes() for p,m in files.items()}
manifest=[{'original_path':str(p),'archive_member':m,'bytes':len(blobs[m]),'sha256':sha(blobs[m])} for p,m in sorted(files.items(),key=lambda kv:kv[1])]
with (OUT/'raw-census.tar.gz').open('wb') as target:
 with gzip.GzipFile(filename='',mode='wb',fileobj=target,mtime=0) as gz:
  with tarfile.open(fileobj=gz,mode='w') as tf:
   for member in sorted(blobs):
    b=blobs[member];info=tarfile.TarInfo(member);info.size=len(b);info.mode=0o644;info.mtime=0;tf.addfile(info,io.BytesIO(b))
with tarfile.open(OUT/'raw-census.tar.gz','r:gz') as tf:
 assert set(tf.getnames())==set(blobs)
 for m in tf.getmembers():assert tf.extractfile(m).read()==blobs[m.name]
(OUT/'archive-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(OUT/'pinned-provenance.json').write_text(json.dumps({'checks':checks,'scope':'Current retained runner, parser, guard, plan and reviewed control bytes match inputs.json from the completed run. Unmeasured runner readmes/audits are retained as preparation records, not run status.','outer_process':{'exit_code':0,'session':'34967','provenance':'Coordinator confirmed exact outer command and completed rc0 from exec_command/write_stdin session 34967. The audit_only preamble is emitted by this same runner, not a separate command.','argv':['python3','/tmp/m1-tools/phase-b-census-runner/run-census.py','--run','--out','/tmp/m1-tools/phase-b-portable-before-fill-evidence'],'command':'python3 /tmp/m1-tools/phase-b-census-runner/run-census.py --run --out /tmp/m1-tools/phase-b-portable-before-fill-evidence > /tmp/m1-phase-b-portable-census.log 2>&1','log':'provenance/outer-run.log'},'inner_processes':'All 139 exact subprocess argv and exit_code 0 are retained in before-fill/run.json.'},indent=2)+'\n')
rows_by_module={r['module']:r for r in plan['rows']}
with (OUT/'module-baseline.tsv').open('w',newline='') as f:
 w=csv.writer(f,delimiter='\t',lineterminator='\n')
 w.writerow(['module','original_radius38','historical_module','raw_closed','admissible_closed','total_theorems','source_path','source_sha256','olean_sha256','module_log','module_log_sha256','process_id'])
 for r in sorted(results,key=lambda x:x['module']):
  w.writerow([r['module'],str(r['original_radius38']).lower(),r['historical_module'] or '',r['instrument_closed_count'],r['trust_admissible_closed_count'],r['instrument_total_count'],rows_by_module[r['module']]['path'],r['source_sha256'],r['olean_sha256'],'before-fill/module-logs/'+Path(r['module_log']).name,r['module_log_sha256'],r['process_id']])
original=[r for r in results if r['original_radius38']]
rejected=[dict(module=r['module'],**theorem) for r in results for theorem in r['rows'] if not theorem['trust_admissible']]
assert len(rejected)==1 and rejected[0]['name']=='Effect4.Program.path_beq_self'
summary={'lane':'before-fill','process_exit_code':0,'process_exit_provenance':'Coordinator completed session 34967; exact outer command and all inner exits retained.','modules':len(results),'processes':len(run['jobs']),'skipped_modules':0,'heartbeat_cap':20000,'tactic':'aesop','raw_closed':sum(r['instrument_closed_count'] for r in results),'admissible_closed':sum(r['trust_admissible_closed_count'] for r in results),'total_theorems':sum(r['instrument_total_count'] for r in results),'original_radius38':{'modules':len(original),'raw_closed':sum(r['instrument_closed_count'] for r in original),'admissible_closed':sum(r['trust_admissible_closed_count'] for r in original),'total_theorems':sum(r['instrument_total_count'] for r in original)},'rejected':rejected,'archived_files':len(blobs),'archived_bytes':sum(map(len,blobs.values())),'compressed_bytes':(OUT/'raw-census.tar.gz').stat().st_size,'verification':'All 218 reports reparsed and compared, all 139 frozen scratch/process hashes and 218 module-log hashes checked, pinned provenance matched, all archive bytes compared on readback.','final_bank_status':'not measured in this package','historical_old_cap_comparison':'not performed; old 246/1593 figures are not a comparable baseline and enter no aggregate'}
assert (summary['raw_closed'],summary['admissible_closed'],summary['total_theorems'])==(648,647,4062)
assert summary['original_radius38']=={'modules':38,'raw_closed':247,'admissible_closed':247,'total_theorems':1584}
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
# Compare only with the retained provisional same-cap run, never the old inherited-cap run.
provisional=json.loads(Path('/tmp/m1-tools/phase-b-before-fill-evidence/results.json').read_text())
fields=['instrument_closed_count','trust_admissible_closed_count','instrument_total_count']
old_by_module={r['module']:r for r in provisional}
assert set(old_by_module)=={r['module'] for r in results}
assert all(all(r[k]==old_by_module[r['module']][k] for k in fields) for r in results)
summary['same_per_module_counts_as_provisional_run']=True
summary['prior_run_status']='Provisional, retained unchanged in phase-b-before-fill-evidence and phase-b-census-evidence; not portable-proof evidence.'
summary['corrected_guarantee']='Every returned candidate passed synchronous requested-proposition kernel checking against the frozen original kernel environment; reported axiom dependencies include both proposition and proof.'
summary['plan_preparation_hash_mismatches']=[{'module':r['module'],'prepared_source_sha256':next(x for x in plan['rows'] if x['module']==r['module'])['source_sha256_current'],'captured_run_source_sha256':r['source_sha256']} for r in results if r['source_sha256']!=next(x for x in plan['rows'] if x['module']==r['module'])['source_sha256_current']]
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(OUT/'receipt.md').write_text('''Corrected Phase B before-fill census

The corrected census returned 0 and measured all 218 planned modules in 139 serial Lean processes. Every process used the same 20,000-heartbeat cap, warnings as errors, and plain aesop; no module was skipped. It closed 648 of 4,062 statements. Every returned candidate passed synchronous kernel checking at the requested proposition against the frozen pre-search kernel environment. Of those candidates, 647 had only [propext, Quot.sound] dependencies when both proposition and proof were audited.

The original 38-module group has 247 closures out of 1,584 statements, all admissible. The sole rejected dependency report remains Effect4.Program.path_beq_self in Effect4.Laws.Api.ModuleReadable, which reaches Classical.choice. These are measured search results; authored proof replacements still require their normal narrow builds.

The earlier same-cap run remains separately retained and explicitly provisional because its returned terms were not checked for portability and its axiom scan omitted proposition-only dependencies. The corrected run independently reproduces every module's raw, admissible and total counts. This equality is a comparison of observed counts, not retrospective validation of the old instrument. The older inherited-cap 246/1593 figures are neither compared nor included. No final-bank result or improvement is claimed.

The lossless archive contains every raw record, scratch source, process log and module log from the corrected run, plus the exact runner, parser, guard, pinned plan, reviewed instrument/control sources, control logs and outer run log. The manifest records the exact outer command and confirmed exit 0. The audit_only preamble comes from that same runner invocation. All 218 reports were reparsed and compared; all 139 scratch/process hashes and 218 module-log hashes were checked. All archived bytes were read back and compared.

Preparation plan fields remain verbatim and can predate the portability repair. The actual captured source/olean hashes in inputs.json and results.json, reproduced in the TSV, identify the measured tree; summary.json lists differences from prepared source hashes. Existing run timestamps are retained, and none were invented. Archive header timestamps are normalized only for deterministic packaging.

This package leaves both the provisional evidence directory and its earlier package unchanged. Packaging launched no Lean process, changed no repository source, and included no later ledger-status run.
''')
(OUT/'COPY-RECIPE.md').write_text('''Reviewed promotion recipe (not executed)

```sh
cd /Users/pooks/Dev/lean4-effect4
mkdir -p docs/research/2026-09-20-m1-evidence/portable-census
cp -p /tmp/m1-tools/portable-census-evidence/* docs/research/2026-09-20-m1-evidence/portable-census/
cd docs/research/2026-09-20-m1-evidence/portable-census
shasum -a 256 -c SHA256SUMS
```

Review receipt.md, summary.json and module-baseline.tsv before copying. The archive preserves every raw evidence file losslessly; archive-manifest.json maps each original path to the retained member and hash. Stage explicit promoted paths only. package.py writes to its named scratch output directory; it is retained for review, not intended to rerun in the promoted directory.
''')
entries=[]
for p in sorted(OUT.iterdir()):
 if p.is_file() and p.name!='SHA256SUMS':entries.append(f'{sha(p.read_bytes())}  {p.name}\n')
(OUT/'SHA256SUMS').write_text(''.join(entries))
for line in entries:
 h,name=line.rstrip('\n').split('  ',1);assert sha((OUT/name).read_bytes())==h
print(json.dumps({k:v for k,v in summary.items() if k not in ['rejected','verification','historical_old_cap_comparison']},indent=2))
