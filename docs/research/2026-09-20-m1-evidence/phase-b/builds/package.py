from pathlib import Path
import csv, gzip, hashlib, io, json, re, shlex, tarfile

OUT=Path('/tmp/m1-tools/phase-b-build-evidence')
ROOT=Path('/Users/pooks/Dev/lean4-effect4')
PLAN=Path('/tmp/m1-tools/phase-b-serial-plan/serial-plan.json')
plan=json.loads(PLAN.read_text())
serial_dir=PLAN.parent/'logs'
meta_names=['modules-2-9','modules-7-9','modules-15-18','world-repair-run','modules-21-24','frame-repair-run','laws-root-run','state-controls-run']
manual_names=['api-supervision','arena-contract','completion-data','forms-compile','frames-old-pin','indexed-columns-unpinned','indexed-columns','machine-handshake','position-tool','state-generator-syntax-failed','state-generator','state-old-pin','test-all','test-all-census-tool','census-truth-build','census-keyed-build']
instrument=json.loads(Path('/tmp/m1-tools/phase-b-instrument-evidence/commands-and-results.json').read_text())
instrument_by_name={Path(c['stdout_stderr']).name:c for c in instrument['controls']}
files={}
for p in sorted(serial_dir.glob('*.log')): files[p]='logs/serial/'+p.name
for n in meta_names: files[Path('/tmp/m1-phase-b-'+n+'.log')]='logs/orchestration/m1-phase-b-'+n+'.log'
for n in manual_names: files[Path('/tmp/m1-phase-b-'+n+'.log')]='logs/manual/m1-phase-b-'+n+'.log'
for n in instrument_by_name: files[Path('/tmp')/n]='logs/instruments/'+n
metadata={PLAN:'metadata/serial-plan.original.json',Path('/tmp/m1-tools/run-phase-b-modules.py'):'metadata/run-phase-b-modules.py',Path('/tmp/m1-tools/phase-b-repair-notes.txt'):'metadata/phase-b-repair-notes.txt',Path('/tmp/m1-tools/phase-b-census-runner/direct-driver-compiles.sh'):'metadata/direct-driver-compiles.sh',Path('/tmp/m1-tools/phase-b-instrument-evidence/commands-and-results.json'):'metadata/instrument-commands-and-results.json',ROOT/'lakefile.toml':'metadata/lakefile.toml'}
files.update(metadata)
assert all(p.is_file() for p in files)
blobs={member:p.read_bytes() for p,member in files.items()}
sha=lambda b:hashlib.sha256(b).hexdigest()
rawmanifest=[{'original_path':str(p),'archive_member':m,'bytes':len(blobs[m]),'sha256':sha(blobs[m])} for p,m in files.items()]
raw_by_path={r['original_path']:r for r in rawmanifest}
serial_events={}
for name in meta_names:
 p=Path('/tmp/m1-phase-b-'+name+'.log')
 current=None
 for line_number,line in enumerate(p.read_text().splitlines(),1):
  if line.startswith('BUILD '):
   _,order,module=line.split(' ',2);current=(int(order),module)
  if line.startswith('RESULT '):
   _,code,path=line.split(' ',2); code=int(code)
   assert current
   actual=Path(path)
   if code and actual.with_suffix('.attempt1.log').exists():actual=actual.with_suffix('.attempt1.log')
   assert actual not in serial_events
   serial_events[actual]={'order':current[0],'module':current[1],'process_exit_code':code,'result_record':{'original_path':str(p),'line':line_number,'literal':line},'recorded_path':path,'renamed_prior_attempt':str(actual)!=path}
assert set(serial_events)==set(serial_dir.glob('*.log'))

records=[]
for p,m in files.items():
 if m.startswith(('metadata/','logs/orchestration/')):continue
 txt=blobs[m].decode()
 rec={'log':m,'original_path':str(p),'bytes':len(blobs[m]),'sha256':sha(blobs[m]),'argv':None,'env':None,'cwd':str(ROOT),'command':None,'process_exit_code':None,'compiler_child_exit_code':None,'provenance':'Retained compiler/build output only; exact outer command and exit code not retained.'}
 child=re.findall(r'Lean exited with code (\d+)',txt)
 if child:rec['compiler_child_exit_code']=int(child[-1])
 rec['observed_result']='build completed successfully' if 'Build completed successfully' in txt else 'build failed' if 'error: build failed' in txt else 'compiler error' if re.search(r'(^|\n).*error:',txt) else 'empty output' if not txt else 'diagnostics retained'
 rec['fresh_built_modules']=re.findall(r'^[✔ℹ] \[\d+/\d+\] Built (\S+)',txt,re.M)
 rec['embedded_child_commands']=[x.removeprefix('trace: .> ') for x in txt.splitlines() if x.startswith('trace: .> ')]
 if p in serial_events:
  ev=serial_events[p];rec.update(ev);rec['argv']=['lake','build',ev['module']];rec['env']={'LEAN_NUM_THREADS':'1'};rec['command']=f"LEAN_NUM_THREADS=1 lake build {ev['module']}";rec['provenance']='Exact runner implementation plus retained orchestration RESULT; prior failures preserved through runner rename.';rec['kind']='serial module build'
 elif p.name in instrument_by_name:
  c=instrument_by_name[p.name]
  for k in ['argv','env','process_exit_code','compiler_child_exit_code','provenance']:rec[k]=c[k]
  rec['kind']='instrument finite control';rec['control_id']=c['id'];rec['control_result']=c['result']
  if rec['argv']:rec['command']='LEAN_NUM_THREADS=1 '+shlex.join(rec['argv'])
 else:rec['kind']='manual compile/build'
 if p.name in ['m1-phase-b-test-all.log','m1-phase-b-test-all-census-tool.log']:
  rec.update(argv=['lake','build','Test.All'],env={'LEAN_NUM_THREADS':'1'},command='LEAN_NUM_THREADS=1 lake build Test.All',process_exit_code=0,provenance='Exact command and process exit confirmed by coordinator from completed tool result.')
  audit=re.search(r'Effect4 module and axiom gate: checked (\d+) modules and (\d+) declarations; semantic/test axioms are \[propext,\s*Quot.sound\]; exact implementation boundary \((\d+) module\(s\), (\d+) declaration\(s\)\) additionally allows Classical.choice',txt)
  assert audit
  rec['audit']={'modules':int(audit[1]),'declarations':int(audit[2]),'semantic_test_axioms':['propext','Quot.sound'],'implementation_modules':int(audit[3]),'implementation_declarations':int(audit[4]),'implementation_additional_axiom':'Classical.choice'}
 if p.name=='m1-phase-b-forms-compile.log':
  argv=['lake','env','lean','-M6144','-DwarningAsError=true','--root=tools','tools/Effect4Gen/Forms.lean','-o','.lake/build/lib/lean/Effect4Gen/Forms.olean','-i','.lake/build/lib/lean/Effect4Gen/Forms.ilean']
  rec.update(argv=argv,env={'LEAN_NUM_THREADS':'1'},command='LEAN_NUM_THREADS=1 '+shlex.join(argv),process_exit_code=0,provenance='Exact command and rc0 confirmed by coordinator from completed session 8293; empty diagnostic log retained.')
 if p.name in ['m1-phase-b-census-truth-build.log','m1-phase-b-census-keyed-build.log']:
  script=metadata[Path('/tmp/m1-tools/phase-b-census-runner/direct-driver-compiles.sh')]
  line=next(x for x in blobs[script].decode().splitlines() if x.endswith('> '+str(p)+' 2>&1'))
  command=line.split(' > ',1)[0]
  rec.update(argv=shlex.split(command)[1:],env={'LEAN_NUM_THREADS':'1'},command=command,process_exit_code=0,provenance='Exact direct-driver script retained; coordinator confirmed entire set -e script rc0 in session 11629, establishing each sequential command rc0.',kind='prebaseline direct driver compile')
 rec['redirected_command']=None if rec['command'] is None else rec['command']+' > '+str(p)+' 2>&1'
 records.append(rec)

with (OUT/'raw-logs.tar.gz').open('wb') as target:
 with gzip.GzipFile(filename='',mode='wb',fileobj=target,mtime=0) as gz:
  with tarfile.open(fileobj=gz,mode='w') as tf:
   for member in sorted(blobs):
    b=blobs[member];info=tarfile.TarInfo(member);info.size=len(b);info.mode=0o644;info.mtime=0;tf.addfile(info,io.BytesIO(b))
with tarfile.open(OUT/'raw-logs.tar.gz','r:gz') as tf:
 assert set(tf.getnames())==set(blobs)
 for member in tf.getmembers():assert tf.extractfile(member).read()==blobs[member.name]
(OUT/'archive-manifest.json').write_text(json.dumps(rawmanifest,indent=2)+'\n')
result={'scope':'Phase B statement/tool builds and completed prebaseline direct compiles; not the later theorem census or ledger-status runs.','event_timestamps':'No timestamps inferred. Archive metadata normalized to zero only for reproducible packaging, not execution evidence.','serialization':'Recorded runner runs one module at a time with LEAN_NUM_THREADS=1; no Lean process was started for packaging.','plan_caveat':'Original serial-plan status and requested counts are planning fields, not execution evidence. Actual records below override no field in the retained original.','outer_exit_caveat':'Null means unknown, never inferred from successful stdout or a compiler child exit.','records':records}
(OUT/'commands-and-results.json').write_text(json.dumps(result,indent=2)+'\n')
with (OUT/'build-results.tsv').open('w',newline='') as f:
 w=csv.writer(f,delimiter='\t',lineterminator='\n');w.writerow(['kind','module_or_control','log','outer_exit_code','child_exit_code','observed_result','command'])
 for r in records:w.writerow([r['kind'],r.get('module',r.get('control_id','')),r['log'],'' if r['process_exit_code'] is None else r['process_exit_code'],'' if r['compiler_child_exit_code'] is None else r['compiler_child_exit_code'],r['observed_result'],r['command'] or ''])

# Coverage is observed fresh-build lines only, distinct from replayed/cached diagnostics.
coverage=[]
for row in plan['statement_build_order']:
 matches=[{'log':r['log'],'line':i,'diagnostic':line} for r in records for i,line in enumerate(blobs[r['log']].decode().splitlines(),1) if re.match(r'^[✔ℹ] \[\d+/\d+\] Built '+re.escape(row['module'])+r'(?: |$)',line)]
 coverage.append({'plan_order':row['order'],'module':row['module'],'fresh_build_evidence':matches})
(OUT/'planned-module-coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
summary={'archived_files':len(blobs),'archived_log_files':sum(m.startswith('logs/') for m in blobs),'uncompressed_bytes':sum(map(len,blobs.values())),'archive_bytes':(OUT/'raw-logs.tar.gz').stat().st_size,'compile_records':len(records),'serial_records':len(serial_events),'serial_process_successes':sum(e['process_exit_code']==0 for e in serial_events.values()),'serial_process_failures':sum(e['process_exit_code']!=0 for e in serial_events.values()),'unknown_outer_exit_records':sum(r['process_exit_code'] is None for r in records),'planned_modules':len(coverage),'planned_modules_with_fresh_build_evidence':sum(bool(x['fresh_build_evidence']) for x in coverage),'archive_byte_verification':'Every archived member matches the original bytes and manifest SHA256.'}
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
(OUT/'receipt.md').write_text(f'''Phase B build evidence

This bundle retains {summary['archived_log_files']} diagnostic logs and six input/runner metadata files in a lossless archive. It records {len(records)} compile attempts or finite instrument controls. The serial runner records 19 successful module builds and two failed attempts, each followed by a separately retained successful retry. Standalone failures and repairs also remain separate. {summary['unknown_outer_exit_records']} outer process exit codes are unknown; their recorded output and any child exit are retained without promoting them to exact process status.

Both Test.All runs returned 0. The earlier audit checked 469 modules and 66,141 declarations; the latest checked 469 modules and 66,142 declarations. Both reported semantic/test axioms [propext, Quot.sound] and the same explicit implementation allowance: 14 modules, 29 declarations, additionally admitting Classical.choice. These results establish the recorded build/audit scope; they are not a claim that the Phase B wanted statements are proved.

Forms compiled directly with the confirmed command and returned 0. The two direct driver compiles (Truth and Keyed) also returned 0 through the retained sequential set -e script. Their empty diagnostic logs are kept. These are completed prerequisites for the next census, not census results. Later census and ledger-status output is excluded.

The original serial plan is retained verbatim, including stale plan-only wording and planned counts. It is not execution metadata. The runner RESULT records, exact commands where retained or coordinator-confirmed, and fresh Built lines supply the execution evidence. Every one of the 26 planned statement-build targets has a fresh Built line somewhere in this retained set; planned-module-coverage.json gives each location and excludes Replayed lines.

The instrument controls are finite checks. Search and zero-theorem-census failures, the initial missing-import setup failure, successful repairs, and the ordinary dead-tactic refusal remain distinguished. The separate phase-b-instrument-evidence bundle contains the detailed source/diff review.

All original bytes were read back from the compressed archive and compared with their source and SHA256. Archive header timestamps are normalized only for deterministic packaging; no execution timestamps are inferred. Packaging started no Lean process and changed no repository files.
''')
(OUT/'COPY-RECIPE.md').write_text('''Reviewed promotion recipe (not executed)

The coordinator may copy this directory after reviewing commands-and-results.json and receipt.md. It contains only retained build evidence and packaging metadata; no source patch or generated artifact.

```sh
cd /Users/pooks/Dev/lean4-effect4
mkdir -p docs/research/2026-09-20-m1-evidence/phase-b-builds
cp -p /tmp/m1-tools/phase-b-build-evidence/* docs/research/2026-09-20-m1-evidence/phase-b-builds/
cd docs/research/2026-09-20-m1-evidence/phase-b-builds
shasum -a 256 -c SHA256SUMS
```

This command copies only top-level packaged files. The archive keeps the raw logs losslessly. Do not rerun package.py from the repository destination: it intentionally writes only the original scratch directory. Stage explicit promoted paths only after reviewing the copy.
''')
# package.py is included in top-level manifest so the extraction/packaging procedure is reviewable.
entries=[]
for p in sorted(OUT.iterdir()):
 if p.is_file() and p.name!='SHA256SUMS':entries.append(f'{sha(p.read_bytes())}  {p.name}\n')
(OUT/'SHA256SUMS').write_text(''.join(entries))
for line in entries:
 h,name=line.rstrip('\n').split('  ',1);assert sha((OUT/name).read_bytes())==h
print(json.dumps(summary,indent=2))
