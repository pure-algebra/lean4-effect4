from pathlib import Path
import subprocess,json,hashlib,datetime,shlex,re
r=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4')
e=r/'docs/research/2026-10-17-seams/receipts/evidence/S0'
for label in ['generate-lcnf-6','generate-lcnf-7-compare','native-final','core-audit','regeneration-alias-controls']:
 assert json.loads((e/(label+'.json')).read_text())['exit_status']==0,label
log=(e/'generate-lcnf-7-compare.log').read_text()
closure={}
for segment in log.split('== ')[1:]:
 name=segment.splitlines()[0]
 if name in ['ocaml/gen/api_gen.ml','ocaml/engine/api_engine.ml']:
  assert 'clock refusals (0)' in segment,name
  assert 'types as placeholders: #[]' in segment,name
  assert 'field types not spelled: #[]' in segment,name
  closure[name]=int(re.search(r'closure: (\d+)',segment).group(1))
assert len(closure)==2
parent={'src/Effect4.lean','Test/All.lean','docs/core/semantics.md','tools/ProofGraph/Registry.lean','docs/research/2026-10-17-seams/receipts/README.md'}
paths=set(subprocess.check_output(['git','diff','--name-only'],cwd=r,text=True).splitlines())
paths.update(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=r,text=True).splitlines())
paths=sorted(p for p in paths-parent if not p.startswith('generated/'))
(e/'source-paths.txt').write_text('\n'.join(paths)+'\n')
compared=sorted(p for p in Path('/private/tmp/seams-s0-final-compare').rglob('*') if p.is_file())
snapshot={'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'base':'faa7d0122bd550186e4c622517509ac001763a35',
          'source_sha256':{p:hashlib.sha256((r/p).read_bytes()).hexdigest() for p in paths},
          'compared_file_count':len(compared),'closure_declarations':closure}
(e/'source-freeze.json').write_text(json.dumps(snapshot,indent=2)+'\n')
p=r/'docs/research/2026-10-17-seams/receipts/S0.md'
s=p.read_text().replace('Final production gates remain pending until the source freeze.', 'The source is frozen after the final comparison and production native controls.\nThe coordinator runs the final batteries and complete OCaml gate before committing.')
s += '''
## Source freeze

`evidence/S0/source-freeze.json` records the measured freeze time and each owned file's SHA-256.
`evidence/S0/source-paths.txt` gives the exact owned production paths.
The receipt and its evidence directory are additional force-added research artifacts.
The coordinator owns the root imports, semantics placement, registry roots, generated semantics, and receipts index.

`generate-lcnf-6` publishes the final generated family successfully.
After the alias guard changes, `generate-lcnf-7-compare` reruns the actual producer in a fresh comparison directory.
Every inferred interface, implementation, and closure manifest matches the production family byte for byte.
The Live artifact and native engine report zero clock refusals, placeholders, and unknown fields.

`native-final` passes the production positive, hostile-client, interface, stable-step, staging, and alias controls.
No S0 Lean source changes after the successful core audit.
The final batteries, complete OCaml gate, and commit remain the coordinator's landing steps.

## Command index

The linked logs retain every command's output, including each failed control.

| Record | Exit | Seconds | Exact command |
| --- | --- | --- | --- |
'''
for f in sorted(e.glob('*.json')):
 data=json.loads(f.read_text())
 if 'command' not in data:continue
 command=shlex.join(data['command']).replace('|','\\|')
 s+=f'| [{f.stem}](evidence/S0/{f.name}) | {data["exit_status"]} | {data["elapsed_seconds"]} | `{command}` |\n'
p.write_text(s)
print(json.dumps({'frozen':True,'owned_paths':len(paths),'compared_files':len(compared),'closure_declarations':closure}),flush=True)
