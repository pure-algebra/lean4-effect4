from pathlib import Path
import re,json,csv,subprocess,shutil
r=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4')
text=(r/'ocaml/engine/e4_engine_intf.ml').read_text().split('module type INSTANCE = sig',1)[1].split('module type ENGINE = sig',1)[0]
required=set(re.findall(r'\bval\s+([a-z_][a-zA-Z0-9_\']*)\s*:',text))
for adapter,public in [('ocaml/engine/e4_instance.ml','ocaml/engine/api_engine.mli'),('ocaml/engine/test/api_gen_inst.ml','ocaml/gen/api_gen.mli')]:
 definitions=set(re.findall(r'^\s*let(?:\s+rec)?\s+([a-z_][a-zA-Z0-9_\']*)\b',(r/adapter).read_text(),re.M))
 exported=set(re.findall(r'\bval\s+([a-z_][a-zA-Z0-9_\']*)\s*:',(r/public).read_text()))
 print('name/carriers supplied by Api_engine_inst/Api_engine_ref wrappers' if 'e4_instance' in adapter else '', flush=True)
 print(adapter, '\nINSTANCE vals',sorted(required),'\nadapter vals',sorted(definitions),'\nmissing inherited linkage',sorted(required-definitions-exported),flush=True)
overlay=Path('/private/tmp/seams-s0-linkage-overlay')
if overlay.exists():shutil.rmtree(overlay)
shutil.copytree(r/'ocaml',overlay,ignore=shutil.ignore_patterns('_build','.git'))
fresh=overlay/'fresh-cmt'
fresh.mkdir()
compiler=['opam','exec','--switch=effect4','--','ocamlopt','-bin-annot','-w','@55','-I',str(fresh)]
for directory in ['clock/.effect4_clock.objs/byte','lcnf/.effect4_lcnf.objs/byte']:
 compiler += ['-I',str(r/'ocaml/_build/default'/directory)]
for name in ['eff_types.mli','eff_types.ml']:
 shutil.copyfile(r/'ocaml/eff'/name,fresh/name)
 subprocess.run([*compiler,'-c',str(fresh/name)],cwd=fresh,check=True)
recipe=json.loads((r/'ocaml/gen/roots.json').read_text())
for entry in recipe['artefacts']:
 if entry['out']=='ocaml/eff/eff_types.ml':continue
 stem=Path(entry['out']).stem
 manifest=list(csv.DictReader((r/f'ocaml/gen/closure-{stem}.tsv').open(),delimiter='\t'))
 by_user={row['user']:row['ocaml'] for row in manifest}
 roots=[by_user[name] for name in entry['roots']]
 folder,library=('gen','effect4_gen') if stem=='api_gen' else ('engine','effect4_engine')
 implementation=fresh/(stem+'.ml')
 shutil.copyfile(r/entry['out'],implementation)
 subprocess.run([*compiler,'-c',str(implementation)],cwd=fresh,check=True)
 cmt=implementation.with_suffix('.cmt')
 abstract='checked,memo,oracle,hit_rule,live' if stem=='api_gen' else ''
 target=overlay/Path(entry['out']).relative_to('ocaml').with_suffix('.mli')
 command=['opam','exec','--switch=effect4','--',str(r/'ocaml/_build/default/gen/interface/main.exe'),str(cmt),str(target),','.join(roots),abstract,str(r/entry['prelude']) if entry.get('prelude') else '']
 subprocess.run(command,cwd=r,check=True)
 print('overlay typed-tree interface',target,flush=True)
shutil.rmtree(fresh)
subprocess.run(['opam','exec','--switch=effect4','--','dune','build','--root',str(overlay)],cwd=r,check=True)
