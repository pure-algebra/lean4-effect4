from pathlib import Path
import subprocess, json, sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
suffix=sys.argv[1] if len(sys.argv)>1 else ''
def run(name,cwd,*cmd):
 subprocess.run([sys.executable,str(HERE/'check.py'),name+suffix,cwd,*cmd],cwd=ROOT,check=True)
run('narrow-tests','.', 'lake','build','Test.Counterexamples.Machine.Runtime.LayerEnvironment','Test.Program.RuntimeRContract','Test.Program.ProvisionContract','Test.Program.LayerSharingContract','Test.Program.CompileContract','Test.Program.DenoteRContract')
run('axioms','.', 'lake','env','lean','-DwarningAsError=true','docs/research/2026-09-30-seat-codex-slice6-evidence/F/axioms.lean')
def changed_paths():
 return set(subprocess.check_output(['git','diff','--name-only','HEAD'],cwd=ROOT,text=True).splitlines()) | set(subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=ROOT,text=True).splitlines())
base=changed_paths()
outputs={'ocaml/gen/fibers_gen.ml','ocaml/gen/machine_gen.ml','ocaml/gen/api_gen.ml','ocaml/engine/api_engine.ml','ocaml/gen/closure-api_gen.tsv','ocaml/gen/closure-api_engine.tsv','ocaml/engine/e4_program_layout.ml','ocaml/engine/e4_program_layout.json'}
prefixes=('ocaml/eff/','ocaml/goldens/eff/','ocaml/engine/cas/goldens/')
for group in ('derived','lcnf','eff','wire','cas'):
 run('gen-'+group,'.','make','gen-'+group)
 changed=changed_paths()
 extra=sorted(p for p in changed-base if p not in outputs and not p.startswith(prefixes))
 (HERE/('gen-'+group+suffix+'-paths.json')).write_text(json.dumps({'changed':sorted(changed),'outside_scope':extra},indent=2)+'\n')
 if extra: raise SystemExit('Scope stop: '+repr(extra))
run('dune','ocaml','opam','exec','--switch=effect4','--','dune','build')
run('engine-test','ocaml','opam','exec','--switch=effect4','--','dune','exec','engine/test/test_engine.exe')
run('check-ocaml','.','make','check-ocaml')
