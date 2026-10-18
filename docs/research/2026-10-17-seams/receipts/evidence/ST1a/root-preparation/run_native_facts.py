from pathlib import Path
import subprocess,json,sys
root=Path('/private/tmp/seams-st1a-root/native-facts')
log=Path('/private/tmp/seams-st1a-root/native-facts.log')
modules=['eff_frame','e4_be','e4_hex','e4_sha256','e4_kind','e4_addr','e4_node','e4_admission']
base=['opam','exec','--switch=effect4','--','ocamlfind','ocamlc','-package','zarith','-w','+a-4-9-40-41-42-44-45-70','-warn-error','+a-4-9-40-41-42-44-45-70']
with log.open('w') as f:
 def run(cmd,expect=0):
  f.write(json.dumps({'command':cmd})+'\n');f.flush()
  p=subprocess.run(cmd,cwd=root,stdout=f,stderr=subprocess.STDOUT)
  f.write(f'exit_status={p.returncode}\n');f.flush()
  if (expect==0 and p.returncode!=0) or (expect!=0 and p.returncode==0):
   print(log.read_text()[-5000:]);sys.exit(1)
 for name in modules:
  if (root/(name+'.mli')).exists():run(base+['-c',name+'.mli'])
  run(base+['-c',name+'.ml'])
 run(base+['-linkpkg','-o','test_shared_facts']+[name+'.cmo' for name in modules]+['test_shared_facts.ml'])
 run(['opam','exec','--switch=effect4','--','./test_shared_facts'])
 original=(root/'e4_admission.ml').read_text()
 needle='E4_node.Unknown_tag a0 -> Model (Unknown_tag a0)'
 assert needle in original
 (root/'e4_admission.ml').write_text(original.replace(needle,'E4_node.Unknown_tag _ -> Model Oversize'))
 try:
  run(base+['-c','e4_admission.ml'])
  run(base+['-linkpkg','-o','test_shared_facts_red']+[name+'.cmo' for name in modules]+['test_shared_facts.ml'])
  run(['opam','exec','--switch=effect4','--','./test_shared_facts_red'],expect=1)
 finally:
  (root/'e4_admission.ml').write_text(original)
 run(base+['-c','e4_admission.ml'])
print(log.read_text()[-1800:])
