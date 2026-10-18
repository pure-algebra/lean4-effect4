import subprocess,json
commands=[
 ['opam','exec','--switch=effect4','--','dune','build','--root','ocaml','gen/test_seams_s0.exe','engine/test/test_seams_step.exe'],
 ['opam','exec','--switch=effect4','--','dune','exec','--root','ocaml','gen/test_seams_s0.exe'],
 ['opam','exec','--switch=effect4','--','dune','exec','--root','ocaml','engine/test/test_seams_step.exe'],
 ['opam','exec','--switch=effect4','--','dune','runtest','--root','ocaml','gen/interface'],
 ['python3','scripts/check-lcnf-interfaces.py'],
 ['python3','scripts/check-lcnf-sealing.py'],
 ['git','diff','--check']]
for command in commands:
 print(json.dumps(command),flush=True)
 subprocess.run(command,check=True)
print('PASS S0 final production native controls',flush=True)
