from pathlib import Path
import subprocess,os,hashlib,json
out=Path('/private/tmp/seams-st1b-sol');red=out/'policy-red-native'
assert not red.exists()
subprocess.run(['cp','-c','-R',str(out/'ocaml'),str(red)],check=True)
p=red/'engine/cas/e4_root_policy.ml';before=p.read_text();after=before.replace('1 -> Some Journal','1 -> Some Swap');assert before!=after;p.write_text(after)
command=['opam','exec','--switch=effect4','--','dune','exec','--root',str(red),'engine/cas/test/test_shared_facts.exe']
with (out/'policy-native-red.log').open('w') as log:
 log.write(json.dumps({'command':command,'original_sha256':hashlib.sha256(before.encode()).hexdigest(),'mutated_sha256':hashlib.sha256(after.encode()).hexdigest()})+'\n');log.flush()
 p=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,env={**os.environ,'E4_CAS_GOLDENS':str(out/'ocaml/engine/cas/goldens')})
 log.write('exit_status='+str(p.returncode)+'\n')
assert p.returncode!=0
assert 'policy byte round trip' in (out/'policy-native-red.log').read_text()
print('actual shared-facts fixture detects mutated policy map',flush=True)
