"""Exercise existing gate reuse and vector code, writing only beside this file."""
from pathlib import Path
import hashlib
import importlib.util
import json
import os
import subprocess
import sys

ROOT = Path('/Users/pooks/Dev/lean4-effect4')
HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True

spec = importlib.util.spec_from_file_location('review_gate_cache', ROOT/'scripts/lib/gate_cache.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
case = HERE/'gate-case'
case.mkdir(exist_ok=True)
(case/'input').write_text('fixed input\n')
(case/'invocations').write_text('')
key = gate.prepare(case, 'seams-command', ['input'])
commands = [[sys.executable, '-c', "from pathlib import Path; p=Path('invocations'); p.write_text(p.read_text()+'"+label+"\\n')"] for label in ['A', 'B']]
for command in [commands[0], commands[1], commands[1]]:
    assert gate.run(case, 'seams-command', command, store=case/'store') == 0
observed = (case/'invocations').read_text().splitlines()
assert observed == ['A', 'B'], observed
assert (case/'.lake/check/seams-command.key').read_text().strip() == key
print(json.dumps({'probe':'changed_gate_command','same_input_key':True,'invocations':observed,'third_call_reused':True}), flush=True)

project = HERE/'array-case'
project.mkdir(exist_ok=True)
sources = ['ocaml/lcnf/lcnf_array.ml', 'ocaml/engine/e4_log.ml', 'ocaml/engine/e4_trace.ml']
manifest = {}
for name in sources:
    contents = (ROOT/name).read_bytes()
    (project/Path(name).name).write_bytes(contents)
    manifest[name] = hashlib.sha256(contents).hexdigest()
(project/'sources.json').write_text(json.dumps(manifest, indent=2)+'\n')
(project/'dune-project').write_text('(lang dune 3.0)\n(name seams_array_probe)\n')
(project/'dune').write_text('(executable (name array_probe) (modules array_probe lcnf_array e4_log e4_trace))\n')
(project/'array_probe.ml').write_bytes((HERE/'array_probe.ml').read_bytes())
command = ['opam','exec','--switch=effect4','--','dune','exec','--root',str(project),'--build-dir',str(project/'_build'),'--profile','release','./array_probe.exe']
print(json.dumps({'probe':'array_allocations','command':command,'cwd':str(ROOT/'ocaml')}), flush=True)
run = subprocess.run(command, cwd=ROOT/'ocaml', stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
print(run.stdout, end='')
assert run.returncode == 0, run.returncode

