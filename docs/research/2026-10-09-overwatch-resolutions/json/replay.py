#!/usr/bin/env python3
"""Finite source-pinned JSON admission probe using existing Lean artifacts; no Lake build."""
import argparse, hashlib, json, os, pathlib, subprocess
p = argparse.ArgumentParser()
p.add_argument('--repo', type=pathlib.Path, default=pathlib.Path('/Users/pooks/Dev/lean4-effect4'))
p.add_argument('--out', type=pathlib.Path, required=True)
a = p.parse_args()
if a.out.exists():
    raise SystemExit('Output path must be new')
a.out.mkdir(parents=True)
pin = '8811a61bab98a6d07e897c3361a703f5729c9c82'
sources = ['src/Effect4/Store/Domain/ShapeRead.lean', 'src/Effect4/Laws/Store/ShapeRead.lean',
           'tools/Tools/JsonBridge.lean', 'tools/Tools/Session.lean', 'Test/Program/JsonFormControls.lean', 'Test/Program/SessionToolControls.lean']
hashes = {}
for name in sources:
    pinned = subprocess.check_output(['git', 'show', f'{pin}:{name}'], cwd=a.repo)
    if pinned != (a.repo / name).read_bytes():
        if name != 'Test/Program/SessionToolControls.lean':
            raise SystemExit(f'Audited source changed: {name}')
        current = a.out / 'current-source' / name
        current.parent.mkdir(parents=True, exist_ok=True)
        current.write_bytes((a.repo / name).read_bytes())
        hashes['current:' + name] = hashlib.sha256(current.read_bytes()).hexdigest()
    target = a.out / 'source' / name
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(pinned)
    hashes[name] = hashlib.sha256(pinned).hexdigest()
driver = a.out / 'SessionDriver.lean'
driver.write_bytes(subprocess.check_output(['git', 'show', f'{pin}:tools/Drivers/Session.lean'], cwd=a.repo))
controls = [('small', 7), ('exact-boundary', 2**53), ('exact-large', 2**53+2),
            ('rounded-input', 2**53+1), ('fractional', 3.5), ('negative', -1)]
lines = []
for name, value in controls:
    lines += [json.dumps({'op':'open','id':name,'programJson':{'_tag':'succeed','value':{'_tag':'lit','value':{'_tag':'nat','value':value}}}}),
              json.dumps({'op':'sketch','id':name})]
for name, value in [('fill-small', 11), ('fill-rounded', 2**53+1), ('fill-exact-large', 2**53+2)]:
    lines += [json.dumps({'op':'fill','path':[],'id':name,'replacementJson':{'_tag':'succeed','value':{'_tag':'lit','value':{'_tag':'nat','value':value}}}}), json.dumps({'op':'sketch','id':name})]
requests = '\n'.join(lines) + '\n' 
(a.out / 'requests.jsonl').write_text(requests)
env = os.environ.copy()
env['LEAN_NUM_THREADS'] = '3'
env['LEAN_PATH'] = ':'.join(str(path) for path in [a.repo / '.lake/build/lib/lean', *sorted((a.repo / '.lake/packages').glob('*/.lake/build/lib/lean'))])
lean = pathlib.Path('/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean')
command = [str(lean), '--run', str(driver)]
result = subprocess.run(command, cwd=a.out, env=env, input=requests, capture_output=True, text=True)
(a.out / 'answers.jsonl').write_text(result.stdout)
(a.out / 'stderr.log').write_text(result.stderr)
if result.returncode != 0:
    raise SystemExit(f'Lean driver failed: {result.returncode}: {result.stderr}')
answers = [json.loads(line) for line in result.stdout.splitlines()]
assert len(answers) == len(lines)
summary = []
programs = {}
for index, (name, value) in enumerate(controls):
    opened, sketch = answers[2*index:2*index+2]
    observed = sketch['result']['programJson']['value']['value']['value']
    programs[name] = sketch['result']['program']
    if name in ['rounded-input','fractional','negative']:
        assert not opened['ok'], name
        assert opened['error'] == 'the program does not read', opened
        assert observed == 2**53+2, (name, observed)
    else:
        assert opened['ok'] and opened['result']['refusals'] == [], opened
        assert observed == value, (name, observed)
        assert 'Effect4.Store.Canonical.ofJson_exact' in opened['laws'], opened
    summary.append({'control':name, 'input':value, 'accepted':opened['ok'], 'returnedNat':observed})
assert programs['rounded-input'] == programs['exact-large']
for index, (name, value) in enumerate([('fill-small',11), ('fill-rounded',2**53+1), ('fill-exact-large',2**53+2)]):
    filled, sketch = answers[2*len(controls)+2*index:2*len(controls)+2*index+2]
    observed = sketch['result']['programJson']['value']['value']['value']
    if name == 'fill-rounded':
        assert not filled['ok'] and filled['error'] == 'the filling does not read'
        assert observed == 11
        assert sketch['result']['program'] == prior_fill_program
    else:
        assert filled['ok'] and filled['result']['view']['refusals'] == []
        assert observed == value
        assert 'Tools.JsonBridge.ofLeanJson_num' in filled['laws']
        prior_fill_program = sketch['result']['program']
    summary.append({'control':name,'input':value,'accepted':filled['ok'],'returnedNat':observed})
(a.out / 'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
for name in ['Tools/Session.olean','Tools/JsonBridge.olean','Effect4/Store/Domain/ShapeRead.olean','Effect4/Laws/Store/ShapeRead.olean','Test/Program/SessionToolControls.olean']:
    path = a.repo / '.lake/build/lib/lean' / name
    hashes[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
hashes[str(lean)] = hashlib.sha256(lean.read_bytes()).hexdigest()
hashes[str(pathlib.Path(__file__).resolve())] = hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
(a.out / 'execution.json').write_text(json.dumps({'pin':pin,'command':command,'leanPath':env['LEAN_PATH'], 'leanNumThreads':env['LEAN_NUM_THREADS'],
    'exit':result.returncode,'leanVersion':subprocess.check_output([str(lean),'--version'],text=True).strip(),
    'currentHead':subprocess.check_output(['git','rev-parse','HEAD'],cwd=a.repo,text=True).strip(),
    'pythonVersion':subprocess.check_output(['python3','--version'],text=True).strip(),'hashes':hashes},indent=2)+'\n')
print(json.dumps(summary))
