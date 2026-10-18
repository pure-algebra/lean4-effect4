from pathlib import Path
import importlib.util, sys, json, subprocess
out=Path('/private/tmp/seams-st1a-m2')
root=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4')
sys.path.insert(0,str(root/'scripts'))
spec=importlib.util.spec_from_file_location('seams_generate',out/'scripts/generate.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
g.ROOT=out/'family-root'
def refuse_command(*args,**kwargs):
    raise AssertionError('output alias was not refused before a command')
g.run=refuse_command
before={p:p.read_bytes() for p in (g.ROOT/'rocq').glob('*.v')}
with (out/'family-alias-controls.log').open('w') as log:
    try:
        g.generate(['store-rocq'],str(g.ROOT))
    except ValueError as error:
        assert str(error)=='rocq/Skeleton.v: check output aliases repository destination',str(error)
        assert all(p.read_bytes()==data for p,data in before.items())
        log.write('PASS red control: aliased check output refuses before running commands or writing canonical files\n')
    else:
        raise AssertionError('aliased check output passed')
    command=['python3','scripts/generate.py','--only','rocq']
    log.write(json.dumps({'baseline_command':command})+'\n');log.flush()
    p=subprocess.run(command,cwd=root,stdout=log,stderr=subprocess.STDOUT)
    assert p.returncode==2,p.returncode
    log.write('PASS baseline red control: --only rocq refuses with exit 2\n')
print('PASS alias refusal and invalid baseline family controls')
