from pathlib import Path
import importlib.util, os, subprocess, sys, shutil, json
out=Path('/private/tmp/seams-st1a-m2')
root=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4')
sys.path.insert(0,str(root/'scripts'))
spec=importlib.util.spec_from_file_location('seams_generate',out/'scripts/generate.py')
g=importlib.util.module_from_spec(spec)
spec.loader.exec_module(g)
fixture=out/'family-root'
(fixture/'rocq').mkdir(parents=True,exist_ok=True)
for name in ['Skeleton.v','StoreCode.v']:
    shutil.copy2(root/'rocq'/name,fixture/'rocq'/name)
g.ROOT=fixture
env=dict(os.environ)
env['LEAN_PATH']=str(out/'lib/lean')+':'+env.get('LEAN_PATH','')
env['LEAN_NUM_THREADS']='3'
os.chdir(root)
with (out/'family-controls.log').open('w') as log:
    def run_overlay(args,capture=False):
        log.write(json.dumps({'requested':args,'scope':'temporary module overlay and output root'})+'\n')
        if args[:2]==['lake','build']:
            assert args[2:]==['Effect4.Run.Tree','Effect4.Store.Domain.Word','OCaml5.Lcnf.Gallina']
            command=['python3',str(out/'build_overlay.py'),'Effect4.Store.Carrier.Kind','Effect4.Store.Domain.Node','Effect4.Store.Domain.NodeRead','Effect4.Store.Domain.Store','Effect4.Store.Domain.Word','OCaml5.Lcnf.Gallina']
        else:
            assert args[:3]==['lake','env','lean']
            command=args[2:]
            command[1:1]=['-DwarningAsError=true']
            command[command.index('src/OCaml5/Tools/GallinaGen.lean')]=str(out/'src/OCaml5/Tools/GallinaGen.lean')
        log.write(json.dumps({'actual_under_outer_lean_launcher':command})+'\n');log.flush()
        subprocess.run(command,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,check=True)
        return None
    g.run=run_overlay
    sys.argv=[str(out/'scripts/generate.py'),'--only','store-rocq']
    g.main()
    actual=(fixture/'rocq/StoreCode.v').read_bytes()
    assert actual==(out/'rocq/StoreCode.v').read_bytes()
    assert (fixture/'rocq/Skeleton.v').read_bytes()==(root/'rocq/Skeleton.v').read_bytes()
    log.write('PASS: store-rocq CLI regenerates current StoreCode and leaves Skeleton unchanged\n');log.flush()
    checkdir=out/'family-check'
    g.generate(['store-rocq'],str(checkdir))
    assert (checkdir/'rocq/StoreCode.v').read_bytes()==actual
    log.write('PASS: output-dir checks the current StoreCode and writes the same output bytes\n');log.flush()
    (fixture/'rocq/Skeleton.v').write_bytes(b'changed skeleton control\n')
    try:
        g.generate(['store-rocq'],None)
    except ValueError as error:
        assert str(error)=='rocq/Skeleton.v is not what Lean emits',str(error)
        assert (fixture/'rocq/StoreCode.v').read_bytes()==actual
        log.write('PASS red control: changed Skeleton refuses before installing StoreCode\n')
        print('PASS red control: changed Skeleton refuses before StoreCode install',flush=True)
    else:
        raise AssertionError('changed Skeleton did not refuse')
    (fixture/'rocq/Skeleton.v').write_bytes((root/'rocq/Skeleton.v').read_bytes())
print('PASS temporary store-rocq family controls',flush=True)
