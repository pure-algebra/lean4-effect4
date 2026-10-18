from pathlib import Path
import subprocess, tempfile, shutil, hashlib, json
root=Path('/Users/pooks/.codex/worktrees/seams/lean4-effect4')
names=['Eff_types','StoreCode','StoreLaws','StoreGrammar','StoreAssumptions']
with tempfile.TemporaryDirectory(prefix='seams-st1a-rocq-') as directory:
    work=Path(directory)
    for name in names:
        source=root/'rocq'/(name+'.v')
        shutil.copyfile(source,work/source.name)
        print(json.dumps({'source':str(source.relative_to(root)),'sha256':hashlib.sha256(source.read_bytes()).hexdigest()}),flush=True)
    for name in names:
        command=['opam','exec','--switch=rocq','--','rocq','compile','-Q','.','E4',name+'.v']
        print('COMMAND',json.dumps(command),flush=True)
        result=subprocess.run(command,cwd=work)
        print(name,'exit',result.returncode,flush=True)
        if result.returncode:
            raise SystemExit(result.returncode)
