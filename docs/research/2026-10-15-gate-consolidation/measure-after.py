import json, os, shutil, subprocess, time
from pathlib import Path

root = Path('/home/kokok/Dev/lean4-effect4-gates-dev')
folder = root / 'scratch/after'
folder.mkdir(parents=True, exist_ok=True)
common = Path(subprocess.check_output(['git','rev-parse','--path-format=absolute','--git-common-dir'],cwd=root,text=True).strip())
store = common.parent / (common.name + '-checks')
archive = common.parent / (common.name + '-checks-before-after-timing')
if archive.exists():
    raise SystemExit('timing archive exists; preserve the previous run before repeating')
if store.exists():
    store.rename(archive)
steps = ['native','compiler','ocaml','schema-codec','schema-ts','truth','target','ts-reader','host-protocol','corpus','tsdiag','ingest-smoke','service-identity']
for name in steps + ['tsgo']:
    (root / '.lake/check' / name).unlink(missing_ok=True)
targets = [('check','check')] + [('check-'+s, '.lake/check/ocaml' if s == 'ocaml' else 'check-'+s) for s in steps]
rows = []
source = root / 'src/Effect4/Codegen/Names.lean'
original = source.read_bytes()
def measure(phase, label, target):
    started = time.monotonic()
    with (folder / f'{phase}-{label}.log').open('w') as log:
        result = subprocess.run(['make','--no-print-directory',target],cwd=root,stdout=log,stderr=subprocess.STDOUT)
    row = {'phase':phase,'target':label,'command_target':target,'seconds':round(time.monotonic()-started,3),'exit':result.returncode}
    rows.append(row)
    (folder/'results.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps(row),flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
try:
    for phase in ['cold','warm','core-edit','noop-checkout']:
        if phase == 'core-edit':
            source.write_bytes(original+b'\n-- Gate timing: one core source edit.\n')
        if phase == 'noop-checkout':
            tracked = subprocess.check_output(['git','ls-files','-z','--cached','--others','--exclude-standard'],cwd=root).decode().split('\0')
            for name in filter(None,tracked):
                path = root/name
                if path.is_file() and not path.is_symlink():
                    path.write_bytes(path.read_bytes())
        for label,target in targets:
            measure(phase,label,target)
        if phase in ['warm','noop-checkout']:
            measure(phase,'check-full','check-full')
finally:
    source.write_bytes(original)
    if archive.exists():
        for old in archive.rglob('*'):
            if old.is_file():
                target = store/old.relative_to(archive)
                target.parent.mkdir(parents=True,exist_ok=True)
                if not target.exists(): shutil.copyfile(old,target)
