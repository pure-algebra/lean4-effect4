import json, re, hashlib, subprocess
from pathlib import Path
root = Path('/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4')
out = Path(__file__).parent
changed = {'ProofGraph.Proof', 'ProofGraph.Ledger', 'ProofGraph.Search',
           'Effect4.Laws.Auto.Obligations', 'Effect4.Program.Authoring.Sugar',
           'Test.Audit.ProofGraph', 'Test.Program.AuthoringScope'}
roots = ['Effect4.Laws.Machine.Approximation', 'Effect4.Laws.Machine.Scheduling', 'Test.Program.TypedProgBindRed', 'Test.Program.BlameContract', 'Test.Api.TestClockContract', 'Effect4.Laws.Program.Authoring.Forms', 'Test.Audit.ProofGraph', 'Test.Audit.Obligations',
         'Conform.Core.Proof', 'Effect4.Laws.Auto.Frames', 'Test.Program.AuthoringScope',
         'Effect4.Laws.Machine.Handles', 'Test.Machine.Runtime.HandlesContract',
         'Effect4.Laws.Program.Handles.Alphabet', 'Effect4.Laws.Program.Guard.FrameOwned',
         'Effect4.Laws.Program.Typed.World', 'Effect4.Laws.Program.Admit',
         'Effect4.Laws.Machine.Folds.Val', 'Effect4.Laws.Machine.StoresValue']
changed.add('Test.Machine.Runtime.HandlesContract')
for receipt in out.glob('*.json'):
    try:
        data = __import__('json').loads(receipt.read_text())
        cmd = data.get('command', [])
        if data.get('exit') == 0 and '-o' in cmd:
            path = cmd[cmd.index('-o')+1]
            changed.add(path.split('/lib/lean/')[-1].removesuffix('.olean').replace('/', '.'))
    except (ValueError, KeyError, AttributeError):
        pass
packages = list((root / '.lake/packages').iterdir())
def source(name):
    tail = Path(*name.split('.')).with_suffix('.lean')
    for base in [root/'src',root/'tools',root,*packages]:
        if (base/tail).is_file(): return base/tail, base
    return None, None
rows, files, seen, missing = [], [], set(), []
def walk(name):
    if name in seen: return
    seen.add(name)
    src, base = source(name)
    if src is None: return # bundled Lean/Init/Std/Lake compiler modules
    text = src.read_text()
    for line in text.splitlines():
        m = re.match(r'^(?:public |meta )*import\s+([\w.]+)', line)
        if m: walk(m[1])
    is_project = base in [root/'src',root/'tools',root]
    build = (root if is_project else base) / '.lake/build/lib/lean'
    artifact = build / Path(*name.split('.')).with_suffix('.olean')
    trace = artifact.with_suffix('.trace')
    item = dict(module=name, source=str(src), sourceSha256=hashlib.sha256(src.read_bytes()).hexdigest(),
                artifact=str(artifact), rebuilt=name in changed)
    if name not in changed:
        if not trace.is_file() or not artifact.is_file():
            missing.append(name)
        else:
            receipt = json.loads(trace.read_text())
            expected_sources = [val for key,val in receipt['inputs'] if isinstance(key,str) and key.endswith('.lean')]
            if len(expected_sources)!=1: raise ValueError((name,expected_sources))
            rows.append(('text', str(src), expected_sources[0]))
            for output in receipt['outputs']['o']:
                digest, suffix = output.split('.',1)
                path = artifact.with_suffix('.'+suffix)
                rows.append(('bin',str(path),digest))
            item['traceSha256'] = hashlib.sha256(trace.read_bytes()).hexdigest()
    files.append(item)
for name in roots: walk(name)
(out/'cache-hashes.tsv').write_text(''.join('\t'.join(row)+'\n' for row in rows))
(out/'cache-manifest.json').write_text(json.dumps(dict(roots=roots, sources=files, missing=missing),indent=2)+'\n')
print(json.dumps(dict(sourceModules=len(files),checks=len(rows),missing=missing)))
