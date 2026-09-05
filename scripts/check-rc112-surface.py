#!/usr/bin/env python3
"""Regenerate the pinned surface projection and refuse byte drift (portable Node driver)."""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
node = shutil.which('node') or shutil.which('node.exe')
if not node:
    sys.exit('FAIL rc112-surface: node is required')
def host_path(path):
    if os.name != 'nt' and node.lower().endswith('.exe'):
        return subprocess.check_output(['wslpath', '-w', str(path)], text=True).strip()
    return str(path)
names = ['rc112-surface.tsv', 'rc112-surface.json', 'rc112-surface.summary.txt']
inputs = [root / 'scripts/surface-export.mjs', Path(__file__), root / 'ts/eff/package.json']
inputs += sorted((root / 'vendor/effect-4.0.0-rc.112').rglob('*'))
inputs += [root / 'generated' / name for name in names]
compiler = Path(os.environ.get('EFFECT4_TYPESCRIPT_DIR', root / 'ts/eff/node_modules/typescript'))
if not (compiler / 'package.json').is_file():
    sys.exit('FAIL rc112-surface: install the pinned TypeScript compiler in ts/eff')
digest = hashlib.sha256()
digest.update(subprocess.check_output([node, '--version']))
digest.update((compiler / 'package.json').read_bytes())
digest.update((compiler / 'lib/typescript.js').read_bytes())
for file in inputs:
    if file.is_file():
        digest.update(str(file.relative_to(root)).encode() + b'\0' + file.read_bytes())
key = digest.hexdigest()
stamp_dir = root / '.lake/stamps/rc112-surface'
stamp = stamp_dir / key
if stamp.exists() and os.environ.get('EFFECT4_FORCE') != '1':
    print('PASS rc112-surface: unchanged; skipped (EFFECT4_FORCE=1 re-runs)')
    sys.exit(0)
(root / '.lake').mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='surface-check-', dir=root / '.lake') as work:
    result = subprocess.run([node, host_path(root / 'scripts/surface-export.mjs'), '--ts', host_path(compiler),
                             '--out', host_path(Path(work))],
                            cwd=root, capture_output=True, text=True, encoding='utf-8')
    if result.returncode:
        sys.stderr.write(result.stdout + result.stderr)
        sys.exit(result.returncode)
    for name in names:
        if (Path(work) / name).read_bytes() != (root / 'generated' / name).read_bytes():
            sys.exit(f'FAIL rc112-surface: generated/{name} differs; regenerate with node scripts/surface-export.mjs')
stamp_dir.mkdir(parents=True, exist_ok=True)
for old in stamp_dir.iterdir():
    if old.is_file(): old.unlink()
stamp.write_text('three projections match the pinned inputs\n')
print('PASS rc112-surface: all three projections match the pinned inputs')
