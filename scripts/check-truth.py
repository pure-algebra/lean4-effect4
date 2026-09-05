#!/usr/bin/env python3
"""Bounded Lean/rc.112 differential, with pinned host selection and drift refusal."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
truth = root / 'harness/truth'
modules = Path(os.environ.get('EFFECT4_EFFECT_NODE_MODULES', root / 'ts/eff/node_modules')).resolve()
package = modules / 'effect/package.json'
if not package.is_file() or json.loads(package.read_text())['version'] != '4.0.0-rc.112':
    sys.exit('FAIL truth: EFFECT4_EFFECT_NODE_MODULES must contain effect@4.0.0-rc.112')
bun = shutil.which('bun') or shutil.which('bun.exe')
if not bun:
    sys.exit('FAIL truth: bun is required')
def host_path(path):
    if os.name != 'nt' and bun.lower().endswith('.exe'):
        return subprocess.check_output(['wslpath', '-w', str(path)], text=True).strip()
    return str(path)

# Bun resolves imports relative to the runner. An existing link must select the same pin.
link = truth / 'node_modules'
if link.exists():
    if not (link / 'effect').samefile(modules / 'effect'):
        sys.exit('FAIL truth: harness/truth/node_modules selects a different installation; use its path or relink explicitly')
elif os.name == 'nt':
    script = "New-Item -ItemType Junction -Path $env:E4_TRUTH_LINK -Target $env:E4_TRUTH_MODULES | Out-Null"
    subprocess.run(['pwsh', '-NoProfile', '-Command', script], check=True,
                   env={**os.environ, 'E4_TRUTH_LINK': str(link), 'E4_TRUTH_MODULES': str(modules)})
else:
    link.symlink_to(modules, target_is_directory=True)

inputs = list(truth.glob('*.ts')) + list(truth.glob('*.lean')) + [package, Path(__file__),
          root/'lean-toolchain', root/'lake-manifest.json']
inputs += sorted((root/'src/Effect4').rglob('*.lean'))
inputs += [truth/'corpus.json', truth/'result.json', truth/'result.md']
inputs += sorted((truth/'generated').glob('*.ts'))
# The package version alone cannot detect locally changed host implementations.
inputs += sorted(path for path in package.parent.rglob('*') if path.is_file())
digest = hashlib.sha256()
for path in inputs:
    digest.update(str(path).encode() + b'\0' + path.read_bytes())
digest.update(subprocess.check_output([bun, '--version']))
stamp_dir = root/'.lake/stamps/truth'
stamp = stamp_dir/digest.hexdigest()
if stamp.exists() and os.environ.get('EFFECT4_FORCE') != '1':
    print('PASS truth: unchanged; skipped (EFFECT4_FORCE=1 re-runs)')
    sys.exit(0)
with tempfile.TemporaryDirectory(prefix='truth-check-', dir=truth) as work:
    # Generated modules import ../prelude.ts and resolve Effect from their parent tree.
    # Keep the temporary run beneath the selected installation link, as the real run is.
    shutil.copyfile(truth/'prelude.ts', Path(work)/'prelude.ts')
    manifest = Path(work)/'corpus.json'
    subprocess.run(['lake', 'env', 'lean', '-M4096', '--run', 'harness/truth/Truth.lean', str(manifest)],
                   cwd=root, check=True, timeout=540)
    subprocess.run([bun, 'run', host_path(truth/'run-truth.ts'), '--manifest', host_path(manifest),
                    '--out', host_path(Path(work)), '--timeout', '300'], cwd=root, check=True, timeout=180)
    for name in ['corpus.json', 'result.json', 'result.md']:
        if (Path(work)/name).read_bytes() != (truth/name).read_bytes():
            sys.exit(f'FAIL truth: harness/truth/{name} drifted; inspect the regenerated differential before refreshing')
    generated = Path(work)/'generated'
    expected = truth/'generated'
    if sorted(p.name for p in generated.glob('*.ts')) != sorted(p.name for p in expected.glob('*.ts')):
        sys.exit('FAIL truth: generated module inventory drifted')
    for file in generated.glob('*.ts'):
        if file.read_bytes() != (expected/file.name).read_bytes():
            sys.exit(f'FAIL truth: generated module {file.name} drifted')
stamp_dir.mkdir(parents=True, exist_ok=True)
for old in stamp_dir.iterdir():
    if old.is_file(): old.unlink()
stamp.write_text('bounded corpus differential agrees with rc.112\n')
print('PASS truth: pinned corpus and bounded exit/schedule differential agree')
