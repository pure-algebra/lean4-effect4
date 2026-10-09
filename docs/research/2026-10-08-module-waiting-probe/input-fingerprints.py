#!/usr/bin/env python3
"""Identify selected local runtime and compiler inputs; not the full import graph."""
import hashlib
import json
from pathlib import Path
import subprocess

primary = Path('/Users/pooks/Dev/lean4-effect4')
effect = primary / 'ts/release/node_modules/effect'
compiler = primary / 'ts/eff/node_modules/.bin/tsgo'
root = Path(__file__).resolve().parents[3]
version = json.loads((effect / 'package.json').read_text())['version']
compiler_version = subprocess.check_output([str(compiler), '--version'], text=True).strip()
if version != '4.0.1':
    raise SystemExit(f'Unexpected Effect version: {version}')
if compiler_version != 'Version 7.0.0-dev.20260629.1':
    raise SystemExit(f'Unexpected compiler: {compiler_version}')
files = {}
equal_source_pairs = []
for name in ['Effect', 'Fiber', 'PartitionedSemaphore', 'Queue', 'internal/effect']:
    vendor = root / f'vendor/effect-4.0.1/src/{name}.ts'
    installed = effect / f'src/{name}.ts'
    if vendor.read_bytes() != installed.read_bytes():
        raise SystemExit(f'Vendor/installed source differs: {name}')
    equal_source_pairs.append(name)
    for label, path in [(f'vendor/{name}.ts', vendor),
                        (f'installed/{name}.ts', installed),
                        (f'dist/{name}.js', effect / f'dist/{name}.js')]:
        data = path.read_bytes()
        files[label] = {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
for label, path in [('runtime-package', effect / 'package.json'),
                    ('compiler-package', primary / 'ts/eff/node_modules/@typescript/native-preview/package.json')]:
    data = path.read_bytes()
    files[label] = {'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}
print(json.dumps({'effect': version, 'compiler': compiler_version,
                  'bun': subprocess.check_output(['bun', '--version'], text=True).strip(),
                  'selected_input_count': len(files),
                  'equal_source_pairs': equal_source_pairs, 'inputs': files}, indent=2))
