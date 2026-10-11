#!/usr/bin/env python3
"""Check the context signature probe with the existing pinned truth dependencies."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

parser = argparse.ArgumentParser()
parser.add_argument('--truth', type=Path, required=True)
args = parser.parse_args()
modules = args.truth.resolve() / 'node_modules'
for package, expected in [('effect', '4.0.0-rc.112'), ('@typescript/native-preview', '7.0.0-dev.20260629.1')]:
    actual = json.loads((modules / package / 'package.json').read_text())['version']
    if actual != expected:
        raise SystemExit(f'REFUSE {package}: expected {expected}, found {actual}')
    print(f'{package} {actual}', flush=True)
probe = Path(__file__).resolve().with_name('Signatures.ts')
config = {'compilerOptions': {'strict': True, 'noEmit': True, 'target': 'ESNext',
    'module': 'NodeNext', 'moduleResolution': 'NodeNext',
    'paths': {'effect': [str(modules / 'effect/dist/index.d.ts')]}}, 'files': [str(probe)]}
with tempfile.TemporaryDirectory(prefix='effect4-context-types-') as output:
    path = Path(output) / 'tsconfig.json'
    path.write_text(json.dumps(config))
    subprocess.run([str(modules / '.bin/tsgo'), '--project', str(path)], check=True)
print('PASS typed context reader, provideContext and callback signature controls')
