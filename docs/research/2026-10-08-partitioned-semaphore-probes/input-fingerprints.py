"""Measure the selected runtime, source, compiler, and probe inputs without installing."""
import hashlib
import json
import subprocess
from pathlib import Path

primary = Path('/Users/pooks/Dev/lean4-effect4')
packet = Path(__file__).resolve().parent
installed = primary / 'ts/release/node_modules/effect'
compiler = primary / 'ts/eff/node_modules/@typescript/native-preview'
bun_version = subprocess.check_output(['bun', '--version'], text=True).strip()
tsgo_version = subprocess.check_output([str(primary / 'ts/eff/node_modules/.bin/tsgo'), '--version'], text=True).strip()
effect_version = json.loads((installed / 'package.json').read_text())['version']
assert bun_version == '1.4.2', bun_version
assert effect_version == '4.0.1', effect_version
assert tsgo_version == 'Version 7.0.0-dev.20260629.1', tsgo_version

inputs = {}
def measure(label, path):
    content = path.read_bytes()
    inputs[label] = {'sha256': hashlib.sha256(content).hexdigest(), 'bytes': len(content)}

for name in ['package.json', 'src/PartitionedSemaphore.ts', 'src/MutableHashMap.ts', 'src/internal/effect.ts',
             'src/internal/core.ts', 'dist/Effect.js', 'dist/Fiber.js', 'dist/PartitionedSemaphore.js',
             'dist/MutableHashMap.js', 'dist/internal/effect.js', 'dist/internal/core.js']:
    measure('installed-effect/' + name, installed / name)
for name in ['PartitionedSemaphore.ts', 'MutableHashMap.ts', 'internal/effect.ts', 'internal/core.ts']:
    measure('vendor-effect/' + name, primary / 'vendor/effect-4.0.1/src' / name)
    assert inputs['vendor-effect/' + name]['sha256'] == inputs['installed-effect/src/' + name]['sha256']
measure('compiler/package.json', compiler / 'package.json')
for name in ['host-controls.ts', 'tsconfig.json', 'package.json', 'run.sh', 'input-fingerprints.py']:
    measure('packet/' + name, packet / name)
print(json.dumps({'effect': effect_version, 'bun': bun_version, 'tsgo': tsgo_version,
                  'source_pairs_equal': 4, 'selected_input_count': len(inputs), 'inputs': inputs}, indent=2))
