"""Recheck scout source snapshots against the exact frozen Git commit."""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = Path('/Users/pooks/Dev/lean4-effect4')
COMMIT = 'a02126a85051ab7ec0be0a3bd30471feb18fbdd3'


def read_blob(path):
    result = subprocess.run(['git', '-C', str(REPO), 'show', f'{COMMIT}:{path}'],
                            capture_output=True, check=False)
    if result.returncode != 0:
        raise ValueError(f'missing frozen path: {path}')
    return result.stdout


def verify(entry):
    data = read_blob(entry['path'])
    digest = hashlib.sha256(data).hexdigest()
    if digest != entry['sha256'] or len(data) != entry['bytes']:
        raise ValueError(f'hash or length mismatch: {entry["path"]}')
    return {'path': entry['path'], 'sha256': digest, 'bytes': len(data), 'pass': True}


rows = []
for filename in ['generation/source-hashes.json', 'breadth/sources.json', 'proofs/hashes.json']:
    raw = json.loads((ROOT / filename).read_text())
    entries = raw if isinstance(raw, list) else raw['sources']
    for entry in entries:
        rows.append({'packet': filename, **verify(entry)})

for path in ['tools/ProofGraph/Goal.lean', 'tools/ProofGraph/Sketch.lean',
             'tools/ProofGraph/Plan.lean', 'tools/Tools/SemanticsRegistry.lean',
             'src/Effect4/Laws/Machine/Refinement.lean',
             'src/Effect4/Laws/Machine/RefKernel.lean',
             'src/Effect4/Laws/Program/MeaningEq.lean',
             'docs/core/system-map.md', 'tools/Tools/SemanticsRegistry.lean',
             'generated/semantics.md']:
    data = read_blob(path)
    rows.append({'packet': 'parent', 'path': path,
                 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data), 'pass': True})

controls = []
for label, entry in [('bad-hash', {**rows[0], 'sha256': '0' * 64}),
                     ('missing-file', {**rows[0], 'path': 'not-a-real-factory-review-source.lean'})]:
    try:
        verify(entry)
    except ValueError as error:
        controls.append({'control': label, 'refused': True, 'diagnostic': str(error)})
    else:
        raise AssertionError(f'{label} was not refused')

result = {'commit': COMMIT, 'comparisons': len(rows),
          'unique_paths': len({row['path'] for row in rows}),
          'all_match': all(row['pass'] for row in rows), 'checks': rows,
          'verifier_controls': controls,
          'exclusions': 'Byte verification and source review only; no Lean or native runtime result.'}
(ROOT / 'parent-verification.json').write_text(json.dumps(result, indent=2) + '\n')
print(f'{len(rows)} source comparisons passed, {result["unique_paths"]} unique paths; two refusal controls passed')
