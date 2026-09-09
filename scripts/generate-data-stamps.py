#!/usr/bin/env python3
"""Reproduce the report or archive input bytes, then write their adjacent stamps.

Run under the Lean lane lock. Original data formats and their gates are unchanged.
"""

import json
import re
import os
from pathlib import Path
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
os.chdir(root)
family, = sys.argv[1:]
sources = {
    'census': 'scripts/generate-effect-runtime-census.sh',
    'assurance': 'scripts/generate-schema-structural-assurance.sh',
    'archived': 'ocaml/server/tools/vendor-archived-inputs.sh',
}
source = sources[family]
if not (root / '.lake/LANE.lock').is_dir():
    sys.exit('Hold .lake/LANE.lock before running a Lean producer')

if family == 'archived':
    manifest = Path('ocaml/server/generated/archived-from.tsv')
    lines = manifest.read_text().splitlines()
    outputs = [manifest]
    revision = lines[0].split('\t')[1]
    for row in lines[1:]:
        dest, origin, blob = row.split('\t')
        target = Path('ocaml/server') / dest
        actual = subprocess.check_output(['git', 'show', f'{revision}:{origin}'])
        actual_blob = subprocess.check_output(['git', 'rev-parse', f'{revision}:{origin}'], text=True).strip()
        if target.read_bytes() != actual or actual_blob != blob:
            sys.exit(f'FAIL archived input differs from its recorded blob: {target}')
        outputs.append(target)
    inputs = outputs
else:
    output = Path('generated') / ('effect-runtime-census.tsv' if family == 'census'
                                  else 'schema-structural-assurance.tsv')
    fresh = subprocess.check_output(['bash', source], timeout=600)
    if fresh != output.read_bytes():
        sys.exit(f'FAIL {output} differs from its producer; metadata was not written')
    outputs = [output]
    # Reports list their input paths beside the hashes they checked. Include all
    # those existing files, in addition to the producer and report bytes.
    inputs = [output] + [Path(field) for line in fresh.decode().splitlines()
                        for field in line.split('\t') if re.fullmatch(r'[A-Za-z0-9_./-]+', field) and Path(field).is_file()]

with tempfile.TemporaryDirectory(prefix='effect4-data-stamps-') as directory:
    recipe = Path(directory) / 'recipe.json'
    recipe.write_text(json.dumps({'source': source,
        'inputs': sorted(set(str(p) for p in inputs) | {str(Path(__file__).relative_to(root))}),
        'outputs': [str(p) for p in outputs]}))
    subprocess.run(['lake', 'env', 'lean', '-M4096', '--run', 'tools/Tools/StampFiles.lean',
                    str(recipe)], check=True, timeout=600)
print(f'PASS {family}: {len(outputs)} artifacts reproduced; separate stamps written')
