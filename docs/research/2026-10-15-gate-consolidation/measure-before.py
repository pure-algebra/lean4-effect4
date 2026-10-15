import json
import os
import subprocess
import time
from pathlib import Path

root = Path('/home/kokok/Dev/lean4-effect4-gates')
folder = root / 'scratch/before'
folder.mkdir(parents=True, exist_ok=True)
targets = ['check', 'check-native', 'check-compiler', 'check-ocaml', 'check-schema-codec',
           'check-schema-ts', 'check-truth', 'check-target', 'check-ts-reader',
           'check-host-protocol', 'check-corpus', 'check-tsdiag', 'check-ingest-smoke']
rows = []
source = root / 'src/Effect4/Codegen/Names.lean'
original = source.read_bytes()
try:
    for phase in ['cold', 'warm', 'core-edit', 'noop-checkout']:
        if phase == 'core-edit':
            source.write_bytes(original + b'\n-- Gate timing: one core source edit.\n')
        if phase == 'noop-checkout':
            # Rewrite identical bytes, as a checkout does, retaining the measured edit.
            # This isolates mtime invalidation from the preceding content change.
            tracked = subprocess.check_output(['git', 'ls-files', '-z'], cwd=root).decode().split('\0')
            for name in filter(None, tracked):
                path = root / name
                if path.is_file() and not path.is_symlink():
                    path.write_bytes(path.read_bytes())
        for target in targets:
            started = time.monotonic()
            with (folder / f'{phase}-{target}.log').open('w') as output:
                process = subprocess.run(['make', '--no-print-directory', target], cwd=root,
                                         stdout=output, stderr=subprocess.STDOUT)
            row = {'phase': phase, 'target': target, 'seconds': round(time.monotonic() - started, 3),
                   'exit': process.returncode}
            rows.append(row)
            (folder / 'results.json').write_text(json.dumps(rows, indent=2) + '\n')
            print(json.dumps(row), flush=True)
finally:
    source.write_bytes(original)
