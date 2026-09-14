#!/usr/bin/env python3
"""Bounded Lean/rc.112 differential, with pinned host selection and drift refusal.

Two phases, as before: Lean writes the manifest (reading the committed tapes under
harness/truth/tapes, the answers rc.112 gave the package rows last time), bun runs the
generated modules with the recording prelude and writes the observed result and fresh tapes,
and every committed artefact must equal the fresh one. A tape that moved fails the gate the
way corpus.json does: the answers Lean replayed are byte for byte the answers rc.112 just gave.

Between the two, one more refusal (DI-49): the freshly printed modules, their adapter, and the recorder/session sources
must type-check under the pinned compiler, `tsc --noEmit -p harness/truth/tsconfig.json`
copied beside them in the work directory. Running is not being well typed — `pKv.ts` ran for
months while its declared error type disagreed with what the shim could raise (TS2375) — so
the check is on the modules rc.112 just ran, before any byte is compared. Evidence word:
tested; a finite checker run, not byte reproduction (DI-32).

Whether to run at all is the Makefile's decision (`make check-truth` is keyed on the
harness, the tapes, the pinned host manifest and the compiled core); this script always runs.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(root / 'scripts/lib'))
import truth_host  # noqa: E402

truth = root / 'harness/truth'


def main():
    bun, modules, host_path = truth_host.select(root, truth)

    tapes = truth / 'tapes'
    tapes.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='truth-check-', dir=truth) as work:
        # Generated modules import ../prelude.ts and resolve Effect from their parent tree.
        # Keep the temporary run beneath the selected installation link, as the real run is.
        shutil.copyfile(truth/'prelude.ts', Path(work)/'prelude.ts')
        shutil.copytree(truth/'session', Path(work)/'session', ignore=shutil.ignore_patterns('.work'))
        manifest = Path(work)/'corpus.json'
        subprocess.run(['lake', 'env', 'lean', '-M4096', '--run', 'harness/truth/Truth.lean', str(manifest),
                        '--tapes', str(tapes)], cwd=root, check=True, timeout=540)
        subprocess.run([bun, 'run', host_path(truth/'run-truth.ts'), '--manifest', host_path(manifest),
                        '--out', host_path(Path(work)), '--timeout', '300',
                        '--tape-out', host_path(Path(work)/'tapes')], cwd=root, check=True, timeout=180)
        # DI-49: the modules rc.112 just ran, and the adapter they call, under the pinned
        # compiler. The config is copied beside them so that `generated/` and `prelude.ts`
        # resolve as they do in the tree, and `effect`/`@types/bun` through the link above.
        # Check the actual recorder and session sources as well. Copying them flat would
        # break their relative imports of the generated profile; absolute files preserve
        # source topology while prelude/generated are the freshly exercised copies.
        config = json.loads((truth/'tsconfig.json').read_text())
        config['files'] = [host_path(truth/'run-truth.ts')] + [
            host_path(path) for path in sorted((truth/'session').glob('*.ts'))]
        (Path(work)/'tsconfig.json').write_text(json.dumps(config, indent=2) + '\n')
        typed = subprocess.run([bun, host_path(modules/'typescript/bin/tsc'), '--pretty', 'false',
                                '--noEmit', '-p', host_path(Path(work)/'tsconfig.json')],
                               cwd=work, text=True, capture_output=True, timeout=300)
        if typed.returncode != 0:
            sys.exit('FAIL truth: the regenerated modules do not type-check under '
                     f'harness/truth/tsconfig.json:\n{typed.stdout}{typed.stderr}')
        for name in ['corpus.json', 'result.json', 'result.md']:
            if (Path(work)/name).read_bytes() != (truth/name).read_bytes():
                sys.exit(f'FAIL truth: harness/truth/{name} drifted; inspect the regenerated differential before refreshing (make gen-truth)')
        generated = Path(work)/'generated'
        expected = truth/'generated'
        if sorted(p.name for p in generated.glob('*.ts')) != sorted(p.name for p in expected.glob('*.ts')):
            sys.exit('FAIL truth: generated module inventory drifted')
        for file in generated.glob('*.ts'):
            if file.read_bytes() != (expected/file.name).read_bytes():
                sys.exit(f'FAIL truth: generated module {file.name} drifted')
        fresh = Path(work)/'tapes'
        fresh_names = sorted(p.name for p in fresh.glob('*')) if fresh.is_dir() else []
        if fresh_names != sorted(p.name for p in tapes.glob('*')):
            sys.exit(f'FAIL truth: tape inventory drifted: rc.112 recorded {fresh_names}, committed {sorted(p.name for p in tapes.glob("*"))}; install the fresh tapes deliberately')
        for file in fresh.glob('*') if fresh.is_dir() else []:
            if file.read_bytes() != (tapes/file.name).read_bytes():
                sys.exit(f'FAIL truth: tape {file.name} drifted; rc.112 answered differently from the committed tape')
    print('PASS truth: pinned corpus and bounded exit/schedule differential agree; '
          'the regenerated modules type-check')
    return 0


if __name__ == '__main__':
    sys.exit(main())
