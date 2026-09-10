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
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(root / 'scripts/lib'))
from generated_bytes import comparable

truth = root / 'harness/truth'
PINNED = '4.0.0-rc.112'
# The host packages the harness can import: `effect` and the `@effect/*` drivers. Not the whole
# tree: `oxc-parser`'s platform-specific bindings differ per machine and would make the stamp
# machine-dependent (the standing rule against non-incremental gates).
HOST_PACKAGES = ('effect', '@effect')


def inputs_of(root, truth, modules, manifest_files):
    """Everything the differential reads, in a fixed order: the harness, the Lean sources, the
    committed artefacts and tapes, the host packages, and the manifest that pins them."""
    inputs = list(truth.glob('*.ts')) + list(truth.glob('*.lean')) + sorted((truth/'session').glob('*.ts')) + [Path(__file__),
              root/'lean-toolchain', root/'lake-manifest.json']
    inputs += list(manifest_files)
    inputs += sorted((root/'src/Effect4').rglob('*.lean'))
    inputs += [truth/'corpus.json', truth/'result.json', truth/'result.md', truth/'tsconfig.json']
    inputs += sorted((truth/'generated').glob('*.ts'))
    inputs += sorted(truth.glob('*.cut-from'))
    inputs += sorted((truth/'tapes').glob('*')) if (truth/'tapes').is_dir() else []
    inputs += [root/'scripts/lib/generated_bytes.py', root/'tools/Tools/GeneratedStamp.lean']
    # `run-truth.ts`'s self-test reads the atom set out of the TypeScript estate's profile
    # (DI-40), so the profile and the schema module it decodes through are inputs here too.
    inputs += [root/'ts/eff/profile.gen.ts', root/'ts/eff/eff.gen.ts']
    # The package versions alone cannot detect locally changed host implementations.
    for name in HOST_PACKAGES:
        base = modules / name
        if base.is_dir():
            inputs += sorted(path for path in base.rglob('*') if path.is_file())
    return inputs


def truth_digest(root, truth, modules, manifest_files, bun_version):
    digest = hashlib.sha256()
    for path in inputs_of(root, truth, modules, manifest_files):
        digest.update(str(path).encode() + b'\0' + path.read_bytes())
    digest.update(bun_version)
    return digest.hexdigest()


def main():
    modules = Path(os.environ.get('EFFECT4_EFFECT_NODE_MODULES', root / 'ts/eff/node_modules')).resolve()
    package = modules / 'effect/package.json'
    if not package.is_file() or json.loads(package.read_text())['version'] != PINNED:
        sys.exit(f'FAIL truth: EFFECT4_EFFECT_NODE_MODULES must contain effect@{PINNED}')
    driver = modules / '@effect/sql-sqlite-bun/package.json'
    if not driver.is_file() or json.loads(driver.read_text())['version'] != PINNED:
        sys.exit(f'FAIL truth: EFFECT4_EFFECT_NODE_MODULES must contain @effect/sql-sqlite-bun@{PINNED} (bun install in ts/eff)')
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

    manifest_files = [root/'ts/eff/package.json', root/'ts/eff/bun.lock']
    digest = truth_digest(root, truth, modules, manifest_files, subprocess.check_output([bun, '--version']))
    stamp_dir = root/'.lake/stamps/truth'
    stamp = stamp_dir/digest
    if stamp.exists() and os.environ.get('EFFECT4_FORCE') != '1':
        print('PASS truth: unchanged; skipped (EFFECT4_FORCE=1 re-runs)')
        return 0
    tapes = truth / 'tapes'
    tapes.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='truth-check-', dir=truth) as work:
        # Generated modules import ../prelude.ts and resolve Effect from their parent tree.
        # Keep the temporary run beneath the selected installation link, as the real run is.
        shutil.copyfile(truth/'prelude.ts', Path(work)/'prelude.ts')
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
        for name in ['corpus.json', 'result.json', 'result.md', 'corpus.json.cut-from', 'result.json.cut-from']:
            if comparable((Path(work)/name).read_bytes()) != comparable((truth/name).read_bytes()):
                sys.exit(f'FAIL truth: harness/truth/{name} drifted; inspect the regenerated differential before refreshing')
        generated = Path(work)/'generated'
        expected = truth/'generated'
        if sorted(p.name for p in generated.glob('*.ts')) != sorted(p.name for p in expected.glob('*.ts')):
            sys.exit('FAIL truth: generated module inventory drifted')
        for file in generated.glob('*.ts'):
            if comparable(file.read_bytes()) != comparable((expected/file.name).read_bytes()):
                sys.exit(f'FAIL truth: generated module {file.name} drifted')
        fresh = Path(work)/'tapes'
        fresh_names = sorted(p.name for p in fresh.glob('*')) if fresh.is_dir() else []
        if fresh_names != sorted(p.name for p in tapes.glob('*')):
            sys.exit(f'FAIL truth: tape inventory drifted: rc.112 recorded {fresh_names}, committed {sorted(p.name for p in tapes.glob("*"))}; install the fresh tapes deliberately')
        for file in fresh.glob('*') if fresh.is_dir() else []:
            if comparable(file.read_bytes()) != comparable((tapes/file.name).read_bytes()):
                sys.exit(f'FAIL truth: tape {file.name} drifted; rc.112 answered differently from the committed tape')
    stamp_dir.mkdir(parents=True, exist_ok=True)
    for old in stamp_dir.iterdir():
        if old.is_file(): old.unlink()
    stamp.write_text('bounded corpus differential agrees with rc.112; modules type-check\n')
    print('PASS truth: pinned corpus and bounded exit/schedule differential agree; '
          'the regenerated modules type-check')
    return 0


if __name__ == '__main__':
    sys.exit(main())
