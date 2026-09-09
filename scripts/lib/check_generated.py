"""Generated provenance and fresh-byte gates; cache only an accepted policy verdict."""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import time

import generated_inputs as inputs
from generated_bytes import comparable

ROOT = inputs.ROOT
BASE = '7f8a9fc239822a3028c2f68c2235cb903ee902c2'
LCNF = {'ocaml/gen/api_gen.ml', 'ocaml/gen/fibers_gen.ml',
        'ocaml/gen/machine_gen.ml', 'ocaml/engine/api_engine.ml'}
REASON = 'engines cut before e2285a9; cleared by plan v2 Phase 1'


def observe(rows):
    current, stale, fingerprints = 0, [], {}
    toolchain = (ROOT/'lean-toolchain').read_text().strip().split(':v')[-1]
    for path, family in rows:
        if path in inputs.DEFERRED_ARTIFACTS:
            continue
        expected = inputs.expected(path, family)
        fingerprints[path] = expected
        if path in LCNF and b'cut-from:' not in (ROOT/path).read_bytes():
            # The declaration covers only these original frozen bytes. It cannot
            # accept a corrupted engine or another artifact's stamp failure.
            original = subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=ROOT)
            if (ROOT/path).read_bytes() != original:
                raise ValueError(path + ': unstamped LCNF bytes changed outside Phase 1')
            stale.append(path)
            continue
        version, stamp = inputs.recorded(path)
        if version != toolchain or stamp != expected:
            raise ValueError(path + ': stale provenance; regenerate its owning family')
        current += 1
    return current, stale, fingerprints


def policy(stale, declared):
    if declared is not None and declared != REASON:
        raise ValueError('generated-stale declaration has an unexpected reason')
    if stale and declared is None:
        raise ValueError('UNDECLARED FAILURE: LCNF outputs need Phase 1 regeneration')
    if not stale and declared is not None:
        raise ValueError('UNEXPECTED PASS: remove generated-stale deliberately after Phase 1')
    return 'red as declared: ' + declared if stale else 'all provenance current'


def key(rows, fingerprints):
    paths = {'scripts/check-generated.sh', 'scripts/generate.sh', 'scripts/generate-ts-eff.sh',
             'scripts/lib/known-red.sh', 'lean-toolchain', 'lakefile.toml',
             'tools/Effect4Gen/manifest.json', 'docs/GENERATED.md',
             'Test/fixtures/trust-gate/known-red.txt'}
    paths.update(path for path, _ in rows)
    for folder in ['scripts/lib', 'tools', 'src']:
        paths.update(str(p.relative_to(ROOT)) for p in (ROOT/folder).rglob('*')
                     if p.is_file() and p.suffix in {'.py', '.lean'})
    for folder in ['Effect4', 'OCaml5', 'Tools', 'Effect4Gen']:
        paths.update(str(p.relative_to(ROOT)) for p in
                     (ROOT/'.lake/build/lib/lean'/folder).rglob('*.trace'))
    digest = hashlib.sha256()
    for path in sorted(paths):
        digest.update(path.encode() + b'\0')
        digest.update(hashlib.sha256((ROOT/path).read_bytes()).digest())
    for path, value in sorted(fingerprints.items()):
        digest.update(path.encode() + b'\0' + value.encode())
    return digest.hexdigest()


def drift_files(rows):
    chosen = []
    for path, family in rows:
        if path.endswith('.cut-from'):
            continue
        if family.startswith('Derived ') or family in {'Eff', 'Wire goldens', 'TypeScript'}:
            chosen.append(path)
    if len(chosen) != 24:
        raise ValueError(f'expected 24 cheap drift files, map names {len(chosen)}')
    return chosen


def drift(rows):
    chosen = drift_files(rows)
    with tempfile.TemporaryDirectory(prefix='effect4-generated-check-') as temporary:
        for family in ['derived', 'eff', 'wire', 'ts']:
            subprocess.run(['bash', 'scripts/generate.sh', '--only', family,
                            '--output-dir', temporary], cwd=ROOT, check=True,
                           stdout=None, stderr=None)
        for path in chosen:
            if comparable((Path(temporary)/path).read_bytes()) != comparable((ROOT/path).read_bytes()):
                raise ValueError(path + ': is not what Lean emits')
    return len(chosen)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stale', action='store_true')
    parser.add_argument('--declared-reason')
    args = parser.parse_args()
    start = time.monotonic()
    rows = [(path, family) for path, family in inputs.inventory()
            if path not in inputs.DEFERRED_ARTIFACTS]
    current, stale, fingerprints = observe(rows)
    verdict = policy(stale, args.declared_reason)
    gate = 'generated-stale' if args.stale else 'generated'
    stamp = ROOT/'.lake/stamps'/gate/key(rows, fingerprints)
    if os.environ.get('EFFECT4_FORCE') != '1' and stamp.is_file():
        print(stamp.read_text().strip())
        print(f'PASS {gate}: skipped (EFFECT4_FORCE=1 re-runs)')
        return
    if not args.stale:
        count = drift(rows)
        # Building imports can change trace bytes; stamp the final observed inputs.
        for fn in [inputs.read, inputs.trace, inputs.digest, inputs.recipe]:
            fn.cache_clear()
        current, stale, fingerprints = observe(rows)
        verdict = policy(stale, args.declared_reason)
        stamp = ROOT/'.lake/stamps'/gate/key(rows, fingerprints)
        summary = f'PASS generated: {count} files are what Lean emits; LCNF and 119 CAS goldens checked by stamp'
    else:
        summary = f'PASS generated-stale: {current} stamps checked in {time.monotonic()-start:.3f}s; {verdict}'
    if stale:
        summary += '\nLCNF: ' + ', '.join(stale) + '\n' + REASON
    summary += '\nDeferred by owner: ' + ', '.join(sorted(inputs.DEFERRED_ARTIFACTS))
    # Cache an accepted policy verdict, including exactly the declared frozen
    # LCNF state. Any other failure exits before this write.
    stamp.parent.mkdir(parents=True, exist_ok=True)
    stamp.write_text(summary + '\n')
    print(summary)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        raise SystemExit('FAIL generated: ' + str(error))
