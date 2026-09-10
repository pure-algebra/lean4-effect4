"""Generated provenance and fresh-byte gates; cache only an accepted policy verdict."""
import argparse
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile
import time

import generated_inputs as inputs
from generated_bytes import STAMP, comparable

ROOT = inputs.ROOT
BASE = '7f8a9fc239822a3028c2f68c2235cb903ee902c2'
LCNF = {'ocaml/gen/api_gen.ml', 'ocaml/gen/fibers_gen.ml',
        'ocaml/gen/machine_gen.ml', 'ocaml/engine/api_engine.ml'}
# The declared reason of the `generated-stale` red entry in Test/fixtures/trust-gate/known-red.txt,
# verbatim; the gate refuses when the two drift apart, so a change there is a change here.
REASON = ("the two flat LCNF outputs `ocaml/gen/fibers_gen.ml` and `machine_gen.ml` were cut before "
          "e2285a9; regenerating them at HEAD builds, but the hand-written `ocaml/gen/gen_check.ml` "
          "still tests the pre-timer machine shape (no Task_wake, no wake_list/clock_step/prepare_answer) "
          "and fails C2. Cleared when gen_check.ml is brought to the timer and external rows (DI-19's Phase 1)")


def mapped_paths():
    """Every path the map names, whatever its last column says. `inventory()` yields only the
    rows a byte gate re-cuts; this is the map's whole index."""
    paths = set()
    for line in (ROOT/'docs/GENERATED.md').read_text().splitlines():
        if line.startswith('| `'):
            paths.add([s.strip() for s in line.strip('|').split('|')][0].strip('`'))
    return paths


def unmapped(tracked=None):
    """DI-44, the tree-to-map walk: a tracked file that carries a `cut-from:` stamp — in its
    own header or in a `.cut-from` sidecar beside it — and has no row in docs/GENERATED.md.
    The map is how every other gate here finds what is generated, so an artefact that stamps
    itself and is missing from the map is invisible to all of them. The stamp must be in the
    first three lines: five tracked files mention the format in their body (the map itself,
    `generated_bytes.py`, `generated_inputs.py`, `GeneratedStamp.lean`, `render-readme.ts`)
    and are producers, not products. Measured 2026-09-09: 310 stamped files and 266 sidecars,
    all mapped."""
    mapped = mapped_paths() | inputs.DEFERRED_ARTIFACTS
    if tracked is None:
        tracked = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
    missing = []
    for name in tracked:
        if not name or name in mapped:
            continue
        base = name[:-len('.cut-from')] if name.endswith('.cut-from') else name
        if base in mapped:
            continue
        if name.endswith('.cut-from'):
            missing.append(name)
            continue
        try:
            head = b'\n'.join((ROOT/name).read_bytes().split(b'\n', 3)[:3])
        except OSError:
            continue
        if STAMP.search(head):
            missing.append(name)
    return sorted(set(missing))


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
        if family.startswith('Derived ') or family in {'Typing specs', 'Eff', 'Eff goldens', 'Engine structure', 'Wire goldens', 'CAS goldens', 'TypeScript'}:
            chosen.append(path)
    if len(chosen) != len(set(chosen)):
        raise ValueError('duplicate fresh-byte inventory path')
    for prefix in ['src/Effect4/', 'ocaml/eff/', 'ocaml/goldens/eff/',
                   'ocaml/engine/cas/goldens/', 'ts/eff/']:
        if not any(path.startswith(prefix) for path in chosen):
            raise ValueError('missing fresh-byte family: ' + prefix)
    return chosen


def compare_fresh(chosen, temporary):
    """Check an inventory bijection before comparing complete non-stamp bytes."""
    temporary = Path(temporary)
    produced = {str(path.relative_to(temporary)) for path in temporary.rglob('*')
                if path.is_file() and not path.name.endswith('.cut-from')}
    if produced != set(chosen):
        raise ValueError('fresh-byte inventory differs: unlisted=' +
                         repr(sorted(produced - set(chosen))) + ', unproduced=' +
                         repr(sorted(set(chosen) - produced)))
    for path in chosen:
        if comparable((temporary/path).read_bytes()) != comparable((ROOT/path).read_bytes()):
            raise ValueError(path + ': is not what Lean emits')


def drift(rows):
    chosen = drift_files(rows)
    with tempfile.TemporaryDirectory(prefix='effect4-generated-check-') as temporary:
        for family in ['derived', 'specs', 'eff', 'wire', 'cas', 'ts']:
            subprocess.run(['bash', 'scripts/generate.sh', '--only', family,
                            '--output-dir', temporary], cwd=ROOT, check=True,
                           stdout=None, stderr=None)
        compare_fresh(chosen, temporary)
    return len(chosen)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stale', action='store_true')
    parser.add_argument('--declared-reason')
    args = parser.parse_args()
    start = time.monotonic()
    # The walk is 0.12 s over 1857 tracked files, so it runs before the stamp shortcut: a
    # stamped artefact added anywhere in the tree must not be able to hide behind a hit.
    orphans = unmapped()
    if orphans:
        raise ValueError('stamped artefacts with no row in docs/GENERATED.md: ' + ', '.join(orphans))
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
        summary = f'PASS generated: {count} files are what Lean emits, including CAS and metadata; LCNF checked by its declared provenance policy'
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
