#!/usr/bin/env python3
"""Exercise provenance failures in temporary fixtures; never edit committed projections."""
from pathlib import Path
import shutil
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent/'lib'))
import check_generated as gate
import generated_inputs as inputs
from generated_bytes import comparable

original_root = gate.ROOT


def reset():
    for fn in [inputs.read, inputs.trace, inputs.digest, inputs.recipe]:
        fn.cache_clear()


def refuses(label, action):
    try:
        action()
    except (ValueError, OSError):
        print('PASS refuses ' + label)
    else:
        raise AssertionError(label + ' was accepted')


with tempfile.TemporaryDirectory(prefix='effect4-stamp-attacks-') as temporary:
    root = Path(temporary)
    for name in ['scripts', 'docs']:
        (root/name).symlink_to(original_root/name, target_is_directory=True)
    # A cloned trace is resolved against this checkout's source tree, never by reading
    # the absolute source path saved in the original checkout.
    for name in ['src', 'tools', 'Test']:
        shutil.copytree(original_root/name, root/name)
    for name in ['lean-toolchain', 'lakefile.toml']:
        shutil.copyfile(original_root/name, root/name)
    traces = root/'.lake/build/lib/lean'
    traces.mkdir(parents=True)
    for source in (original_root/'.lake/build/lib/lean').rglob('*.trace'):
        target = traces/source.relative_to(original_root/'.lake/build/lib/lean')
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    # Dependency packages are also local package roots. Copy their source/config/trace
    # inventory, without expensive native/compiler build products or git histories.
    packages = original_root/'.lake/packages'
    for package in packages.iterdir():
        for source in package.rglob('*'):
            if source.is_file() and (source.suffix in {'.lean', '.trace'} or source.name == 'lakefile.toml'):
                target = root/'.lake/packages'/source.relative_to(packages)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
    source_path = 'src/OCaml5/Tools/EffGen.lean'
    source = root/source_path
    source.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(original_root/source_path, source)
    path = 'ocaml/eff/eff_native.ml'
    output = root/path
    output.parent.mkdir(parents=True)
    data = (original_root/path).read_bytes()
    output.write_bytes(data)
    inputs.ROOT = gate.ROOT = root
    rows = [(path, 'Eff')]
    reset()
    current, stale, fingerprints = gate.observe(rows)
    assert current == 1 and not stale
    baseline_key = gate.key(rows, fingerprints)
    print('PASS current generated fixture')

    for label, corrupted in [
        ('wrong digest', data.replace(b'inputs=', b'inputs=0', 1)),
        ('wrong toolchain', data.replace(b'toolchain=4.33.1', b'toolchain=0')),
        ('missing stamp', b'\n'.join(data.split(b'\n')[1:])),
    ]:
        output.write_bytes(corrupted)
        reset()
        refuses(label, lambda: gate.observe(rows))
    output.write_bytes(data)
    before = source.read_bytes()
    source.write_bytes(before + b'\n-- source changed without a build\n')
    reset()
    refuses('unbuilt producer edit', lambda: gate.observe(rows))
    source.write_bytes(before)

    # A transitive trace may still point at a different checkout. Matching module suffixes
    # resolve to local source; unrelated source names refuse rather than being followed.
    import json
    trace = traces/'Effect4/Program/Native.trace'
    trace_data = json.loads(trace.read_text())
    entry = next(e for e in trace_data['inputs'] if e[0].endswith('.lean'))
    imported = root/'src/Effect4/Program/Native.lean'
    entry[0] = '/unavailable/old-checkout/src/Effect4/Program/Native.lean'
    trace.write_text(json.dumps(trace_data))
    reset()
    assert gate.observe(rows)[0] == 1
    print('PASS cloned absolute trace resolves to current module source')
    imported.write_bytes(imported.read_bytes() + b'\n-- unbuilt imported edit\n')
    reset()
    refuses('unbuilt transitive import edit', lambda: gate.observe(rows))
    imported.write_bytes(imported.read_bytes().removesuffix(b'\n-- unbuilt imported edit\n'))
    entry[0] = '/unavailable/native-input.lean'
    trace.write_text(json.dumps(trace_data))
    reset()
    refuses('trace source names a different module', lambda: gate.observe(rows))
    entry[0] = '/unavailable/old-checkout/src/Effect4/Program/Native.lean'
    trace.write_text(json.dumps(trace_data))
    reset()
    output.write_bytes(data + b'\n(* changed body *)\n')
    current, stale, fingerprints = gate.observe(rows)
    assert current == 1  # stamp-only evidence does not claim body equality
    assert comparable(output.read_bytes()) != comparable(data)
    assert gate.key(rows, fingerprints) != baseline_key
    print('PASS body edit changes cache key and fails full-byte comparison')
    output.write_bytes(data.replace(b'rev=', b'rev=another-', 1))
    assert comparable(output.read_bytes()) == comparable(data)
    print('PASS informational revision alone compares equal')

inputs.ROOT = gate.ROOT = original_root
reset()
refuses('undeclared LCNF stale state', lambda: gate.policy(['ocaml/gen/api_gen.ml'], None))
refuses('unexpected LCNF pass', lambda: gate.policy([], gate.REASON))
refuses('different declared reason', lambda: gate.policy(['ocaml/gen/api_gen.ml'], 'ignore errors'))
assert gate.policy(['ocaml/gen/api_gen.ml'], gate.REASON).startswith('red as declared:')
chosen = gate.drift_files(list(inputs.inventory()))
assert any(path.startswith('ocaml/engine/cas/goldens/') for path in chosen)
assert 'ocaml/eff/goldens/metadata.tsv' in chosen
# Exercise the same full-byte and inventory comparison used after fresh production.
# Preserve the CAS stamp: stamp-only checking deliberately cannot see this corruption.
with tempfile.TemporaryDirectory(prefix='effect4-cas-byte-attack-') as temporary:
    temp = Path(temporary)
    fixture = next(path for path in chosen if path.startswith('ocaml/engine/cas/goldens/'))
    fresh = temp/fixture
    fresh.parent.mkdir(parents=True)
    data = (original_root/fixture).read_bytes()
    fresh.write_bytes(data)
    gate.compare_fresh([fixture], temp)
    fresh.write_bytes(data + b'\x00')
    refuses('CAS body corruption with retained stamp', lambda: gate.compare_fresh([fixture], temp))
    fresh.write_bytes(data)
    refuses('unlisted fresh output', lambda: gate.compare_fresh([], temp))
    refuses('missing fresh output', lambda: gate.compare_fresh([fixture, 'missing'], temp))
print('PASS generated gate reaction battery; temporary fixtures only')
