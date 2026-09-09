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
    for name in ['tools', 'scripts', 'docs', 'Test']:
        (root/name).symlink_to(original_root/name, target_is_directory=True)
    for name in ['lean-toolchain', 'lakefile.toml']:
        shutil.copyfile(original_root/name, root/name)
    traces = root/'.lake/build/lib/lean'
    traces.mkdir(parents=True)
    for source in (original_root/'.lake/build/lib/lean').rglob('*.trace'):
        target = traces/source.relative_to(original_root/'.lake/build/lib/lean')
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    (root/'.lake/packages').symlink_to(original_root/'.lake/packages', target_is_directory=True)
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

    # A transitive trace may still name its old depHash after a source edit.
    # Point one copied trace at identical local source, then change source only.
    import json
    trace = traces/'Effect4/Program/Native.trace'
    trace_data = json.loads(trace.read_text())
    entry = next(e for e in trace_data['inputs'] if e[0].endswith('.lean'))
    imported = root/'native-input.lean'
    imported.write_bytes(Path(entry[0]).read_bytes())
    entry[0] = str(imported)
    trace.write_text(json.dumps(trace_data))
    reset()
    assert gate.observe(rows)[0] == 1
    imported.write_bytes(imported.read_bytes() + b'\n-- unbuilt imported edit\n')
    reset()
    refuses('unbuilt transitive import edit', lambda: gate.observe(rows))
    imported.write_bytes(imported.read_bytes().removesuffix(b'\n-- unbuilt imported edit\n'))
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
# 24 -> 25 on 2026-09-09 with check_generated.py: ts/eff/packages.gen.ts joined the TypeScript
# family (host rows step 5); this battery was not moved with the pin and failed until the
# error-paths map scout noticed.
assert len(gate.drift_files(list(inputs.inventory()))) == 25
print('PASS generated gate reaction battery; temporary fixtures only')
