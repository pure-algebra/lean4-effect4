#!/usr/bin/env python3
"""Run the production OCaml decoder on immutable pre-change vectors in a temp dir.

This is a finite decoder/JSON/byte observation, not structural proof or host
execution. Typing deltas are reported separately and require an exact policy
file when present. The original baseline and generated library are read-only.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent / 'lib'))
import compatibility as c


def run(out, ocamlc, admission_policy):
    sources = ['eff_types.ml', 'eff_frame.ml', 'eff_wire.ml', 'eff_json_text.ml',
               'eff_json.ml', 'eff_native.ml', 'eff_typing.ml']
    original = c.ROOT / 'Test/fixtures/baseline/66ee4657'
    hashes = {p.name: c.digest(p.read_bytes()) for p in original.iterdir() if p.is_file()}
    entries = []
    for line in (original / 'golden-digests.sha256').read_text().splitlines():
        sha, path = line.split(maxsplit=1)
        if path.endswith(('.bin', '.hex')):
            data = c.git_bytes(c.ROOT, c.BASE, 'ocaml/' + path)
            if c.digest(data) != sha:
                raise ValueError('historical input differs from retained digest: ' + path)
            entries.append((path, data, sha))
    if len(entries) != 50:
        raise ValueError(f'historical byte inventory changed: {len(entries)} expected 50')
    with tempfile.TemporaryDirectory(prefix='effect4-compatibility-history-') as tmp:
        work = Path(tmp)
        source_hashes = {}
        for name in sources:
            data = (c.ROOT / 'ocaml/eff' / name).read_bytes()
            (work / name).write_bytes(data)
            source_hashes['ocaml/eff/' + name] = c.digest(data)
        observer = c.ROOT / 'tools/Compatibility/Decode.ml'
        shutil.copyfile(observer, work / 'Decode.ml')
        source_hashes['tools/Compatibility/Decode.ml'] = c.digest(observer.read_bytes())
        command = [str(ocamlc), '-o', 'decode', *sources, 'Decode.ml']
        built = subprocess.run(command, cwd=work, capture_output=True, text=True)
        if built.returncode:
            raise ValueError('OCaml observer build failed:\n' + built.stdout + built.stderr)
        expectations, inputs = {}, []
        for i, (path, data, sha) in enumerate(entries):
            file = work / f'{i:02d}-{Path(path).name}.bin'
            raw = bytes.fromhex(data.decode().strip()) if path.endswith('.hex') else data
            file.write_bytes(raw)
            inputs.append(file)
            expected = {'path': path, 'sha256': sha}
            if path.endswith('.bin'):
                expected['program'] = c.git_bytes(c.ROOT, c.BASE, 'ocaml/' + path[:-4] + '.json').decode().strip()
                expected['type'] = c.git_bytes(c.ROOT, c.BASE, 'ocaml/' + path[:-4] + '.ty').decode().strip()
            expectations[file.name] = expected
        # A payload independently assembled from the documented old constructor/frame
        # ordinals: Eff.fail (Term.lit (Lit.bool true)). Decoder permission remains
        # separate from a policy that later refuses Boolean typed failures.
        frame = lambda tag, payload: bytes([tag]) + len(payload).to_bytes(8, 'big') + payload
        nat = lambda n: frame(2, bytes([n]) if n else b'')
        ctor = lambda i, args: frame(10, nat(i) + args)
        boolean_error = ctor(1, ctor(1, ctor(2, frame(1, b'\x01'))))
        control = work / 'boolean-error.bin'; control.write_bytes(boolean_error)
        inputs.append(control)
        result = subprocess.run([str(work / 'decode'), *map(str, inputs)], cwd=work, capture_output=True, text=True)
        if result.returncode:
            raise ValueError('decoder observer failed: ' + result.stderr)
        rows = [json.loads(line) for line in result.stdout.splitlines()]
        if len(rows) != len(inputs) or {r['file'] for r in rows} != {p.name for p in inputs}:
            raise ValueError('decoder observer did not return the exact requested inventory')
        errors, before, after = [], {}, {}
        for row in rows:
            if not row.get('decoded') or not row.get('reencoded') or not row.get('trailing_refused'):
                errors.append(row['file'] + ': decoding, byte roundtrip or exactness control failed')
            expected = expectations.get(row['file'])
            if expected and 'program' in expected:
                if row.get('program') != expected['program']:
                    errors.append(expected['path'] + ': decoded old value differs')
                before[expected['path']] = expected['type']
                after[expected['path']] = row.get('type')
        type_report = c.policy_delta(before, after, admission_policy, 'admission')
        report = {
            'revision': c.BASE,
            'source_sha256': source_hashes,
            'ocaml_version': subprocess.check_output([str(ocamlc), '-version'], text=True).strip(),
            'compiler_argv': [str(ocamlc), '-o', '<temporary>/decode', *sources, 'Decode.ml'],
            'structural_wire': {'status': 'not_run', 'reason': 'run reflected-shape comparison separately'},
            'decoding': {'status': 'fail' if errors else 'pass', 'old_vectors': len(entries),
                         'old_value_comparisons': len(before), 'errors': errors,
                         'judgment': 'current OCaml decoder on retained bytes; exact re-encoding and 42 old JSON values'},
            'admission': {**type_report, 'oracle': 'current OCaml checker on 42 retained programs',
                          'judgment': 'fresh print_type results compared with retained type outputs and exact delta policy'},
            'execution_permission': {'status': 'not_run', 'reason': 'no runtime invoked'},
            'boolean_error_control': next(row for row in rows if row['file'] == control.name),
            'rows': rows,
        }
    if hashes != {p.name: c.digest(p.read_bytes()) for p in original.iterdir() if p.is_file()}:
        raise ValueError('original baseline changed during historical check')
    if out:
        if out.resolve().is_relative_to(original.parent.resolve()):
            raise ValueError('history report cannot write baseline fixtures')
        out.write_text(c.canonical(report))
    print(c.canonical({key: value for key, value in report.items() if key != 'rows'}), end='')
    return int(bool(errors) or type_report['status'] != 'pass')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ocamlc', type=Path, default=Path(shutil.which('ocamlc') or str(Path.home() / '.opam/effect4/bin/ocamlc')))
    parser.add_argument('--out', type=Path)
    parser.add_argument('--admission-policy', type=Path)
    args = parser.parse_args()
    try:
        policy = json.loads(args.admission_policy.read_text()) if args.admission_policy else {}
        sys.exit(run(args.out, args.ocamlc, policy))
    except (ValueError, OSError, KeyError, subprocess.CalledProcessError) as error:
        print('FAIL historical compatibility: ' + str(error), file=sys.stderr)
        sys.exit(1)
