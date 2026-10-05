#!/usr/bin/env python3
"""Build once, run fresh Conform profiles, validate every result, retain exact run receipts.

    python3 scripts/check-conform.py [PROFILE ...]      default: native

`make check-cases` and `make check-native` run the `cases` and `native` profiles; `compiler`
runs by name (CI's OCaml job). Each profile is a producer that gets an empty directory and
must write exactly its named files; `conform_report.fresh_run` validates the reports,
refuses an input that changed during the run, and keeps the receipt under `.lake/conform/`.
`compiler` is a Python step of this file (`--step`): one production compiler checkpoint,
Lean-emitted OCaml for normalization, compiled and run against Lean's fixture list, plus
two emitted-code mutations, each of which must fail the observation that reads it. The report refusal controls (`test-conform-report.py`) were
retired on 2026-09-19 with the other tests of scripts. The `models`, `types`, `layouts`
and `target` profiles were retired on 2026-09-13: receipts of theorems the build already
checks, a layout enumeration the wire theorems and the OCaml lane cover, and a subset of
`make check-target`.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/lib"))
from conform_report import InvalidReport, fresh_run, manifest, validate

SELF = "scripts/check-conform.py"

PROFILES = {
    "compiler": ([sys.executable, SELF, "--step", "compiler", "{out}"],
                 ["normalization.json", "validity.json", "closure.json", "normalization.ml", "expected.txt", "actual.txt", "mutated.ml", "mutated-support.ml", "ocaml.json", "mutation.txt"]),
    "native": (["lake", "env", "lean", "-M4096", "--run", "tools/Conform/Effect4/NativeMain.lean", "{out}"],
               ["layout-lean-native.json", "native-layout.json"]),
    "cases": (["lake", "env", "lean", "-M4096", "--run", "tools/Conform/Cli/Audit.lean",
               "--config", "tools/Conform/Effect4/cases.json", "--out", "{out}/cases.json"],
              ["cases.json"]),
}


# ---------------------------------------------------------------- the two Python steps

def run(command):
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(f'{command[0]} exited {result.returncode}\n{result.stdout[-4000:]}\n{result.stderr[-4000:]}')
    return result


def mutation(out, compiler, text, name, original, replacement, intended, expected):
    """Compile an altered copy of the emitted module and run it.

    The alteration must compile. The run must stop with exit 1 at one observation, that
    observation must be one of `intended`, and the output before it must be the expected
    prefix. A compiler failure, or a failure of an unrelated observation, is not the evidence
    this control asks for.
    """
    if text.count(original) != 1:
        raise RuntimeError(f'{name}: mutation anchor missing or ambiguous')
    (out / f'{name}.ml').write_text(text.replace(original, replacement))
    run([compiler, '-w', '-a', str(out / f'{name}.ml'), '-o', str(out / name)])
    result = subprocess.run([str(out / name)], capture_output=True, text=True)
    failed = [line.split('\t')[0] for line in result.stderr.splitlines() if line.endswith('\tFAIL')]
    if result.returncode != 1 or len(failed) != 1:
        raise RuntimeError(f'{name}: the mutation did not fail exactly one selected observation')
    if failed[0] not in intended:
        raise RuntimeError(f'{name}: the mutation failed {failed[0]}, not one of {sorted(intended)}')
    lines = expected.splitlines()
    before = lines[:lines.index(f'{failed[0]}\tPASS')]
    if result.stdout != ''.join(line + '\n' for line in before):
        raise RuntimeError(f'{name}: the observations before {failed[0]} differ from the expected prefix')
    return result.stderr


def step_compiler(out):
    """One production compiler checkpoint."""
    run(['lake', 'env', 'lean', '-M4096', '--run', 'tools/Conform/Effect4/Normalization.lean', str(out)])
    for file in ['normalization.json', 'validity.json']:
        if validate(json.loads((out / file).read_text())):
            raise RuntimeError(f'{file}: checkpoint has unresolved or failed rows')
    compiler = os.environ.get('OCAMLOPT') or shutil.which('ocamlopt')
    if shutil.which('opam') and not os.environ.get('OCAMLOPT'):
        compiler = str(Path(run(['opam', 'var', 'bin', '--switch=effect4']).stdout.strip()) / 'ocamlopt')
    if not compiler:
        raise RuntimeError('ocamlopt is required for the compiler profile')
    run([compiler, '-w', '-a', str(out / 'normalization.ml'), '-o', str(out / 'normalization')])
    actual = run([str(out / 'normalization')]).stdout
    expected = (out / 'expected.txt').read_text()
    if actual != expected:
        raise RuntimeError('compiled OCaml observations differ from the Lean fixture list')
    (out / 'actual.txt').write_text(actual)
    text = (out / 'normalization.ml').read_text()
    # Two alterations of the emitted prelude. Each must compile, and each must fail the first
    # observation that reads the altered definition: fixture 12, the key of the handle type
    # whose name is not ASCII, and the product of the first name fixture.
    utf8 = mutation(out, compiler, text, 'mutated', 'Char.code (String.get s i)', '0',
                    {'12'}, expected)
    support = mutation(out, compiler, text, 'mutated-support', 'max_int else a * b',
                       'max_int else a * a', {'names/mulCap'}, expected)
    ids = [line.split('\t')[0] for line in expected.splitlines()] + ['utf8-mutation', 'support-mutation']
    if len(ids) != len(set(ids)):
        raise RuntimeError('duplicate host observation ID')
    required = [{'check': 'normalization.ocaml', 'subject': {'kind': 'fixture', 'path': [id]}} for id in ids]
    rows = [{**item, 'outcome': 'pass', 'evidence': 'tested', 'message': 'actual emitted OCaml observation matched', 'detail': None} for item in required]
    report = {'format': 'conform-report-v2', 'tool': 'conform.normalization.ocaml',
              'pins': [{'name': 'ocaml', 'value': run([compiler, '-version']).stdout.strip()}], 'inputs': [],
              'expected': len(ids), 'required': required, 'rows': rows,
              'summary': {'rows': len(ids), 'pass': len(ids), 'refused': 0, 'counterexample': 0, 'unresolved': 0, 'complete': True, 'exit': 0}}
    validate(report, 0)
    (out / 'ocaml.json').write_text(json.dumps(report, indent=2) + '\n')
    (out / 'mutation.txt').write_text(utf8 + support)
    for name in ['normalization', 'mutated', 'mutated-support']:
        for suffix in ['', '.cmi', '.cmx', '.o']:
            (out / (name + suffix)).unlink(missing_ok=True)
    print(f'compiler checkpoint: {len(ids)-2} actual OCaml checks and two emitted-code mutations passed')
    return 0


STEPS = {"compiler": step_compiler}


# ---------------------------------------------------------------- the runner

def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("profiles", nargs="*", metavar="PROFILE")
    parser.add_argument("--step", choices=sorted(STEPS), help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.step:
        (out,) = args.profiles
        try:
            return STEPS[args.step](Path(out).resolve())
        except (RuntimeError, OSError, ValueError) as error:
            print(error, file=sys.stderr)
            return 2
    args.profiles = args.profiles or ["native"]
    unknown = set(args.profiles) - PROFILES.keys()
    if unknown:
        parser.error(f"unknown profiles: {sorted(unknown)}; choose from {list(PROFILES)}")
    if len(args.profiles) != len(set(args.profiles)):
        parser.error("each profile may be requested only once")
    build = subprocess.run(["lake", "build", "Conform", "Effect4.Laws.Program.Typing.Check"], cwd=ROOT)
    if build.returncode:
        return build.returncode
    worst = 0
    for profile in args.profiles:
        command, files = PROFILES[profile]
        code = fresh_run(command, ROOT / f".lake/conform/{profile}.json", files, cwd=ROOT,
                         input_snapshot=lambda: manifest(ROOT))
        label = {0: "PASS", 1: "REFUSED", 2: "UNRESOLVED"}[code]
        print(f"conform {profile}: {label}, exit {code}; .lake/conform/{profile}.json")
        worst = max(worst, code)
    return worst


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (InvalidReport, ValueError, OSError) as error:
        print(f"conform: INVALID: {error}", file=sys.stderr)
        sys.exit(2)
