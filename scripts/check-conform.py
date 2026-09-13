#!/usr/bin/env python3
"""Build once, run fresh Conform profiles, validate every result, retain exact run receipts.

    python3 scripts/check-conform.py [PROFILE ...]      default: models native types

`make check-cases` and `make check-native` run the `cases` and `native` profiles; the rest
are run by name. Each profile is a producer that gets an empty directory and must write
exactly its named files; `conform_report.fresh_run` validates the reports, refuses an
input that changed during the run, and keeps the receipt under `.lake/conform/`. Two
profiles are Python steps of this file (`--step`): `target` (the current Lean fixtures
through the pinned TypeScript oracle) and `compiler` (one production compiler checkpoint:
Lean-emitted OCaml for normalization, compiled and run against Lean's fixture list, plus
one emitted-code mutation that must fail). The report refusal controls are
`scripts/test-conform-report.py`, in `make check-tools`.
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
                 ["normalization.json", "validity.json", "closure.json", "normalization.ml", "expected.txt", "actual.txt", "mutated.ml", "ocaml.json", "mutation.txt"]),
    "target": ([sys.executable, SELF, "--step", "target", "{out}"],
               ["target-fixtures.json", "target-oracle.json", "typing-target.json"]),
    "types": (["lake", "env", "lean", "-M4096", "--run", "tools/Conform/Effect4/InspectTypes.lean", "{out}"],
              ["types.json", "type-descriptions.json"]),
    "models": (["lake", "env", "lean", "-M4096", "--run", "tools/Conform/Effect4/ModelsMain.lean", "{out}"],
               ["models.json"]),
    "native": (["lake", "env", "lean", "-M4096", "--run", "tools/Conform/Effect4/NativeMain.lean", "{out}"],
               ["layout-lean-native.json", "native-layout.json"]),
    "layouts": (["lake", "env", "lean", "-M4096", "--run", "tools/Conform/Effect4/LayoutMain.lean", "{out}"],
                ["layout-x2-typescript.json", "layout-x2-typescript-corrected.json", "layout-canonical-wire.json", "layout-ocaml-eff.json"]),
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


def step_target(out):
    """Fresh current-Lean fixture map followed by the pinned TypeScript oracle."""
    out.mkdir(parents=True, exist_ok=True)
    fixture = out / 'target-fixtures.json'
    first = subprocess.run(['lake', 'env', 'lean', '-M4096', '--run',
                            'tools/Conform/Effect4/TargetFixtures.lean', str(fixture)], cwd=ROOT)
    if first.returncode:
        return first.returncode
    return subprocess.run(['bun', 'tools/target/conform.ts', str(fixture), str(out)], cwd=ROOT).returncode


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
    # Mutate the actual emitted UTF-8 helper. Compiling must still succeed and the selected
    # program must report failure; a compiler failure is not a detected semantic mutation.
    text = (out / 'normalization.ml').read_text()
    original = 'Char.code (String.get s i)'
    if text.count(original) != 1:
        raise RuntimeError('UTF-8 mutation anchor missing or ambiguous')
    (out / 'mutated.ml').write_text(text.replace(original, '0'))
    run([compiler, '-w', '-a', str(out / 'mutated.ml'), '-o', str(out / 'mutated')])
    mutation = subprocess.run([str(out / 'mutated')], capture_output=True, text=True)
    if mutation.returncode != 1 or '\tFAIL' not in mutation.stderr:
        raise RuntimeError('UTF-8 mutation did not fail the selected observation')
    ids = [line.split('\t')[0] for line in expected.splitlines()] + ['utf8-mutation']
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
    (out / 'mutation.txt').write_text(mutation.stderr)
    for name in ['normalization', 'mutated']:
        for suffix in ['', '.cmi', '.cmx', '.o']:
            (out / (name + suffix)).unlink(missing_ok=True)
    print(f'compiler checkpoint: {len(ids)-1} actual OCaml checks and one emitted-code mutation passed')
    return 0


STEPS = {"target": step_target, "compiler": step_compiler}


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
    args.profiles = args.profiles or ["models", "native", "types"]
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
