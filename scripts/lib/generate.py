"""Dependency ordering and temporary output installation for scripts/generate.sh."""
import argparse
from pathlib import Path
import json
import os
import shlex
import subprocess
import tempfile

import shutil
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import generated_inputs as inputs
from generated_bytes import comparable

ROOT = Path(__file__).resolve().parents[2]

FAMILY_MAP = {
    'derived': ['Derived Json', 'Derived Schema', 'Derived Program', 'Derived Pin'],
    'specs': ['Typing specs'],
    'eff': ['Eff', 'Eff goldens', 'Engine structure'],
    'wire': ['Wire goldens'],
    'cas': ['CAS goldens'],
    'ts': ['TypeScript'],
    'readme': ['Ingest tables'],
    'lcnf': ['LCNF'],
}


def family_artifacts(family):
    mapped = FAMILY_MAP.get(family, [])
    return [(p, f) for p, f in inputs.inventory()
            if f in mapped and p not in inputs.DEFERRED_ARTIFACTS]


def is_family_clean(family):
    arts = family_artifacts(family)
    if not arts:
        return False
    toolchain = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
    for path, f in arts:
        p = ROOT / path
        if not p.is_file():
            return False
        if path in {'ocaml/gen/fibers_gen.ml', 'ocaml/gen/machine_gen.ml'}:
            continue
        try:
            ver, rec = inputs.recorded(path)
            exp = inputs.expected(path, f)
            if ver != toolchain or rec != exp:
                return False
        except Exception:
            return False
    return True


def populate_clean_family(family, out):
    for path, _ in family_artifacts(family):
        src = ROOT / path
        dst = out / path
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
        sidecar = Path(str(src) + '.cut-from')
        if sidecar.is_file():
            shutil.copy2(sidecar, out / (path + '.cut-from'))


def run(args, capture=False):
    print('+ ' + shlex.join(args), flush=True)
    return subprocess.run(['timeout', '600', *args], check=True,
                          stdout=subprocess.PIPE if capture else None, text=True).stdout


def install(source, destination, checking):
    data = source.read_bytes()
    if checking:
        if not destination.is_file() or comparable(data) != comparable(destination.read_bytes()):
            raise ValueError(f'{destination.relative_to(ROOT)} is not what Lean emits')
        return
    destination.parent.mkdir(parents=True, exist_ok=True)
    # Run the producer every time, retaining informational revision when all
    # meaningful bytes agree. No generated text is rewritten by this installer.
    if not destination.is_file() or comparable(data) != comparable(destination.read_bytes()):
        destination.write_bytes(data)


# The one named order (DI-33). Each producer's inputs are earlier families' outputs:
# `derived` writes the Lean projections the rest import; `eff`, `wire` and `cas` cut the OCaml
# estate from them; `ts` cuts the TypeScript estate; `readme` renders the ingest tables out of
# three files `ts` just wrote, so it is last and it is not a Lean producer at all. `lcnf` is
# not in the order: it is the explicit Phase 1 route and is requested by name.
ALL = ['derived', 'specs', 'eff', 'wire', 'cas', 'ts', 'readme']


def generate(families, output, force=False):
    checking = output is not None
    force = force or os.environ.get('EFFECT4_FORCE') == '1'
    with tempfile.TemporaryDirectory(prefix='effect4-generate-') as scratch:
        out = Path(output).resolve() if checking else Path(scratch)
        out.mkdir(parents=True, exist_ok=True)
        if 'derived' in families:
            if not force and is_family_clean('derived'):
                if checking:
                    populate_clean_family('derived', out)
                    print(f'cached derived: all {len(family_artifacts("derived"))} artifacts current', flush=True)
                else:
                    print(f'skip derived: all {len(family_artifacts("derived"))} artifacts current', flush=True)
            else:
                rows = json.loads(run(['lake', 'env', 'lean', '-M4096', '--run',
                                       'tools/Effect4Gen/Driver.lean', '--commands'], True))
                for row in rows:
                    args = row['args']
                    imports = args[args.index('--imports') + 1].split(',')
                    run(['lake', 'build', 'Tools.GeneratedStamp', *imports])
                    canonical = row['out'].replace('\\', '/')
                    temp = out / canonical
                    temp.parent.mkdir(parents=True, exist_ok=True)
                    args[args.index('--out') + 1] = str(temp)
                    if '--append' in args:
                        i = args.index('--append') + 1
                        args[i] = args[i].replace('\\', '/')
                    args += ['--header-out', canonical]
                    run(['lake', *args])
                    install(temp, ROOT / canonical, checking)
                    # Schema depends on the Json projection just checked/installed.
                    module = canonical.removeprefix('src/').removesuffix('.lean').replace('/', '.')
                    run(['lake', 'build', module])
        if 'specs' in families:
            if not force and is_family_clean('specs'):
                if checking:
                    populate_clean_family('specs', out)
                    print(f'cached specs: all {len(family_artifacts("specs"))} artifacts current', flush=True)
                else:
                    print(f'skip specs: all {len(family_artifacts("specs"))} artifacts current', flush=True)
            else:
                run(['lake', 'build', 'Conform.Cli.EmitSpecs', 'Effect4.Program.Typing'])
                canonical = 'src/Effect4/Laws/Program/Typing/Specs.lean'
                temp = out / canonical
                run(['lake', 'env', 'lean', '-M4096', '--run', 'tools/Conform/Cli/EmitSpecs.lean',
                     'tools/Conform/Effect4/specs.json', str(temp)])
                install(temp, ROOT / canonical, checking)
        routes = [('eff', 'EffGen', 'ocaml/eff'),
                  ('wire', 'EffWire', 'ocaml/goldens/eff'),
                  ('cas', 'CasGoldens', 'ocaml/engine/cas/goldens'),
                  ('ts', 'TsGen', 'ts/eff')]
        for family, tool, target in routes:
            if family not in families:
                continue
            if not force and is_family_clean(family):
                if checking:
                    populate_clean_family(family, out)
                    print(f'cached {family}: all {len(family_artifacts(family))} artifacts current', flush=True)
                else:
                    print(f'skip {family}: all {len(family_artifacts(family))} artifacts current', flush=True)
                continue
            temp = out / target
            temp.mkdir(parents=True, exist_ok=True)
            if family == 'ts':
                # The delegated script caps its build and Lean invocation separately.
                subprocess.run(['bash', 'scripts/generate-ts-eff.sh', str(temp)], check=True)
            else:
                run(['lake', 'build', 'OCaml5.Tools.' + tool])
                run(['lake', 'env', 'lean', '-M4096', '--run',
                     'src/OCaml5/Tools/' + tool + '.lean', str(temp)])
            if not checking:
                for source in sorted(temp.rglob('*')):
                    if source.is_file():
                        install(source, ROOT / target / source.relative_to(temp), False)
            if family == 'eff':
                engine_out = out / 'ocaml/engine'
                run(['python3', 'scripts/generate-engine-structure.py',
                     '--descriptor', str(temp / 'program-structure.json'), '--out', str(engine_out)])
                if not checking:
                    for source in sorted(engine_out.iterdir()):
                        if source.is_file():
                            install(source, ROOT / 'ocaml/engine' / source.name, False)
        if 'readme' in families:
            if not force and is_family_clean('readme'):
                print('skip readme: all 1 artifacts current', flush=True)
            else:
                # A host producer, not a Lean one: it reads profile/forms/taxonomy `.gen.ts` and
                # writes `ts/eff/ingest/README.md` in place. Its own `--check` is the drift form,
                # so the temporary-output route does not apply to it.
                run(['bun', 'ts/eff/ingest/render-readme.ts', *(['--check'] if checking else [])])
        if 'lcnf' in families:
            if checking:
                raise ValueError('LCNF is stamp-only in Phase 0; no temporary regeneration')
            if not force and is_family_clean('lcnf'):
                print('skip lcnf: all 4 artifacts current', flush=True)
            else:
                run(['lake', 'build', 'Effect4', 'OCaml5.Tools.LcnfGen'])
                for target in ['ocaml/gen/api_gen.ml', 'ocaml/engine/api_engine.ml']:
                    text = (ROOT / target).read_text()
                    command = text.split('Regenerate with:\n', 1)[1].split('*)', 1)[0].strip()
                    # These are exactly the two commands published in the headers.
                    run(['lake', 'env', *shlex.split(command)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only', choices=ALL + ['lcnf'])
    parser.add_argument('--all', action='store_true',
                        help='every family of the named order: ' + ', '.join(ALL))
    parser.add_argument('--force', action='store_true',
                        help='regenerate even when outputs are clean')
    parser.add_argument('--output-dir')
    args = parser.parse_args()
    if args.only and args.all:
        raise ValueError('--only and --all are exclusive')
    generate([args.only] if args.only else ALL, args.output_dir, args.force)
    print('PASS generate: requested producers ran in dependency order')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit('FAIL generate: ' + str(error))
