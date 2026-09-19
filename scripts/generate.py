"""The producers behind `make gen-*`: one family per call, run in place or into a directory.

`python3 scripts/generate.py --only <family>` regenerates that family's files in the tree;
`--output-dir DIR` writes them under DIR instead and refuses if a file differs from the
committed one (the drift check's temporary route). Ordering and staleness are the
Makefile's: each `gen-*` rule names the generator's sources and the Lake traces of the
compiled core it reads, and `make check-gen` regenerates every group without trusting
file times. Nothing here reads or writes a provenance label.
"""
import argparse
from pathlib import Path
import json
import os
import shlex
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


# Every producer runs under one wall-clock budget, so a hung generator fails a lane instead
# of hanging it. The budget is not a performance statement and it is not a target: it has to
# cover the `lake build` each family runs first -- a cold build of the core is minutes -- and
# the slowest cut on a machine that is busy. Measured on a quiet machine with the core
# already built, `--only lcnf`'s four cuts are 37s end to end (the engine face 18s of it);
# the same group was measured at 14m38s under four concurrent Lean compilers, past the old
# 600s, which is why `--only lcnf` could not complete at all. One number for every command.
TIMEOUT = os.environ.get('EFFECT4_GEN_TIMEOUT', '5400')


def run(args, capture=False):
    print('+ ' + shlex.join(args), flush=True)
    return subprocess.run(['timeout', TIMEOUT, *args], check=True,
                          stdout=subprocess.PIPE if capture else None, text=True).stdout


def install(source, destination, checking):
    data = source.read_bytes()
    if checking:
        if not destination.is_file() or data != destination.read_bytes():
            raise ValueError(f'{destination.relative_to(ROOT)} is not what Lean emits')
        return
    destination.parent.mkdir(parents=True, exist_ok=True)
    if not destination.is_file() or data != destination.read_bytes():
        destination.write_bytes(data)


# The producers' dependency order (DI-33): `variances` reads declaration-site variance off the
# vendored rc.112 sources and is an INPUT of `derived`, so it is first; `derived` writes the
# Lean projections the rest import; `eff`, `wire` and `cas` cut the OCaml estate from them;
# `ts` cuts the TypeScript estate; `readme` renders the ingest tables out of three files `ts`
# just wrote. `lcnf` is the explicit Phase 1 route and is requested by name.
ALL = ['variances', 'derived', 'eff', 'wire', 'cas', 'ts', 'readme']

# The variance table, its producer and its landing path (tooling plan 1.4a).
VARIANCES = 'tools/Effect4Gen/variances.json'

# The four LCNF outputs; each carries the exact command that regenerates it in its header.
LCNF = ['ocaml/gen/fibers_gen.ml', 'ocaml/gen/machine_gen.ml',
        'ocaml/gen/api_gen.ml', 'ocaml/engine/api_engine.ml']


def generate(families, output):
    checking = output is not None
    with tempfile.TemporaryDirectory(prefix='effect4-generate-') as scratch:
        out = Path(output).resolve() if checking else Path(scratch)
        out.mkdir(parents=True, exist_ok=True)
        if 'variances' in families:
            run(['lake', 'build', 'Tools.Variances'])
            temp = out / VARIANCES
            temp.parent.mkdir(parents=True, exist_ok=True)
            run(['lake', 'env', 'lean', '-M4096', '--run',
                 'tools/Tools/Variances.lean', str(temp)])
            install(temp, ROOT / VARIANCES, checking)
        if 'derived' in families:
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
                # Schema depends on the Json projection just checked/installed. A group whose
                # output is not a Lean module of the library -- the TypeScript prelude's atom
                # block -- has no module to build, and naming one would be a target that does
                # not exist.
                if canonical.startswith('src/') and canonical.endswith('.lean'):
                    module = canonical.removeprefix('src/').removesuffix('.lean').replace('/', '.')
                    run(['lake', 'build', module])
        routes = [('eff', 'EffGen', 'ocaml/eff'),
                  ('wire', 'EffWire', 'ocaml/goldens/eff'),
                  ('cas', 'CasGoldens', 'ocaml/engine/cas/goldens'),
                  ('ts', 'TsGen', 'ts/eff')]
        for family, tool, target in routes:
            if family not in families:
                continue
            temp = out / target
            temp.mkdir(parents=True, exist_ok=True)
            # `Tools.TsGen` (a Tools module) writes the TypeScript estate; the three OCaml
            # tools live under src/OCaml5/Tools. Every family reads the closed world off the
            # environment, so nothing here is typed by hand.
            source = 'tools/Tools/TsGen.lean' if family == 'ts' else 'src/OCaml5/Tools/' + tool + '.lean'
            run(['lake', 'build', ('Tools.' if family == 'ts' else 'OCaml5.Tools.') + tool])
            run(['lake', 'env', 'lean', '-M4096', '--run', source, str(temp)])
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
            # A host producer, not a Lean one: it reads profile/forms/taxonomy `.gen.ts` and
            # writes `ts/eff/ingest/README.md` in place. Its own `--check` is the drift form,
            # so the temporary-output route does not apply to it.
            run(['bun', 'ts/eff/ingest/render-readme.ts', *(['--check'] if checking else [])])
        if 'lcnf' in families:
            if checking:
                raise ValueError('LCNF regenerates in place only; the drift check is `git diff`')
            run(['lake', 'build', 'Effect4', 'OCaml5.Tools.LcnfGen'])
            for target in LCNF:
                text = (ROOT / target).read_text()
                command = text.split('Regenerate with:\n', 1)[1].split('*)', 1)[0].strip()
                # These are exactly the commands published in the headers.
                run(['lake', 'env', *shlex.split(command)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only', choices=ALL + ['lcnf'])
    parser.add_argument('--all', action='store_true',
                        help='every family of the named order: ' + ', '.join(ALL))
    parser.add_argument('--output-dir')
    args = parser.parse_args()
    if args.only and args.all:
        raise ValueError('--only and --all are exclusive')
    generate([args.only] if args.only else ALL, args.output_dir)
    print('PASS generate: requested producers ran in dependency order')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit('FAIL generate: ' + str(error))
