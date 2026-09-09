"""Dependency ordering and temporary output installation for scripts/generate.sh."""
import argparse
from pathlib import Path
import json
import os
import shlex
import subprocess
import tempfile

from generated_bytes import comparable

ROOT = Path(__file__).resolve().parents[2]


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


def generate(families, output):
    checking = output is not None
    with tempfile.TemporaryDirectory(prefix='effect4-generate-') as scratch:
        out = Path(output).resolve() if checking else Path(scratch)
        out.mkdir(parents=True, exist_ok=True)
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
                # Schema depends on the Json projection just checked/installed.
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
        if 'lcnf' in families:
            if checking:
                raise ValueError('LCNF is stamp-only in Phase 0; no temporary regeneration')
            run(['lake', 'build', 'Effect4', 'OCaml5.Tools.LcnfGen'])
            for target in ['ocaml/gen/api_gen.ml', 'ocaml/engine/api_engine.ml']:
                text = (ROOT / target).read_text()
                command = text.split('Regenerate with:\n', 1)[1].split('*)', 1)[0].strip()
                # These are exactly the two commands published in the headers.
                run(['lake', 'env', *shlex.split(command)])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only', choices=['derived', 'eff', 'wire', 'cas', 'ts', 'lcnf'])
    parser.add_argument('--output-dir')
    args = parser.parse_args()
    generate([args.only] if args.only else ['derived', 'eff', 'wire', 'cas', 'ts'], args.output_dir)
    print('PASS generate: requested producers ran in dependency order')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, subprocess.CalledProcessError) as error:
        raise SystemExit('FAIL generate: ' + str(error))
