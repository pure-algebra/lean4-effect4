#!/usr/bin/env python3
"""Compile clients against the generated units to check the recipe's export classes.

The recipe (ocaml/gen/roots.json, read by OCaml5.Lcnf.Export) gives each root one class.
An artefact's interface exports its public and linkage roots and hides its internal and
coverage roots. Each case below compiles one client with ocamlc. A positive case must
compile. A red case must fail with OCaml's own error, and the error must name the
refused value. The OCaml workspace must already be built (make check-ocaml builds it).
These finite controls establish interface scope only: no behaviour and no lowering.
"""
from pathlib import Path
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[1]
build = root / 'ocaml/_build/default'
includes = ['gen/.effect4_gen.objs/byte', 'eff/.effect4_eff.objs/byte',
            'clock/.effect4_clock.objs/byte', 'lcnf/.effect4_lcnf.objs/byte',
            'engine/.effect4_engine.objs/byte', 'engine/bytes/.effect4_bytes.objs/byte']
compiler = ['opam', 'exec', '--switch=effect4', '--', 'ocamlc', '-color', 'never',
            '-I', '+unix', '-I', '+threads']
for directory in includes:
    compiler += ['-I', str(build / directory)]

G = 'module G = Effect4_gen.Api_gen\n'
E = 'module E = Effect4_engine.Api_engine_inst\n'
# name: (expected exit, client source, the text a refusal must name)
cases = {
    # Api_gen: a public root and a linkage root are exported; a coverage root is hidden.
    'api-gen-public': (0, G + 'let f = G.run_tree_of_program\n', None),
    'api-gen-linkage': (0, G + 'let s = G.stores_empty\n', None),
    'api-gen-coverage': (2, G + 'let f = G.dispatcher_insert\n', 'dispatcher_insert'),
    'api-gen-coverage-machine': (2, G + 'let f = G.run_machine_update\n', 'run_machine_update'),
    # Api_engine, through the instance whose interface includes the functor's result: a linkage
    # root is exported; an internal root (called by the prelude only) and a coverage root are not.
    'engine-linkage': (0, E + 'let c = E.empty_ctx\n', None),
    'engine-internal': (2, E + 'let f = E.scope_make\n', 'scope_make'),
    'engine-coverage': (2, E + 'let f = E.step_decision_state\n', 'step_decision_state'),
}

def main():
    failures = []
    with tempfile.TemporaryDirectory(prefix='effect4-export-classes-') as directory:
        for name, (expected, source, refused) in cases.items():
            path = Path(directory) / 'client.ml'
            path.write_text(source)
            result = subprocess.run([*compiler, '-c', str(path)], text=True, cwd=directory,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(f'{name}: exit {result.returncode}, expected {expected}')
            ok = result.returncode == expected
            if expected:
                ok = ok and 'Error: Unbound value' in result.stdout and refused in result.stdout
            if not ok:
                print(result.stdout)
                failures.append(name)
    if failures:
        print('FAIL check-export-classes: ' + ', '.join(failures))
        return 1
    accepted = sum(expected == 0 for expected, _, _ in cases.values())
    print(f'PASS: {accepted} exported roots compile; {len(cases) - accepted} hidden roots are unbound')
    return 0

if __name__ == '__main__':
    sys.exit(main())
