#!/usr/bin/env python3
"""Compile positive aliases and hostile clients against the real generated API.

The generated library must already be built. Every rejection must be OCaml's
ordinary type error. These finite controls establish package sealing only.
"""
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
includes = ['gen/.effect4_gen.objs/byte', 'eff/.effect4_eff.objs/byte',
            'clock/.effect4_clock.objs/byte', 'lcnf/.effect4_lcnf.objs/byte']
compiler = ['opam', 'exec', '--switch=effect4', '--', 'ocamlc', '-color', 'never']
for directory in includes:
    compiler += ['-I', str(root / 'ocaml/_build/default' / directory)]
cases = {
    'lawful-alias': (0, "type public_alias = A.memo\nlet value : public_alias = A.program_check_memo_empty\n"),
    'built-literal': (2, "type public_built_alias = A.built\nlet forged : public_built_alias = { app = { rows = []; services = []; types = [] }; program = Eff_types.Eff.Perform (Eff_types.NativeOp.External 0, Eff_types.Term.Lit Eff_types.Lit.Unit); admitted = { answer = Eff_types.Ty.Nat; error = Eff_types.Ty.Never; requires = [] }; row_names = [] }\n"),
    'memo-public-alias': (2, "type public_alias = A.memo\nlet forged : public_alias = []\n"),
    'checked-literal': (2, "let forged : int A.checked = { value = 7; trace = [] }\n"),
    'oracle-callback': (2, "let forged : A.oracle = fun input -> A.program_check_run input\n"),
    'hit-rule-callback': (2, "let forged : A.hit_rule = fun _ _ -> true\n"),
    'checked-update': (2, "let forge (c : int A.checked) = { c with value = 99 }\n"),
    'hidden-helper': (2, "let helper = A.program_check_typed_program\n"),
    'session-literal': (2, "let forged : A.session = { state = A.tool_native_start; memo = [] }\n"),
    'state-literal': (2, "let forged : A.state = { transcript = []; raw = Obj.magic 0 }\n"),
    'memo-as-session': (2, "let forged = A.tool_native_serve ([] : (A.check_input * A.verdict) list)\n"),
}
with tempfile.TemporaryDirectory(prefix='effect4-sealing-') as directory:
    for name, (expected, source) in cases.items():
        path = Path(directory) / 'client.ml'
        path.write_text('module A = Effect4_gen.Api_gen\n' + source)
        result = subprocess.run([*compiler, '-c', str(path)], text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(f'{name}: exit {result.returncode}, expected {expected}')
        print(result.stdout)
        assert result.returncode == expected, name
        if expected:
            assert 'Error:' in result.stdout, name
print('PASS: lawful public alias and ten hostile sealed-package clients')
