#!/usr/bin/env python3
"""Build a project outside ocaml/ against the installed public facade, with its red controls.

The facade (ocaml/gen/facade/effect4.ml, GENERATED from ocaml/gen/public-names.tsv) is the
library effect4_gen.effect4. This check installs the workspace's packages into dune's install
tree (`dune build @install`), writes a project into a temporary directory outside the
repository, and builds it with OCAMLPATH set to that tree, as an installed client would.

The positive client names R6.2's frozen paths through the facade, uses the facade's types as
the owner's and the implementation's types, and runs one program through the call tree. Each
red client must fail with OCaml's own error at the line it names:
- a coverage root named through the facade, and through the installed Api_gen;
- a linkage root named through the facade;
- each sealed package (Built, Prepared, Checked, the tool Session, Memo) built or updated
  through a facade alias.

These finite controls establish name scope and sealing for one installed client. They
establish no behaviour of the generated code beyond the one run the positive client prints.
"""
from pathlib import Path
import os
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[1]
dune = ['opam', 'exec', '--switch=effect4', '--', 'dune']
library = 'effect4_gen.effect4'

OK = '''(* An installed client of the public facade: R6.2's frozen paths, the type equalities, one run. *)
let program : Effect4.Program.NativeOp.t Effect4.Program.Eff.t =
  Effect4.Program.Eff.Succeed (Effect4.Program.Term.Lit (Effect4.Program.Lit.Nat 42))

(* The facade's types are the owner's and the implementation's, not copies. *)
let (_ : Eff_types.NativeOp.t Eff_types.Eff.t) = program
let of_program =
  if Sys.opaque_identity true then Effect4.Run.Tree.of_program
  else Effect4_gen.Api_gen.run_tree_of_program
let _tree = of_program [] 100 program
let (_ : Effect4.Store.Val.t) = Effect4.Store.Val.Nat 7
let (_ : Effect4.Tool.Native.Session.t) = Effect4.Tool.Native.start
let (_ : Effect4.Program.Check.Memo.t) = Effect4.Program.Check.Memo.empty
let (_ : Effect4_gen.Api_gen.memo) = Effect4.Program.Check.Memo.empty
let _loop_with = Effect4.Program.Authoring.loop_with

let () =
  match Effect4.Run.Tree.settle [] 100 Effect4.Run.Tree.Host.silent () program with
  | Some (steps, _) ->
    Printf.printf "settled after %d steps; a nat is %s\\n" steps
      (Effect4.Run.Kit.ty_text Effect4.Program.Ty.Nat)
  | None -> print_endline "not settled"
'''

# name: (client source, a fragment OCaml's error must contain)
RED = {
    'coverage_facade': ('let _ = Effect4.Machine.Dispatcher.insert\n',
                        'Unbound module Effect4.Machine.Dispatcher'),
    'coverage_api_gen': ('let _ = Effect4_gen.Api_gen.dispatcher_insert\n',
                         'Unbound value Effect4_gen.Api_gen.dispatcher_insert'),
    'linkage_facade': ('let _ = Effect4.Program.err_of\n', 'Unbound value Effect4.Program.err_of'),
    'built_literal': ('type alias = Effect4.Api.Built.t\n'
                      'let forged : alias = { app = { rows = []; services = []; types = [] };\n'
                      '  program = Eff_types.Eff.Succeed (Eff_types.Term.Lit Eff_types.Lit.Unit);\n'
                      '  admitted = { answer = Eff_types.Ty.Nat; error = Eff_types.Ty.Never; requires = [] };\n'
                      '  row_names = [] }\n', 'Unbound record field app'),
    'prepared_update': ('let forge (p : Effect4.Program.Prepared.t) = { p with table = [] }\n',
                        'Unbound record field table'),
    'checked_literal': ('let forged : int Effect4.Program.Check.Checked.t = { value = 7; trace = [] }\n',
                        'Unbound record field value'),
    'session_update': ('let forge (s : Effect4.Tool.Native.Session.t) = { s with memo = [] }\n',
                       'Unbound record field memo'),
    'memo_literal': ('let forged : Effect4.Program.Check.Memo.t = []\n',
                     "This expression has type 'a list"),
}

def write_project(directory):
    (directory / 'dune-project').write_text('(lang dune 3.0)\n')
    for name, source in [('ok', OK)] + [('red_' + n, s) for n, (s, _) in RED.items()]:
        folder = directory / name
        folder.mkdir()
        (folder / 'dune').write_text(f'(executable\n (name {name})\n (libraries {library}))\n')
        (folder / f'{name}.ml').write_text(source)

def main():
    subprocess.run([*dune, 'build', '--root', str(root / 'ocaml'), '@install'], check=True)
    lib = root / 'ocaml/_build/install/default/lib'
    env = dict(os.environ, OCAMLPATH=os.pathsep.join(
        [str(lib)] + ([os.environ['OCAMLPATH']] if os.environ.get('OCAMLPATH') else [])))
    failures = []
    with tempfile.TemporaryDirectory(prefix='effect4-facade-client-') as name:
        project = Path(name)
        assert root not in project.resolve().parents, 'the client must live outside the repository'
        write_project(project)
        def build(target):
            return subprocess.run([*dune, 'build', '--root', str(project), f'./{target}/{target}.exe'],
                                  env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        result = build('ok')
        print(f'ok: exit {result.returncode}')
        if result.returncode != 0:
            print(result.stdout)
            failures.append('ok')
        else:
            run = subprocess.run([str(project / '_build/default/ok/ok.exe')], text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(f'ok: runs, exit {run.returncode}: {run.stdout.strip()}')
            if run.returncode != 0 or not run.stdout.startswith('settled after '):
                failures.append('ok-run')
        for red, (_, fragment) in RED.items():
            result = build('red_' + red)
            refused = (result.returncode != 0 and 'Error' in result.stdout and fragment in result.stdout
                       and 'not found' not in result.stdout)
            print(f'red_{red}: exit {result.returncode}, refused by OCaml: {refused}')
            if not refused:
                print(result.stdout)
                failures.append('red_' + red)
    if failures:
        print('FAIL check-public-facade: ' + ', '.join(failures))
        return 1
    print(f'PASS: an outside project builds against {library} and runs; '
          f'{len(RED)} red clients are refused by OCaml')
    return 0

if __name__ == '__main__':
    sys.exit(main())
