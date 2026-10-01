#!/usr/bin/env python3
"""The generators' fixtures (data wave, commit 2; seat W2): every extension of the derived-code
generators run on a fixture family, refused where it must refuse, its output compiled where it
must hold.

    python3 scripts/test-generators.py [--keep DIR] [CASE ...]     default: every case, in order

Properties. Reads the fixture families and controls under `Test/fixtures/generators/` (a module
root of its own, outside the module-closure gate: `Test/Audit/AxiomGate.lean:348-353`) and the
generators under `tools/` and `src/OCaml5/Tools/`. Every module is compiled into a scratch
directory outside the worktree (a fresh temporary one unless `--keep` names one), never into
`.lake/build` and never onto a tracked path; the generators' outputs land there too. One Lean
process at a time, `LEAN_NUM_THREADS=1`, warnings as errors. Each compiled module's
`#print axioms` lines are read back: an axiom outside `[propext, Quot.sound]` fails the case. One
line per case; the exit code is 0 only when every case is as expected (1 otherwise, 2 on a usage
error). The cases run in order and later ones read earlier ones' outputs, so a named subset runs
its prerequisites first.

The cases and what each one holds (the evidence words of the seat's receipt):

  elim-refuses-plain    tested: `--kind Effect4.Program.Ty=elim` refused, no member under a container
  elim-refuses-param    tested: `--kind Effect4.Program.Eff=elim` refused, a parameterised family
  elim-record           tested: the `elim` kind on the record fixture; the output compiles
  elim-val-agrees       proved: on `Store.Val` the generated companions are the hand ones
  fold-record           tested: the fold group of the nested record fixture compiles
  view-record           tested: the view at a field-list head (no table: today's literal rule) compiles
  view-no-arity         tested: a field-list head whose variance row has no arity word is refused
  view-leaf-one         tested: the view in table mode at today's one edge (`lit < string`) compiles
  view-leaf-cyclic      tested: a cyclic leaf-order table is refused by name before a line is written
  variances-module      tested: the variances producer's core module (`--lean-out`) compiles
  wave-view             tested: the wave fixture (variable-arity heads and the four-edge table) compiles
  wave-controls         proved: `nat ⊑ number` accepted, its converse rejected, through the restated laws
"""
import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'Test/fixtures/generators'
CEILING = {'propext', 'Quot.sound'}
AXIOM_LINE = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")


class CaseFailed(Exception):
    pass


class Context:
    def __init__(self, build):
        self.build = Path(build)
        self.olean = self.build / 'olean'
        self.src = self.build / 'src'
        self.olean.mkdir(parents=True, exist_ok=True)
        self.src.mkdir(parents=True, exist_ok=True)
        self.env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(self.olean))

    def run(self, args, cwd=ROOT):
        return subprocess.run(args, cwd=cwd, env=self.env, capture_output=True, text=True)

    # --------------------------------------------------------------------- the steps
    def compile(self, path, root=None, expect_fail=None):
        """Compile one module into the scratch tree. `root` is the module root (the fixtures'
        own, or the scratch `src` for a generated file). With `expect_fail`, the compile must
        fail and its output must contain that text."""
        path = Path(path)
        root = Path(root) if root else FIXTURES
        stem = path.relative_to(root).with_suffix('')
        out = self.olean / stem
        out.parent.mkdir(parents=True, exist_ok=True)
        r = self.run(['lake', 'env', 'lean', '-R', str(root), '-DwarningAsError=true', '-M6144',
                      '-o', str(out) + '.olean', '-i', str(out) + '.ilean', str(path)])
        text = r.stdout + r.stderr
        if expect_fail is not None:
            if r.returncode == 0:
                raise CaseFailed(f'{stem}: compiled, but it must fail with {expect_fail!r}')
            if expect_fail not in text:
                raise CaseFailed(f'{stem}: failed without {expect_fail!r}:\n{text[-3000:]}')
            return text
        if r.returncode != 0:
            raise CaseFailed(f'{stem}: does not compile:\n{text[-4000:]}')
        bad = []
        for line in text.splitlines():
            m = AXIOM_LINE.match(line.strip())
            if m and m.group(2):
                over = {a.strip() for a in m.group(2).split(',')} - CEILING
                if over:
                    bad.append(f'{m.group(1)}: {sorted(over)}')
        if bad:
            raise CaseFailed(f'{stem}: above the ceiling {sorted(CEILING)}: {bad}')
        return text

    def tool(self, tool, args, expect_fail=None):
        """Run a generator (`lake env lean --run <tool> …`); with `expect_fail`, it must exit
        non-zero with that text in its output."""
        r = self.run(['lake', 'env', 'lean', '-DwarningAsError=true', '-M4096', '--run', tool, *args])
        text = r.stdout + r.stderr
        if expect_fail is not None:
            if r.returncode == 0:
                raise CaseFailed(f'{tool}: exit 0, but it must refuse with {expect_fail!r}')
            if expect_fail not in text:
                raise CaseFailed(f'{tool}: refused without {expect_fail!r}:\n{text[-3000:]}')
            return text
        if r.returncode != 0:
            raise CaseFailed(f'{tool} {" ".join(args)}: exit {r.returncode}:\n{text[-4000:]}')
        return text

    def gen(self, rel):
        """A path under the scratch `src` root, its directory created."""
        p = self.src / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        return p


FOLD = 'tools/Effect4Gen/Fold.lean'
VIEW = 'tools/Effect4Gen/View.lean'
VARIANCES = 'tools/Tools/Variances.lean'
VIEW_IMPORTS = 'Effect4.Laws.Auto.RuleSets,Effect4.Machine.Alphabets'


def variances_with(cx, name, rows):
    """Today's variance table with fixture head rows appended, written to the scratch tree: the
    rows a commit-4 constructor would carry, without touching the tracked table."""
    table = json.loads((ROOT / 'tools/Effect4Gen/variances.json').read_text())
    table['heads'] += rows
    out = cx.build / name
    out.write_text(json.dumps(table, indent=1))
    return out


RECORD_ROW = {'head': 'record', 'source': 'printer', 'arity': 'each', 'variance': ['co'],
              'spelling': '{ readonly a: A; … }', 'note': 'fixture: every field covariant (readonly)'}
WAVE_ROWS = [RECORD_ROW,
             {'head': 'map', 'source': 'printer', 'variance': ['inv', 'co'],
              'spelling': 'Readonly<Record<K, V>>', 'note': 'fixture: key exact, value covariant'},
             {'head': 'tuple', 'source': 'printer', 'arity': 'each', 'variance': ['co'],
              'spelling': 'readonly [A, B, C]', 'note': 'fixture: every item covariant'},
             {'head': 'app', 'source': 'declarations', 'arity': 'byName', 'variance': [],
              'note': "fixture: each argument at the named declaration's variance"}]


# ------------------------------------------------------------------------- the cases
def elim_refuses_plain(cx):
    cx.tool(FOLD, ['--group', 'TyEq', '--imports', 'Effect4.Program.Ty', '--out',
                   str(cx.gen('Refused/TyEq.lean')), '--kind', 'Effect4.Program.Ty=elim',
                   'Effect4.Program.Ty'],
            expect_fail='elim: Effect4.Program.Ty has no member under a container')


def elim_refuses_param(cx):
    cx.tool(FOLD, ['--group', 'EffEq', '--imports', 'Effect4.Program.Eff', '--out',
                   str(cx.gen('Refused/EffEq.lean')), '--kind', 'Effect4.Program.Eff=elim',
                   'Effect4.Program.Eff'],
            expect_fail='elim: Effect4.Program.Eff has parameters or indices')


def elim_record(cx):
    cx.compile(FIXTURES / 'GenFix/Record/TyCore.lean')
    out = cx.gen('GenFix/Record/TyEq.lean')
    cx.tool(FOLD, ['--group', 'TyEq', '--imports', 'GenFix.Record.TyCore', '--out', str(out),
                   '--kind', 'GenFix.Record.Ty=elim', 'GenFix.Record.Ty'])
    text = cx.compile(out, cx.src)
    for name in ['GenFix.Record.Ty.ind', 'GenFix.Record.Ty.beq_iff', 'GenFix.Record.instDecidableEqTy',
                 'GenFix.Record.instReprTy']:
        if f"'{name}'" not in text:
            raise CaseFailed(f'TyEq: no axiom receipt for {name}')
    cx.compile(FIXTURES / 'GenFix/Record/Ty.lean')


def elim_val_agrees(cx):
    out = cx.gen('GenFix/ValElim.lean')
    cx.tool(FOLD, ['--group', 'ValElim', '--imports', 'Effect4.Store.Carrier.Val', '--out', str(out),
                   '--kind', 'Effect4.Store.Val=elim:GenFixVal.Val', 'Effect4.Store.Val'])
    cx.compile(out, cx.src)
    cx.compile(FIXTURES / 'GenFix/Controls/ElimAgrees.lean')


def fold_record(cx):
    out = cx.gen('GenFix/Record/Fold.lean')
    cx.tool(FOLD, ['--group', 'Fold', '--imports', 'GenFix.Record.Ty', '--out', str(out),
                   'GenFix.Record.Ty'])
    text = out.read_text()
    for absent in ['foldM_ty', 'TyMAlgebra', 'foldMapAt_ty']:
        if re.search(r'\b' + absent + r'\b', text):
            raise CaseFailed(f'Fold: the nested block emitted {absent} (the monadic-fold decision)')
    cx.compile(out, cx.src)


def view_record(cx):
    table = variances_with(cx, 'variances-record.json', [RECORD_ROW])
    out = cx.gen('GenFix/Record/TyView.lean')
    cx.tool(VIEW, ['--group', 'TyView', '--imports', 'GenFix.Record.Fold,' + VIEW_IMPORTS,
                   '--variances', str(table), '--out', str(out), 'GenFix.Record.Ty'])
    text = out.read_text()
    if 'litRule' not in text or 'leafRule' in text:
        raise CaseFailed('TyView: a family with no leaf table must read today\'s literal rule')
    cx.compile(out, cx.src)


def view_no_arity(cx):
    row = {k: v for k, v in RECORD_ROW.items() if k != 'arity'}
    table = variances_with(cx, 'variances-record-no-arity.json', [row])
    cx.tool(VIEW, ['--group', 'TyView', '--imports', 'GenFix.Record.Fold,' + VIEW_IMPORTS,
                   '--variances', str(table), '--out', str(cx.gen('Refused/TyView.lean')),
                   'GenFix.Record.Ty'],
            expect_fail='View: `Ty.record` has variable arity')


def view_leaf_one(cx):
    cx.compile(FIXTURES / 'GenFix/LeafOne/Ty.lean')
    fold = cx.gen('GenFix/LeafOne/Fold.lean')
    cx.tool(FOLD, ['--group', 'Fold', '--imports', 'GenFix.LeafOne.Ty', '--out', str(fold),
                   'GenFix.LeafOne.Ty'])
    cx.compile(fold, cx.src)
    out = cx.gen('GenFix/LeafOne/TyView.lean')
    cx.tool(VIEW, ['--group', 'TyView', '--imports', 'GenFix.LeafOne.Fold,' + VIEW_IMPORTS,
                   '--out', str(out), 'GenFix.LeafOne.Ty'])
    text = out.read_text()
    for needed in ['hleaf : leafRule a b = false', 'theorem leafLe_antisymm', 'theorem leafRule_trans',
                   'theorem sub_eq_leafRule_of_not_sameHead', 'lit_string :']:
        if needed not in text:
            raise CaseFailed(f'TyView: table mode did not emit {needed!r}')
    if re.search(r'\blitRule\b', text):
        raise CaseFailed('TyView: table mode still emits `litRule`')
    cx.compile(out, cx.src)


def view_leaf_cyclic(cx):
    cx.compile(FIXTURES / 'GenFix/LeafCyclic/Ty.lean')
    out = cx.gen('Refused/LeafCyclic.lean')
    cx.tool(VIEW, ['--group', 'TyView', '--imports', 'GenFix.LeafCyclic.Ty', '--out', str(out),
                   'GenFix.LeafCyclic.Ty'],
            expect_fail='is cyclic: its closure puts `nat` below `int` and `int` below `nat`')
    if out.exists():
        raise CaseFailed('the refused view wrote its output anyway')


def variances_module(cx):
    cx.compile(FIXTURES / 'GenFix/Wave/TyCore.lean')
    module = cx.gen('GenFix/Wave/TyVariance.lean')
    cx.tool(VARIANCES, [str(cx.build / 'variances-wave-out.json'), '--lean-out', str(module),
                        '--lean-namespace', 'GenFix.Wave'])
    text = module.read_text()
    for needed in ['def argVariance', 'def declaredVariance', '"Layer.Layer" => [.contra, .co, .co]']:
        if needed not in text:
            raise CaseFailed(f'TyVariance: no {needed!r}')
    cx.compile(module, cx.src)


def wave_view(cx):
    eq = cx.gen('GenFix/Wave/TyEq.lean')
    cx.tool(FOLD, ['--group', 'TyEq', '--imports', 'GenFix.Wave.TyCore', '--out', str(eq),
                   '--kind', 'GenFix.Wave.Ty=elim', 'GenFix.Wave.Ty'])
    cx.compile(eq, cx.src)
    cx.compile(FIXTURES / 'GenFix/Wave/Ty.lean')
    fold = cx.gen('GenFix/Wave/Fold.lean')
    cx.tool(FOLD, ['--group', 'Fold', '--imports', 'GenFix.Wave.Ty', '--out', str(fold), 'GenFix.Wave.Ty'])
    cx.compile(fold, cx.src)
    table = variances_with(cx, 'variances-wave.json', WAVE_ROWS)
    out = cx.gen('GenFix/Wave/TyView.lean')
    cx.tool(VIEW, ['--group', 'TyView', '--imports', 'GenFix.Wave.Fold,' + VIEW_IMPORTS,
                   '--variances', str(table), '--out', str(out), 'GenFix.Wave.Ty'])
    text = out.read_text()
    for needed in ['#guard Ty.sub .nat .number  -- derived through the closure, not an entry',
                   '#guard !Ty.sub .number .nat', 'theorem sub_args_record', 'theorem sub_args_app',
                   'theorem leafHead_facts', 'normalize t = t', 'nat_int :', 'undefined_unit :']:
        if needed not in text:
            raise CaseFailed(f'TyView: the wave view did not emit {needed!r}')
    cx.compile(out, cx.src)


def wave_controls(cx):
    text = cx.compile(FIXTURES / 'GenFix/Controls/WaveOrder.lean')
    for name in ['nat_sub_number', 'number_not_sub_nat', 'undefined_sub_unit', 'unit_not_sub_undefined']:
        if f"'GenFix.Controls.{name}'" not in text:
            raise CaseFailed(f'WaveOrder: no axiom receipt for {name}')


CASES = [
    ('elim-refuses-plain', elim_refuses_plain),
    ('elim-refuses-param', elim_refuses_param),
    ('elim-record', elim_record),
    ('elim-val-agrees', elim_val_agrees),
    ('fold-record', fold_record),
    ('view-record', view_record),
    ('view-no-arity', view_no_arity),
    ('view-leaf-one', view_leaf_one),
    ('view-leaf-cyclic', view_leaf_cyclic),
    ('variances-module', variances_module),
    ('wave-view', wave_view),
    ('wave-controls', wave_controls),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('cases', nargs='*', metavar='CASE')
    parser.add_argument('--keep', metavar='DIR', help='build into DIR and keep it (default: a fresh temporary directory, removed on success)')
    args = parser.parse_args()
    names = [n for n, _ in CASES]
    unknown = [c for c in args.cases if c not in names]
    if unknown:
        parser.error(f'unknown cases {unknown}; choose from {names}')
    # a named case runs after every case before it: the later ones read the earlier ones' outputs
    last = max((names.index(c) for c in args.cases), default=len(names) - 1)
    build = Path(args.keep) if args.keep else Path(tempfile.mkdtemp(prefix='effect4-generators-'))
    cx = Context(build)
    failed = 0
    for name, fn in CASES[:last + 1]:
        try:
            fn(cx)
            print(f'PASS {name}', flush=True)
        except CaseFailed as error:
            failed += 1
            print(f'FAIL {name}: {error}', flush=True)
    total = last + 1
    print(f'test-generators: {total - failed} of {total} cases as expected; build {build}')
    if failed == 0 and not args.keep:
        shutil.rmtree(build, ignore_errors=True)
    return 0 if failed == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
