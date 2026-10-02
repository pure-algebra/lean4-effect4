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
  extras-record         proved: `--extras` on the nested record fixture (arguments by sort, `ArgF`):
                        the view law, uniqueness in layer form, fusion, the layer invariant, the
                        banana split, `foldMap` one layer down and both connectors, the position
                        helpers' functor laws; every law at most `[propext, Quot.sound]`
  extras-record-lengths tested: records of 0, 1, 2, 3 and 7 labelled fields through the generated
                        view, layer fold, head and paired folds; red: a two-field reading differs
                        at 3 and 7 (`GenFix/Controls/RecordExtras.lean`)
  extras-val            proved: `--extras` on `Store.Val` (a list of members, two payloads per
                        constructor); nothing written to the tree
  extras-refuses-param  tested: `--extras Effect4.Program.Eff` refused, a parameterised family
  extras-refuses-mutual tested: `--extras Effect4.Representation` refused, a mutual block
  extras-refuses-nullary tested: `--extras` on a nested family with no nullary constructor refused
  foldof-record         proved: `fold_of` through a product position and a field-list sibling
                        (`List (String × Ty)`), a paramorphism among them: six connectors
  view-record           tested: the view at a field-list head (no table: today's literal rule) compiles
  view-no-arity         tested: a field-list head whose variance row has no arity word is refused
  view-leaf-one         tested: the view in table mode at today's one edge (`lit < string`) compiles
  view-leaf-cyclic      tested: a cyclic leaf-order table is refused by name before a line is written
  variances-module      tested: the variances producer's core module (`--lean-out`) compiles
  wave-view             tested: the wave fixture (variable-arity heads and the four-edge table) compiles
  wave-controls         proved: `nat ⊑ number` accepted, its converse rejected, through the restated laws
  lcnf-zipidx           tested (host: the effect4 opam switch): a root reaching `List.zipIdx` lowers to
                        OCaml that ocamlopt builds (the `Array.mk` row) and that answers what Lean
                        answers; a redirected run writes its closure manifest beside its output
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


def receipts_present(text, prefix, names, what):
    """Every law must print its `#print axioms` line (its axioms are checked by `compile`)."""
    for name in names:
        if f"'{prefix}{name}'" not in text:
            raise CaseFailed(f'{what}: no axiom receipt for {name}')


# the laws `--extras` writes for a nested one-member block, by the family's label
def extras_laws(label, argf, positions):
    laws = [f'{label}Build_view', f'{argf}.map_comp', f'{argf}.map_id', f'{argf}.kids_map',
            'cata_ofLayer_view', 'eq_cata_ofLayer', f'cata_fusion_{label}', 'cata_ofLayer_inv',
            f'cata_prod_{label}', 'foldMap_view', 'foldMap_head_eq_cata', 'foldMap_eq_cata']
    for p in positions:
        laws += [f'map_pos_{p}_comp', f'map_pos_{p}_id', f'kids_pos_{p}_map', f'foldMap_pos_{p}_eq']
    return laws


def extras_record(cx):
    out = cx.gen('GenFix/Record/TyExtras.lean')
    cx.tool(FOLD, ['--extras', '--group', 'TyExtras', '--imports', 'GenFix.Record.Fold',
                   '--namespace', 'GenFix.Record', '--out', str(out), 'GenFix.Record.Ty'])
    text = out.read_text()
    for absent in ['TyLeaf', 'sizeOf_tyKids']:
        if re.search(r'\b' + absent + r'\b', text):
            raise CaseFailed(f'TyExtras: the nested block emitted the plain form\'s {absent}')
    if '| list_prod_string_ty (v : List (String × R))' not in text:
        raise CaseFailed('TyExtras: the field list is not an argument sort `List (String × R)`')
    receipts_present(cx.compile(out, cx.src), 'GenFix.Record.',
                     extras_laws('ty', 'TyArgF', ['prod_string_ty', 'list_prod_string_ty']), 'TyExtras')


def extras_record_lengths(cx):
    text = cx.compile(FIXTURES / 'GenFix/Controls/RecordExtras.lean')
    receipts_present(text, 'GenFix.Controls.RecordExtras.', ['size_pos', 'spell_size_rec7'], 'RecordExtras')


def extras_val(cx):
    out = cx.gen('GenFix/ValExtras.lean')
    cx.tool(FOLD, ['--extras', '--group', 'ValExtras', '--imports', 'Effect4.Store.Carrier.Fold',
                   '--namespace', 'GenFix.ValExtras', '--out', str(out), 'Effect4.Store.Val'])
    text = out.read_text()
    for needed in ['| .ref a0 a1 => [.uInt8 a0, .bytes a1]', '| list_val (v : List R)']:
        if needed not in text:
            raise CaseFailed(f'ValExtras: no {needed!r}')
    receipts_present(cx.compile(out, cx.src), 'GenFix.ValExtras.',
                     extras_laws('val', 'ValArgF', ['list_val']), 'ValExtras')


def extras_refuses_param(cx):
    out = cx.gen('Refused/EffExtras.lean')
    cx.tool(FOLD, ['--extras', '--group', 'EffExtras', '--imports', 'Effect4.Program.Fold', '--out',
                   str(out), 'Effect4.Program.Eff'],
            expect_fail='extras: Effect4.Program.Eff takes parameters')
    if out.exists():
        raise CaseFailed('the refused extras wrote their output anyway')


def extras_refuses_mutual(cx):
    out = cx.gen('Refused/SchemaExtras.lean')
    cx.tool(FOLD, ['--extras', '--group', 'SchemaExtras', '--imports', 'Effect4.Schema.Fold', '--out',
                   str(out), 'Effect4.Representation'],
            expect_fail='extras: Effect4.Representation is mutual')
    if out.exists():
        raise CaseFailed('the refused extras wrote their output anyway')


def extras_refuses_nullary(cx):
    cx.compile(FIXTURES / 'GenFix/Refuse/Rose.lean')
    out = cx.gen('Refused/RoseExtras.lean')
    cx.tool(FOLD, ['--extras', '--group', 'RoseExtras', '--imports', 'GenFix.Refuse.Rose', '--out',
                   str(out), 'GenFix.Refuse.Rose'],
            expect_fail='extras: GenFix.Refuse.Rose has no nullary constructor')
    if out.exists():
        raise CaseFailed('the refused extras wrote their output anyway')


def foldof_record(cx):
    text = cx.compile(FIXTURES / 'GenFix/Record/FoldOfScan.lean')
    for name in ['members.eq_cata', 'renderRaw.eq_cata', 'renderFields.eq_foldr', 'renderFields.eq_cata',
                 'closedFields.eq_cata', 'fieldTys.eq_cata', 'fieldTysOf.eq_foldr', 'fieldTysOf.eq_cata']:
        if f"'GenFix.Record.Ty.{name}'" not in text:
            raise CaseFailed(f'FoldOfScan: no axiom receipt for {name}')


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


def lcnf_zipidx(cx):
    cx.compile(FIXTURES / 'GenFix/Lower/ZipIdx.lean')
    out = cx.build / 'lcnf'
    out.mkdir(parents=True, exist_ok=True)
    gen = out / 'zipidx_gen.ml'
    stray = ROOT / 'ocaml/gen/closure-zipidx_gen.tsv'
    cx.tool('src/OCaml5/Tools/LcnfGen.lean', ['--out', str(gen), '--import', 'GenFix.Lower.ZipIdx',
                                              '--cap', '200', 'GenFix.Lower.indexed', 'GenFix.Lower.positionsOfA'])
    if not (out / 'closure-zipidx_gen.tsv').is_file():
        raise CaseFailed('LcnfGen: the closure manifest of a redirected run is not beside its output')
    if stray.exists():
        raise CaseFailed(f'LcnfGen: a redirected run wrote {stray.relative_to(ROOT)} into the tree')
    if '{ to_list' in gen.read_text():
        raise CaseFailed('LcnfGen: `Array.mk l` still renders as a record `{ to_list = l }`')
    for name in ['dune-project', 'dune', 'zipidx_check.ml']:
        shutil.copy(FIXTURES / 'ocaml/zipidx' / name, out / name)
    r = cx.run(['opam', 'exec', '--switch=effect4', '--', 'dune', 'build', '--root', str(out),
                '--build-dir', str(cx.build / 'dune')])
    if r.returncode != 0:
        raise CaseFailed(f'dune build: exit {r.returncode}:\n{(r.stdout + r.stderr)[-3000:]}')
    got = cx.run([str(cx.build / 'dune/default/zipidx_check.exe')]).stdout
    if got != '6\nx 0\n_ 1\n':
        raise CaseFailed(f'the lowered code answers {got!r}; Lean answers 6, [(x, 0), (_, 1)]')


CASES = [
    ('elim-refuses-plain', elim_refuses_plain),
    ('elim-refuses-param', elim_refuses_param),
    ('elim-record', elim_record),
    ('elim-val-agrees', elim_val_agrees),
    ('fold-record', fold_record),
    ('extras-record', extras_record),
    ('extras-record-lengths', extras_record_lengths),
    ('extras-val', extras_val),
    ('extras-refuses-param', extras_refuses_param),
    ('extras-refuses-mutual', extras_refuses_mutual),
    ('extras-refuses-nullary', extras_refuses_nullary),
    ('foldof-record', foldof_record),
    ('view-record', view_record),
    ('view-no-arity', view_no_arity),
    ('view-leaf-one', view_leaf_one),
    ('view-leaf-cyclic', view_leaf_cyclic),
    ('variances-module', variances_module),
    ('wave-view', wave_view),
    ('wave-controls', wave_controls),
    ('lcnf-zipidx', lcnf_zipidx),
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
