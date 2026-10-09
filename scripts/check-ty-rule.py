#!/usr/bin/env python3
"""The rule for the wave's `Ty` append (decisions row 182; probe U §6.1), as a check a reviewer runs
over the tree's own instruments, which first establishes that it looked.

    python3 scripts/check-ty-rule.py <census.log> [<mirrors.log> ...]
    python3 scripts/check-ty-rule.py --tree [--logs DIR]          run the census over the tree, then check
    python3 scripts/check-ty-rule.py --self-test                  the controls, of the logs and the producers

The rule: no hand case analysis on `Ty` outside the generated folds and
`Laws/Program/Typed/Membership.lean`. The logs are the output of `#traversal_census
Effect4.Program.Ty` and `#exhaustive_gate Effect4.Program.Ty` (`src/Effect4/Laws/Auto/`) over the
whole tree (`import Effect4`, `import Effect4.Laws`; `Test/fixtures/ty-rule/Census.lean`) and, in
the mirror logs, the same two `under OCaml5`, `under Tools`, `under Conform`
(`Test/fixtures/ty-rule/CensusMirrors*.lean`).

Evidence first (decisions row 182 amended; Codex 22:16): a check whose verdict is "no violations"
must show that it read a whole census. Before counting anything it requires
  E1  a log that is not empty and holds no `error:` line (a compiler error is no census);
  E2  in the main log, the census and the gate under `Effect4`, each with its header and the
      instrument's completeness footer (`#traversal_census done: N rows; M modules under S
      scanned`), and exactly N rows between them, so a truncated log is caught;
  E3  every module the rule names among the main census's rows (`EXPECTED_MODULES`): a census run
      over a partial import set misses one of them;
  E4  in the mirror logs, when given, complete sections under each of `OCaml5`, `Tools`, `Conform`.
A log cannot show that its producer finished, or that no producer was left out, so `--tree` also
requires the producers' own evidence (row 182 amended again; Codex 23:16):
  E5  the inventory (`PRODUCERS`), checked before any producer runs: the fixtures in
      `Test/fixtures/ty-rule` are exactly the listed ones (listed, not globbed: a listed fixture
      missing, or a fixture the list does not name, refuses), each importing exactly its modules;
  E6  every producer exits 0: a nonzero exit (even after a complete report), a signal, or a
      producer that cannot start refuses, naming its fixture, its command and its status; each
      producer writes its own log in the logs directory, and every log is kept;
  E7  each producer's own log holds exactly the two sections its fixture asks for, the census and
      the gate of `Effect4.Program.Ty` under its scope, each complete (E1, E2): a silent or partial
      mirror is not covered by the other mirrors under the same scope.
Missing evidence exits 2 with a named message, never 0. The number of rows is not the contract
(removing hand traversals is the point of the rule); completeness is.

Then the rule, as probe U wrote it (`U/scripts/check-commit4-rule.py`):
  R1  no `structural` or `wf` census row: a recursive traversal is a `fold` or `generated`;
  R2  a `one-level` row only in a generated module or in Membership.lean;
  R3  a gate row (a compiled `match` reading `Ty`) only in a generated module or in Membership.lean;
  R4  no `structural` row in the mirror modules.
Exempt by name: the derived `Repr` (until the generator emits it for the nested `Ty`), and two
pass-through matchers whose `Ty` discriminant is a variable in every arm (`selectRefusal.match_1`,
`Decision.arms.match_4`). Exit 1 when a violation is found; on today's tree this is the baseline,
the distance from the rule (78 rows at probe U's base `630e6c37`). The gate turns on with the
append (seat W4); it is not wired into `make check`.
"""
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile

from lib.lean_imports import imports_of as lean_imports_of
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'Test/fixtures/ty-rule'

GENERATED_MODULES = {
    'Effect4.Program.Fold', 'Effect4.Laws.Program.TyView', 'Effect4.Store.Domain.Derived.Program',
    # the modules the wave adds (the generators' output)
    'Effect4.Program.TyEq', 'Effect4.Program.TyFoldExtras', 'Effect4.Program.TyTables',
}
ALLOWED_MODULES = {'Effect4.Laws.Program.Typed.Membership'}
EXEMPT = {'Effect4.Program.instReprTy.repr'}
PASS_THROUGH = {'Effect4.Program.selectRefusal.match_1', 'Effect4.Program.Decision.arms.match_4'}
# A whole-tree census always reads these: the declaration's own module, the generated fold and view,
# and the one module the rule allows. A census over a partial import set misses one of them.
EXPECTED_MODULES = ['Effect4.Program.Ty', 'Effect4.Program.Fold', 'Effect4.Laws.Program.TyView',
                    'Effect4.Laws.Program.Typed.Membership']
MIRROR_SCOPES = ['OCaml5', 'Tools', 'Conform']

# The producers `--tree` runs, in this order, one Lean process at a time (E5): each a fixture in
# FIXTURES, the modules it imports (exactly), and the scope its census and gate report under. The
# first is the census over the whole tree, the rest the mirrors. A mirror is added here and as its
# fixture together; a fixture this list does not name refuses rather than going unrun.
CENSUS_ROOT = 'Effect4.Program.Ty'
INSTRUMENTS = ['Effect4.Laws.Auto.Traversals', 'Effect4.Laws.Auto.Exhaustive']
PRODUCERS = [
    ('Census.lean', ['Effect4', 'Effect4.Laws', *INSTRUMENTS], 'Effect4'),
    ('CensusMirrorsConformLcnfMl.lean', ['Effect4', *INSTRUMENTS, 'Conform.Effect4.LcnfMl'], 'Conform'),
    ('CensusMirrorsConformLcnfSemantics.lean', ['Effect4', *INSTRUMENTS, 'Conform.Effect4.LcnfSemantics'],
     'Conform'),
    ('CensusMirrorsOCaml5.lean',
     ['Effect4', *INSTRUMENTS, 'OCaml5.Eff.Goldens', 'OCaml5.Eff.Emit', 'OCaml5.Eff.Metadata'], 'OCaml5'),
    ('CensusMirrorsToolsProfileJson.lean', ['Effect4', *INSTRUMENTS, 'Tools.ProfileJson'], 'Tools'),
    ('CensusMirrorsToolsRowTypes.lean', ['Effect4', *INSTRUMENTS, 'Tools.RowTypes'], 'Tools'),
    ('CensusMirrorsToolsTyVectors.lean', ['Effect4', *INSTRUMENTS, 'Tools.TyVectors'], 'Tools'),
    ('CensusMirrorsToolsVariances.lean', ['Effect4', *INSTRUMENTS, 'Tools.Variances'], 'Tools'),
]
LAKE = ['lake', 'env', 'lean', '-DwarningAsError=true', '-M6144']

HEADER = re.compile(r'^(#traversal_census|#exhaustive_gate) (\S+) \(family [^)]*\) under (\S+):')
FOOTER = re.compile(r'^(#traversal_census|#exhaustive_gate) done: (\d+) rows; (\d+) modules under (\S+) scanned$')


class MissingEvidence(Exception):
    """The log does not show a whole census: exit 2, with the message."""


def sections(path):
    """The census and gate sections of a log, each complete (header, rows, footer) or refused."""
    text = Path(path).read_text(encoding='utf-8', errors='replace')
    if not text.strip():
        raise MissingEvidence(f'{path}: the log is empty; no census was read')
    for n, line in enumerate(text.splitlines(), 1):
        if 'error:' in line:
            raise MissingEvidence(f'{path}:{n}: the log holds a compiler error ({line.strip()[:120]}); '
                                  'a failed run is no census')
    out, cur = [], None
    for n, line in enumerate(text.splitlines(), 1):
        m = HEADER.match(line)
        if m:
            if cur is not None:
                raise MissingEvidence(f'{path}:{n}: a {cur["kind"]} section under {cur["scope"]} has no '
                                      'completeness footer before the next section (a truncated census)')
            cur = {'kind': m.group(1), 'root': m.group(2), 'scope': m.group(3), 'rows': []}
            continue
        f = FOOTER.match(line)
        if f:
            if cur is None or f.group(1) != cur['kind'] or f.group(4) != cur['scope']:
                raise MissingEvidence(f'{path}:{n}: a footer with no section of its own')
            if int(f.group(2)) != len(cur['rows']):
                raise MissingEvidence(f'{path}:{n}: the {cur["kind"]} footer counts {f.group(2)} rows but '
                                      f'{len(cur["rows"])} were read (a truncated census)')
            cur['modules'] = int(f.group(3))
            out.append(cur)
            cur = None
            continue
        if cur is not None and line.startswith('  '):
            cur['rows'].append(line.strip().split('\t'))
    if cur is not None:
        raise MissingEvidence(f'{path}: the {cur["kind"]} section under {cur["scope"]} has no completeness '
                              'footer (a truncated census)')
    return out


def census_rows(sec):
    rows = []
    for p in sec['rows']:
        cls, loc, name = p[0], p[1], p[2].split(' [')[0]
        rows.append((cls, loc.rsplit(':', 1)[0], name))
    return rows


def gate_rows(sec):
    return [(p[0].split(' [')[0], p[1], p[2], p[5] if len(p) > 5 else '') for p in sec['rows']]


def check(main_log, mirror_logs):
    secs = sections(main_log)
    census = [s for s in secs if s['kind'] == '#traversal_census' and s['scope'] == 'Effect4']
    gate = [s for s in secs if s['kind'] == '#exhaustive_gate' and s['scope'] == 'Effect4']
    if not census or not gate:
        missing = ' and '.join(k for k, v in (('#traversal_census', census), ('#exhaustive_gate', gate)) if not v)
        raise MissingEvidence(f'{main_log}: no complete {missing} section under Effect4')
    crows = [r for s in census for r in census_rows(s)]
    grows = [r for s in gate for r in gate_rows(s)]
    present = {mod for _, mod, _ in crows}
    absent = [m for m in EXPECTED_MODULES if m not in present]
    if absent:
        raise MissingEvidence(f'{main_log}: the census reads no row of {absent}; it was not run over the '
                              'whole tree (import Effect4 and Effect4.Laws)')
    mirror = []
    if mirror_logs:
        scopes = set()
        for path in mirror_logs:
            for s in sections(path):
                scopes.add(s['scope'])
                if s['kind'] == '#traversal_census':
                    mirror += census_rows(s)
        lacking = [s for s in MIRROR_SCOPES if s not in scopes]
        if lacking:
            raise MissingEvidence(f'the mirror logs hold no complete section under {lacking}')
    v = []
    for cls, mod, name in crows:
        if name in EXEMPT or mod in ALLOWED_MODULES:
            continue
        if cls in ('structural', 'wf'):
            v.append(f'R1 {cls:10} {name} ({mod})')
        if cls == 'one-level' and mod not in GENERATED_MODULES:
            v.append(f'R2 one-level  {name} ({mod})')
    for name, mod, matcher, ca in grows:
        if (name.endswith('.hom') or name in EXEMPT or matcher in PASS_THROUGH or mod in ALLOWED_MODULES
                or mod in GENERATED_MODULES):
            continue
        v.append(f'R3 {ca:14} {name} ({mod}, {matcher})')
    seen = set()
    for cls, mod, name in mirror:
        if cls == 'structural' and name not in seen:
            seen.add(name)
            v.append(f'R4 structural {name} ({mod})')
    for x in v:
        print(x)
    rules = {}
    for x in v:
        rules[x[:2]] = rules.get(x[:2], 0) + 1
    print(f'evidence: {len(crows)} census rows and {len(grows)} gate rows under Effect4'
          + (f', {len(mirror)} mirror census rows over {len(mirror_logs)} log(s)' if mirror_logs else ''))
    print(f'{len(v)} violation(s)' + (': ' + ', '.join(f'{k} {rules[k]}' for k in sorted(rules)) if v else ''))
    return 1 if v else 0


def refusing(thunk):
    """Missing evidence, or a log that cannot be read or written, exits 2 with its message."""
    try:
        return thunk()
    except (MissingEvidence, OSError) as e:
        print(f'check-ty-rule: REFUSE (missing evidence): {e}')
        return 2


def run(argv):
    return refusing(lambda: check(argv[0], argv[1:]))


def imports_of(path):
    """The modules a fixture imports, in order (`scripts/lib/lean_imports.py`)."""
    return lean_imports_of(path)


def inventory(fixtures):
    """E5: the fixtures in `fixtures` are exactly the producers' (`PRODUCERS`), each importing
    exactly its listed modules. Every difference is named; any one refuses before a producer runs."""
    listed = [fixture for fixture, _, _ in PRODUCERS]
    present = sorted(p.name for p in fixtures.glob('*.lean'))
    problems = [f"{fixtures / f}: a listed producer's fixture is missing" for f in listed if f not in present]
    problems += [f'{fixtures / f}: a fixture the inventory does not list (add it to PRODUCERS with its '
                 'modules and scope, or remove it)' for f in present if f not in listed]
    for fixture, modules, _ in PRODUCERS:
        if fixture in present:
            found = imports_of(fixtures / fixture)
            if sorted(found) != sorted(modules):
                problems.append(f'{fixtures / fixture}: imports {found}; the inventory lists {modules}')
    if problems:
        raise MissingEvidence(f'the fixtures in {fixtures} are not the producer inventory (PRODUCERS); no '
                              'producer was run\n' + '\n'.join('  ' + p for p in problems))


def produce(src, log, env):
    """One producer: its stdout and stderr, in order, into its own log (kept); its exit status, or
    why it could not start."""
    cmd = [*LAKE, str(src)]
    with open(log, 'wb') as out:
        try:
            return cmd, subprocess.run(cmd, cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT).returncode
        except OSError as e:
            return cmd, f'could not start ({e})'


def status_text(status):
    """A producer's status as a report names it: its exit status, its signal, or why it did not start."""
    if isinstance(status, str):
        return status
    return f'killed by signal {-status}' if status < 0 else f'exit status {status}'


def kept(log):
    """A kept log, as a refusal names it: its path, its size and its last line."""
    lines = [l.strip() for l in Path(log).read_text(encoding='utf-8', errors='replace').splitlines() if l.strip()]
    return (f'{log} ({Path(log).stat().st_size} bytes'
            + (f'; its last line: {lines[-1][:120]})' if lines else ', empty)'))


def two_sections(log, scope):
    """E7: None when the log holds exactly the census and the gate of CENSUS_ROOT under `scope`,
    each complete (E1, E2); else what it holds instead."""
    try:
        held = sorted((s['kind'], s['root'], s['scope']) for s in sections(log))
    except MissingEvidence as e:
        return str(e)
    if held == sorted((kind, CENSUS_ROOT, scope) for kind in ('#traversal_census', '#exhaustive_gate')):
        return None
    what = ', '.join(f'{k} {r} under {s}' for k, r, s in held) or 'no section'
    return f'its log holds {what}, not exactly the census and the gate of {CENSUS_ROOT} under {scope} ({log})'


def tree(logs):
    """The census over the whole tree and the mirror censuses (`PRODUCERS`): the inventory first
    (E5), then each producer, one Lean process at a time, into its own log in `logs` (kept), every
    exit status required (E6) and every log's two sections (E7), then the check: on today's tree,
    the distance from the rule."""
    inventory(FIXTURES)
    logs.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    print(f"check-ty-rule: the tree's census, {len(PRODUCERS)} producers one at a time, each into its own "
          f'log in {logs}', flush=True)
    ran, failed = [], []
    for fixture, _, scope in PRODUCERS:
        log = logs / (Path(fixture).stem + '.log')
        cmd, status = produce(FIXTURES / fixture, log, env)
        print(f'  {fixture}: {status_text(status)}, {log.stat().st_size} bytes in {log}', flush=True)
        ran.append((fixture, scope, log))
        if status != 0:
            failed.append(f'{fixture}: {status_text(status)}, from `{shlex.join(cmd)}`; its log is kept: '
                          f'{kept(log)}')
    if failed:
        raise MissingEvidence(f'{len(failed)} of {len(PRODUCERS)} producers failed; a failed run is no census, '
                              'even after a complete report\n' + '\n'.join('  ' + f for f in failed))
    partial = [f'{fixture}: {problem}' for fixture, scope, log in ran
               for problem in [two_sections(log, scope)] if problem]
    if partial:
        raise MissingEvidence(f'{len(partial)} of {len(PRODUCERS)} producers exited 0 without the two sections '
                              'their fixtures ask for\n' + '\n'.join('  ' + p for p in partial))
    print(f'check-ty-rule: {len(PRODUCERS)} of {len(PRODUCERS)} producers exited 0, each log holding its two '
          'complete sections')
    main_log, *mirror_logs = [str(log) for _, _, log in ran]
    return check(main_log, mirror_logs)


# The producer the self-test puts on PATH as `lake` (Codex's fake of 23:16, with four more faults).
# It reads the fixture from its last argument and prints what the instruments print: the green log
# for the main census, one `fold` row under its scope for a mirror. TY_RULE_FAULT names the fault.
FAKE_LAKE = r'''
import os, signal, sys
from pathlib import Path
src, fault = Path(sys.argv[-1]), os.environ.get('TY_RULE_FAULT', '')
if src.name == 'Census.lean':
    sys.stdout.write((src.parent / 'census-green.log').read_text())
    sys.exit(7 if fault == 'main-fails-after-output' else 0)
hit = src.name == 'CensusMirrorsToolsVariances.lean'
if hit and fault == 'mirror-fails-silently':
    sys.exit(7)
if hit and fault == 'mirror-succeeds-silently':
    sys.exit(0)
if hit and fault == 'mirror-killed':
    os.kill(os.getpid(), signal.SIGTERM)
scope = 'OCaml5' if 'OCaml5' in src.name else 'Tools' if 'Tools' in src.name else 'Conform'
if hit and fault == 'mirror-under-another-scope':
    scope = 'Conform'
print(f'#traversal_census Effect4.Program.Ty (family [Effect4.Program.Ty]) under {scope}: synthetic producer')
print(f'  fold\t{scope}.Probe:1\t{scope}.Probe.good\t(Ty)\t{scope}.Probe.alg')
print(f'#traversal_census done: 1 rows; 1 modules under {scope} scanned')
if not (hit and fault == 'mirror-census-only'):
    print(f'#exhaustive_gate Effect4.Program.Ty (family [Effect4.Program.Ty]) under {scope}: synthetic producer')
    print(f'#exhaustive_gate done: 0 rows; 1 modules under {scope} scanned')
'''


def tree_control(base, name, fault, mutate):
    """`--tree`, run by a copy of this script over a copy of the fixtures in a scratch tree, with PATH
    holding only the fake `lake` set to `fault` (an empty directory when `fault` is None, so no
    producer can start, and never the real `lake`); `mutate` changes the copied fixtures first."""
    root = base / re.sub(r'[^A-Za-z0-9]+', '-', name).strip('-')
    fixtures = root / FIXTURES.relative_to(ROOT)
    shutil.copytree(FIXTURES, fixtures)
    script = root / 'scripts' / Path(__file__).name
    script.parent.mkdir()
    shutil.copyfile(Path(__file__).resolve(), script)
    bin_dir = root / 'bin'
    bin_dir.mkdir()
    if fault is not None:
        (bin_dir / 'fake-lake.py').write_text(FAKE_LAKE)
        lake = bin_dir / 'lake'
        lake.write_text(f'#!/bin/sh\nexec {shlex.quote(sys.executable)} '
                        f'{shlex.quote(str(bin_dir / "fake-lake.py"))} "$@"\n')
        lake.chmod(0o755)
    if mutate is not None:
        mutate(fixtures)
    env = dict(os.environ, PATH=str(bin_dir), TY_RULE_FAULT=fault or '')
    return subprocess.run([sys.executable, str(script), '--tree', '--logs', str(root / 'logs')],
                          cwd=root, env=env, capture_output=True, text=True)


def self_test():
    """The controls, each with the exit it must give and the message that exit must carry (for a
    refusal, in the refusal's own text). Of the logs: the green fixture (0), a deliberate violation
    (1), Codex's three missing-evidence logs: empty, a compiler error only, truncated before the gate
    (2 each), and two more (2 each). Of the producers, `--tree` over a scratch copy of the tree with
    a fake `lake`: the green run (0), Codex's three of 23:16, which exited 0 before E5-E6 (the census
    failing after its complete report, a mirror failing silently, a mirror fixture missing), and one
    for each other refusal of E5-E7, a producer killed by a signal among them (2 each)."""
    green = (FIXTURES / 'census-green.log').read_text()
    logs = [
        ('green', green, 0, '0 violation(s)'),
        ('deliberate violation', green.replace('  fold\t', '  structural\t', 1), 1, '1 violation(s): R1 1'),
        ('empty log', '', 2, 'the log is empty'),
        ('compiler error only', 'error: unknown module prefix Effect4\n', 2, 'the log holds a compiler error'),
        ('truncated before the gate', green.split('#exhaustive_gate', 1)[0], 2,
         'no complete #exhaustive_gate section under Effect4'),
        # two more: a census cut inside its rows (its footer lost), and a census run over the core
        # alone, whose rows miss the Laws modules the rule names
        ('rows cut inside the census', green.split('  delegates', 1)[0], 2, 'has no completeness footer'),
        ('a census over a partial import set',
         '\n'.join(l for l in green.splitlines() if 'Effect4.Laws.' not in l)
         .replace('done: 7 rows', 'done: 4 rows').replace('done: 3 rows', 'done: 1 rows') + '\n', 2,
         'the census reads no row of'),
    ]
    v = 'CensusMirrorsToolsVariances'

    def drop(fx):
        (fx / f'{v}.lean').unlink()

    def unlisted(fx):
        (fx / 'CensusMirrorsToolsExtra.lean').write_text((fx / f'{v}.lean').read_text())

    def unimported(fx):
        src = fx / f'{v}.lean'
        src.write_text(''.join(l for l in src.read_text().splitlines(True) if l.strip() != 'import Tools.Variances'))

    trees = [
        ('tree green', '', None, 0, '0 violation(s)'),
        # Codex's three (23:16)
        ('tree, the census fails after its complete report', 'main-fails-after-output', None, 2,
         'Census.lean: exit status 7, from `lake env lean'),
        ('tree, a mirror fails silently', 'mirror-fails-silently', None, 2,
         f'{v}.lean: exit status 7, from `lake env lean'),
        ('tree, a mirror fixture missing', '', drop, 2, f"{v}.lean: a listed producer's fixture is missing"),
        # one for each other refusal of E5-E7
        ('tree, a fixture the inventory does not list', '', unlisted, 2,
         'CensusMirrorsToolsExtra.lean: a fixture the inventory does not list'),
        ('tree, a mirror fixture without its module', '', unimported, 2, f'{v}.lean: imports ['),
        ('tree, no producer can start', None, None, 2, 'Census.lean: could not start'),
        ('tree, a mirror killed by a signal', 'mirror-killed', None, 2,
         f'{v}.lean: killed by signal 15, from `lake env lean'),
        ('tree, a mirror succeeds silently', 'mirror-succeeds-silently', None, 2, f'{v}.log: the log is empty'),
        ('tree, a mirror under another scope', 'mirror-under-another-scope', None, 2,
         f'{v}.lean: its log holds #exhaustive_gate Effect4.Program.Ty under Conform'),
        ('tree, a mirror census without its gate', 'mirror-census-only', None, 2,
         f'{v}.lean: its log holds #traversal_census Effect4.Program.Ty under Tools, not'),
    ]
    failures = 0
    with tempfile.TemporaryDirectory() as d:
        runs = []
        for name, text, want, reason in logs:
            path = Path(d) / (name.replace(' ', '-') + '.log')
            path.write_text(text)
            runs.append((name, want, reason, lambda path=path: subprocess.run(
                [sys.executable, str(Path(__file__).resolve()), str(path)], capture_output=True, text=True)))
        for name, fault, mutate, want, reason in trees:
            runs.append((name, want, reason,
                         lambda name=name, fault=fault, mutate=mutate: tree_control(Path(d), name, fault, mutate)))
        for name, want, reason, go in runs:
            r = go()
            # a refusal's reason is read in the refusal itself, never in the progress lines before it
            said = r.stdout.partition('REFUSE (missing evidence): ')[2] if want == 2 else r.stdout
            ok = r.returncode == want and reason in said
            if not ok:
                failures += 1
            verdict = 'ok' if ok else ('WRONG' if r.returncode != want else f'WRONG: no "{reason}" in its output')
            last = (r.stdout.strip().splitlines() or ['(no output)'])[-1]
            print(f'--- control {name}: exit {r.returncode}, expected {want} ({verdict}): {last}')
            if not ok and r.stderr.strip():
                print('    stderr: ' + r.stderr.strip().splitlines()[-1])
        total = len(runs)
    print(f'self-test: {total - failures} of {total} controls as expected')
    return 0 if failures == 0 else 1


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    if argv[:1] == ['--tree']:
        rest = argv[1:]
        logs = Path(rest[1]) if rest[:1] == ['--logs'] and len(rest) == 2 else Path(tempfile.mkdtemp(prefix='ty-rule-'))
        return refusing(lambda: tree(logs))
    if not argv or argv[0].startswith('-'):
        print(__doc__)
        return 2
    return run(argv)


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
