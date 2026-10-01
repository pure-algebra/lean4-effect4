#!/usr/bin/env python3
"""The rule for the wave's `Ty` append (decisions row 182; probe U §6.1), as a check a reviewer runs
over the tree's own instruments, which first establishes that it looked.

    python3 scripts/check-ty-rule.py <census.log> [<mirrors.log> ...]
    python3 scripts/check-ty-rule.py --tree [--logs DIR]          run the census over the tree, then check
    python3 scripts/check-ty-rule.py --self-test                  the seven controls

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
import re
import subprocess
import sys
import tempfile
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


def run(argv):
    try:
        return check(argv[0], argv[1:])
    except MissingEvidence as e:
        print(f'check-ty-rule: REFUSE (missing evidence): {e}')
        return 2
    except OSError as e:
        print(f'check-ty-rule: REFUSE (missing evidence): {e}')
        return 2


def self_test():
    """The controls: the green fixture (0), a deliberate violation (1), Codex's three missing-evidence
    logs: empty, a compiler error only, truncated before the gate (2 each), and two more (2 each)."""
    green = (FIXTURES / 'census-green.log').read_text()
    cases = [
        ('green', green, 0),
        ('deliberate violation', green.replace('  fold\t', '  structural\t', 1), 1),
        ('empty log', '', 2),
        ('compiler error only', 'error: unknown module prefix Effect4\n', 2),
        ('truncated before the gate', green.split('#exhaustive_gate', 1)[0], 2),
        # two more: a census cut inside its rows (its footer lost), and a census run over the core
        # alone, whose rows miss the Laws modules the rule names
        ('rows cut inside the census', green.split('  delegates', 1)[0], 2),
        ('a census over a partial import set',
         '\n'.join(l for l in green.splitlines() if 'Effect4.Laws.' not in l)
         .replace('done: 7 rows', 'done: 4 rows').replace('done: 3 rows', 'done: 1 rows') + '\n', 2),
    ]
    failures = 0
    with tempfile.TemporaryDirectory() as d:
        for name, text, want in cases:
            path = Path(d) / (name.replace(' ', '-') + '.log')
            path.write_text(text)
            r = subprocess.run([sys.executable, str(Path(__file__).resolve()), str(path)],
                               capture_output=True, text=True)
            ok = r.returncode == want
            if not ok:
                failures += 1
            last = (r.stdout.strip().splitlines() or ['(no output)'])[-1]
            print(f'--- control {name}: exit {r.returncode}, expected {want} ({"ok" if ok else "WRONG"}): {last}')
    print(f'self-test: {len(cases) - failures} of {len(cases)} controls as expected')
    return 0 if failures == 0 else 1


def tree(logs):
    """The census over the whole tree (`Test/fixtures/ty-rule/Census.lean`) and the mirror censuses
    (`CensusMirrors*.lean`), one Lean process at a time, written to `logs`, then checked: on today's
    tree, the distance from the rule."""
    import os
    logs.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    def lean(src, out, mode):
        r = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', '-M6144', str(src)],
                           cwd=ROOT, env=env, capture_output=True, text=True)
        with open(out, mode) as f:
            f.write(r.stdout + r.stderr)
    main_log = logs / 'census.log'
    lean(FIXTURES / 'Census.lean', main_log, 'w')
    mirrors_log = logs / 'census-mirrors.log'
    mirrors_log.write_text('')
    for src in sorted(FIXTURES.glob('CensusMirrors*.lean')):
        lean(src, mirrors_log, 'a')
    print(f'check-ty-rule: the tree\'s census in {main_log} and {mirrors_log}')
    return run([str(main_log), str(mirrors_log)])


def main(argv):
    if argv == ['--self-test']:
        return self_test()
    if argv[:1] == ['--tree']:
        rest = argv[1:]
        logs = Path(rest[1]) if rest[:1] == ['--logs'] and len(rest) == 2 else Path(tempfile.mkdtemp(prefix='ty-rule-'))
        return tree(logs)
    if not argv or argv[0].startswith('-'):
        print(__doc__)
        return 2
    return run(argv)


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
