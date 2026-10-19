#!/usr/bin/env python3
"""C4's mutant campaign: apply one carrier mutant, run the engine's whole test alias, record
which tests and which named checks fail, revert.  One row per mutant.

Run from anywhere; the worktree root is two levels above this folder's parent:

    python3 docs/research/2026-10-18-slices/w2-engine-mutants/campaign.py \
        --label A --corpus /abs/.lake/corpus [--root TREE] [MUTANT ...]

`--label` names the tree the run measures (A: the base, with the Ref instance; B: the tree
without it).  `--root` is the tree the patches apply to, a checkout or a copy holding
`ocaml/` (and `harness/truth/corpus.json`); it defaults to this repository's root, and a copy
keeps the run apart from work in the checkout.  The rows go to `results-<label>.tsv` beside
this file, the full log of each mutant to `logs-<label>/<id>.log`.  Each mutant is a patch in
this folder (`<id>.patch`); the tree must be clean in `ocaml/engine/` before the run, and each
patch is reverted before the next is applied, so a crash leaves at most one patch applied
(`git apply -R` it by hand).

Columns: id, the file it mutates, the build verdict, the failing tests (dune's own test names),
and the failing checks: each `FAIL …` line of a failing test, and for `test_diff` the engine
pairs of the divergences it shows (`pair=…`), read off dune's output.  A test that fails
without a `FAIL` line says so; a test still running when the alias stops at TIMEOUT seconds
is listed as giving no verdict.  After each run the runner compares dune's copies of the
carriers in _build with their sources; a run that measured a stale copy is marked INVALID and
the build is cleaned before the next mutant.
"""
import argparse
import os
import re
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SWITCH = ['opam', 'exec', '--switch=effect4', '--']

TIMEOUT = 600  # seconds; the whole alias takes about 15 s on an idle host
HEADER = re.compile(r'^File "(?P<dune>[^"]+/dune)", line (?P<line>\d+), characters')
NAME = re.compile(r'\(names? (?P<name>[a-z0-9_]+)')
# The compiler's refusal of a source file: its location, then within a few lines `Error`.
COMPILE_ERROR = re.compile(r'^File "[^"]+\.mli?", line \d+[^\n]*\n(?:[^\n]*\n){0,8}?Error', re.M)


def descendants(pid):
    """Every process below `pid`, with its command line.  Dune starts each action in a session
    of its own, so a process group does not reach the tests; the parent links do."""
    table = subprocess.run(['ps', '-A', '-o', 'pid=,ppid=,command='], stdout=subprocess.PIPE,
                           text=True).stdout
    children, commands = {}, {}
    for line in table.splitlines():
        parts = line.split(None, 2)
        if len(parts) < 2:
            continue
        children.setdefault(int(parts[1]), []).append(int(parts[0]))
        commands[int(parts[0])] = parts[2] if len(parts) > 2 else ''
    found, stack = [], [pid]
    while stack:
        for c in children.get(stack.pop(), []):
            found.append((c, commands.get(c, '')))
            stack.append(c)
    return found


def run(command, cwd, env, timeout):
    """Run, and past the timeout name the test executables still running below it, kill those
    processes and everything below them, and answer ('timeout', the output so far, seconds),
    the output closed by one line `HUNG: <names>`.

    Dune itself is not killed: it sees its actions fail and exits, saving its build state.  A
    dune killed in the middle of a build does not save it, and its next build can then keep a
    stale copy of a source in _build (measured on 2026-10-18: a reverted mutant's text stayed
    in _build/default/engine/e4_ppath.ml).  Only a dune that does not exit within a further
    minute is killed."""
    started = time.time()
    child = subprocess.Popen(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, start_new_session=True)
    try:
        out, _ = child.communicate(timeout=timeout)
        return child.returncode, out, time.time() - started
    except subprocess.TimeoutExpired:
        hung = set()
        while True:
            below = [(p, c) for p, c in descendants(child.pid)
                     if re.search(r'\.exe|check_install', c)]
            if not below:
                break
            hung |= {m for _, c in below for m in re.findall(r'\./([a-z0-9_]+)\.exe', c)}
            for p, _ in below:
                try:
                    os.kill(p, 9)
                except ProcessLookupError:
                    pass
            time.sleep(1)
        try:
            out, _ = child.communicate(timeout=60)
        except subprocess.TimeoutExpired:
            child.kill()
            out, _ = child.communicate()
            out = (out or '') + '\nDUNE KILLED: the build state may be stale\n'
        return 'timeout', (out or '') + '\nHUNG: ' + ' '.join(sorted(hung)) + '\n', \
            time.time() - started


def build_copies_match(root, patch_target):
    """Dune's copies of the seven carriers in _build equal their sources, the patched one
    included: the run measured the mutant and nothing else."""
    engine = root / 'ocaml/engine'
    copies = root / 'ocaml/_build/default/engine'
    for source in sorted(engine.glob('e4_*.ml')):
        copy = copies / source.name
        if copy.exists() and copy.read_bytes() != source.read_bytes():
            return False, source.name
    return True, ''


def failing_actions(output):
    """Each failed dune action: its dune file's directory and the test name its stanza shows."""
    lines = output.splitlines()
    found = []
    for i, line in enumerate(lines):
        m = HEADER.match(line)
        if not m:
            continue
        directory = str(Path(m.group('dune')).parent)
        excerpt = lines[i + 1] if i + 1 < len(lines) else ''
        n = NAME.search(excerpt)
        found.append((directory, n.group('name') if n else 'rule@' + m.group('line')))
    return found


def checks_by_action(output):
    """Each failed action's FAIL lines, and test_diff's divergence pairs, read off dune's own
    output.  Dune prints an action's whole output at once, a failed one under its `File …`
    header, and a passing test prints no FAIL line (the base's whole run holds none), so every
    FAIL line belongs to the last header above it."""
    lines = output.splitlines()
    found = {}
    current = None
    for i, line in enumerate(lines):
        m = HEADER.match(line)
        if m:
            directory = str(Path(m.group('dune')).parent)
            excerpt = lines[i + 1] if i + 1 < len(lines) else ''
            n = NAME.search(excerpt)
            current = (directory, n.group('name') if n else 'rule@' + m.group('line'))
            found.setdefault(current, [])
            continue
        if current is None:
            continue
        if line.lstrip().startswith('FAIL'):
            found[current].append(line.strip())
        for pair in re.findall(r'pair=([A-Za-z-]+)', line):
            tag = 'divergence pairs: ' + pair
            if tag not in found[current]:
                found[current].append(tag)
    result = {}
    for key, rows in found.items():
        fails = [r for r in rows if r.startswith('FAIL')]
        pairs = sorted(r.split(': ', 1)[1] for r in rows if r.startswith('divergence pairs: '))
        if pairs:
            fails.append('divergence pairs: ' + ','.join(pairs))
        result[key] = fails or ['failed with no FAIL line (an exception or an exit code)']
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--label', required=True)
    parser.add_argument('--corpus', required=True, help='the printed Lean corpus (E4_LEAN_CORPUS)')
    parser.add_argument('--root', default=str(ROOT), help='the tree the patches apply to')
    parser.add_argument('mutants', nargs='*')
    args = parser.parse_args()
    patches = sorted(HERE.glob('*.patch'))
    if args.mutants:
        patches = [HERE / (m + '.patch') for m in args.mutants]
    root = Path(args.root).resolve()
    ocaml = root / 'ocaml'
    env = dict(os.environ, E4_LEAN_CORPUS=str((ROOT / args.corpus).resolve()))
    logs = HERE / f'logs-{args.label}'
    logs.mkdir(exist_ok=True)
    out = HERE / f'results-{args.label}.tsv'
    write_header = not out.exists()
    with out.open('a') as table:
        if write_header:
            table.write('id\tfile\tbuild\tseconds\tfailing tests\tfailing checks\n')
        for patch in patches:
            mid = patch.stem
            target = re.search(r'^\+\+\+ b/(\S+)', patch.read_text(), re.M).group(1)
            subprocess.run(['git', 'apply', str(patch)], cwd=root, check=True)
            try:
                code, output, seconds = run(
                    SWITCH + ['dune', 'build', '@engine/runtest', '--force'], ocaml, env, TIMEOUT)
                (logs / f'{mid}.log').write_text(output)
                # A hung test is named; it is not rerun, since a rerun would hang as well.
                hung = (re.findall(r'^HUNG: (.*)$', output, re.M) or [''])[0].split()
                actions = failing_actions(output)
                fresh, stale = build_copies_match(root, target)
                if not fresh:
                    # The run measured another text than the mutant: the row says so, and the
                    # next mutant starts from a clean build.
                    verdict = f'INVALID: _build holds a stale {stale}'
                    tests, checks = '', ''
                    subprocess.run(SWITCH + ['dune', 'clean'], cwd=ocaml, env=env)
                elif COMPILE_ERROR.search(output) and not actions and not hung:
                    verdict, tests, checks = 'does not build', '', ''
                else:
                    verdict = 'builds' + (f'; alias stopped at {TIMEOUT} s' if hung else '')
                    tests = ','.join(sorted({n for _, n in actions} | set(hung)))
                    rows = [f'{h}: no verdict within {TIMEOUT} s' for h in hung]
                    for (directory, name), fails in sorted(checks_by_action(output).items()):
                        for c in fails:
                            rows.append(f'{name}: {c}')
                    checks = ' ;; '.join(rows)
            finally:
                subprocess.run(['git', 'apply', '-R', str(patch)], cwd=root, check=True)
            if 'DUNE KILLED' in output:
                # This run built before its tests ran, so it measured the mutant; the build
                # state dune did not save could mislead the next one.
                subprocess.run(SWITCH + ['dune', 'clean'], cwd=ocaml, env=env)
            if code == 0 and tests:
                verdict += ' (dune exit 0?)'
            table.write(f'{mid}\t{Path(target).name}\t{verdict}\t{seconds:.0f}\t'
                        f'{tests or "-"}\t{checks or "-"}\n')
            table.flush()
            print(f'{mid}: {verdict}; failing: {tests or "none"}', flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
