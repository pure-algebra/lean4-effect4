#!/usr/bin/env python3
"""Hand OCaml lines under ocaml/engine at a commit, by part: the installed engine library, its
tests, the disk store and its tests.  Generated files (those `ocaml/.ocamlformat-ignore` lists)
are left out.

    python3 docs/research/2026-10-18-slices/w2-engine-mutants/lines.py REV [REV ...]
"""
import subprocess
import sys


def git(*args):
    return subprocess.run(['git', *args], check=True, stdout=subprocess.PIPE, text=True).stdout


def part(path):
    if path.startswith('ocaml/engine/cas/test/'):
        return 'cas tests'
    if path.startswith('ocaml/engine/cas/'):
        return 'cas library'
    if path.startswith('ocaml/engine/test/'):
        return 'engine tests'
    if path.count('/') == 2:
        return 'engine library'
    return None


def measure(rev):
    ignored = {'ocaml/' + l.strip() for l in git('show', f'{rev}:ocaml/.ocamlformat-ignore')
               .splitlines() if l.strip() and not l.startswith('#')}
    files = [f for f in git('ls-tree', '-r', '--name-only', rev, 'ocaml/engine').splitlines()
             if f.endswith(('.ml', '.mli')) and f not in ignored]
    totals = {}
    for f in files:
        p = part(f)
        if p is None:
            continue
        n = git('show', f'{rev}:{f}').count('\n')
        totals[p] = totals.get(p, 0) + n
    return totals


def main():
    revs = sys.argv[1:] or ['HEAD']
    rows = {r: measure(r) for r in revs}
    parts = ['engine library', 'engine tests', 'cas library', 'cas tests']
    print('| Part | ' + ' | '.join(revs) + ' |')
    print('| --- | ' + ' | '.join('---:' for _ in revs) + ' |')
    for p in parts:
        print(f'| {p} | ' + ' | '.join(str(rows[r].get(p, 0)) for r in revs) + ' |')
    print('| total | ' + ' | '.join(str(sum(rows[r].values())) for r in revs) + ' |')


if __name__ == '__main__':
    main()
