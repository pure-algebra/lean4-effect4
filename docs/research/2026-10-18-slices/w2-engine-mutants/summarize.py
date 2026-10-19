#!/usr/bin/env python3
"""C4's campaign, summarized: one row per mutant, from results-A.tsv (the base, with the Ref
instance) and results-B.tsv (the tree without it).

    python3 docs/research/2026-10-18-slices/w2-engine-mutants/summarize.py

For each mutant it prints the tests that failed in each tree.  A failing check of tree A is
"Ref" when it compares with or runs the Ref instance: a `test_diff` divergence of the pairs
`Gen-vs-Ref` or `Ref-vs-Fast`, or a check whose name says `Ref` as a word.  The last column
answers C4's question: is every mutant some Ref check catches in A caught in B?
"""
import csv
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REF_WORD = re.compile(r'\bRef\b(?!\.(make|get|set|update|modify))')
# A test that no carrier reaches: its failures are not the mutant's.  stm_admit runs a toy
# engine, and its parallel test P1 failed under load in tree B (stm_admit-p1.txt).
NOT_REACHED = {'stm_admit'}


def load(label):
    path = HERE / f'results-{label}.tsv'
    if not path.exists():
        return {}
    with path.open() as f:
        rows = list(csv.DictReader(f, delimiter='\t'))
    return {r['id']: r for r in rows}


def checks(row):
    if not row or row['failing checks'] == '-':
        return []
    return [c.strip() for c in row['failing checks'].split(' ;; ')]


def diff_pairs(row):
    """The engine pairs of the divergences test_diff showed, or [] when it showed none."""
    for c in checks(row):
        test, _, text = c.partition(': ')
        if test == 'test_diff' and text.startswith('divergence pairs:'):
            return [p.strip() for p in text.split(':', 1)[1].split(',') if p.strip()]
    return []


def is_ref(row, check):
    """A test_diff failure is Ref's when every pair it showed has Ref in it; any other check is
    Ref's when its name says `Ref` as a word."""
    test, _, text = check.partition(': ')
    if test == 'test_diff' and not text.startswith('FAIL DF-'):
        pairs = diff_pairs(row)
        return bool(pairs) and all('Ref' in p for p in pairs)
    return bool(REF_WORD.search(text))


def tests_of(row, keep):
    """The failing tests one of whose failing checks passes `keep`."""
    found = set()
    for c in checks(row):
        test, _, _ = c.partition(': ')
        if keep(row, c):
            found.add(test)
    return found


def main():
    a, b = load('A'), load('B')
    ids = sorted(set(a) | set(b))
    out = sys.stdout
    out.write('| Mutant | What it breaks | Caught in A by Ref checks | Caught in A by other checks | '
              'Caught in B (no Ref) |\n')
    out.write('| --- | --- | --- | --- | --- |\n')
    ref_missed, any_missed, survivors = [], [], []
    for mid in ids:
        ra, rb = a.get(mid), b.get(mid)
        by_ref = tests_of(ra, is_ref)
        free = tests_of(ra, lambda r, c: not is_ref(r, c))
        caught_a = set((ra['failing tests'] if ra else '-').split(',')) - {'-', ''}
        caught_b = set((rb['failing tests'] if rb else '-').split(',')) - {'-', ''}
        unrelated = (caught_a | caught_b) & NOT_REACHED
        caught_a -= NOT_REACHED
        caught_b -= NOT_REACHED
        if rb is not None:
            if by_ref and not caught_b:
                ref_missed.append(mid)
            if caught_a and not caught_b:
                any_missed.append(mid)
        if ra is not None and not caught_a and (rb is None or not caught_b):
            survivors.append(mid)
        what = WHAT.get(mid, '')
        fmt = lambda s: ', '.join(sorted(s)) if s else '—'
        free -= NOT_REACHED
        note = f' (and {", ".join(sorted(unrelated))}, not reached)' if unrelated else ''
        out.write(f'| {mid} | {what} | {fmt(by_ref)} | {fmt(free)} | '
                  f'{fmt(caught_b) if rb else "(not run)"}{note} |\n')
    out.write(f'\n{len(ids)} mutants.  Caught by a Ref check in A and by nothing in B: '
              f'{", ".join(ref_missed) or "none"}.  Caught in A and by nothing in B: '
              f'{", ".join(any_missed) or "none"}.  Caught by nothing in either tree: '
              f'{", ".join(survivors) or "none"}.\n')


def what_of():
    """Each mutant's one-line description: the first line of its patch."""
    found = {}
    for p in sorted(HERE.glob('*.patch')):
        first = p.read_text().splitlines()[0]
        found[p.stem] = first.split(': ', 1)[1] if ': ' in first else first
    return found


WHAT = what_of()


if __name__ == '__main__':
    main()
