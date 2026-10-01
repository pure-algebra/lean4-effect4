#!/usr/bin/env python3
"""Seat S: count the lines each `-- [arm:<form>]` / `-- [change:<what>]` marker covers in K2Copy.lean.

Rule: a marker covers the code lines after it. If its first code line opens a declaration
(`def`, `theorem`, `abbrev`, `structure`), it covers that declaration up to the next blank line,
marker or top-level line. Otherwise (an arm inside a definition) it covers lines up to the next
blank line, marker, top-level line, or a sibling arm (`|` at the marker's indentation or less).
Comment and docstring lines are not counted. A floor per form: the per-file diffs in S/patches/
are the totals."""
import re, sys, collections
path = sys.argv[1] if len(sys.argv) > 1 else 'K2Copy.lean'
lines = open(path).read().split('\n')
counts = collections.Counter()
top = re.compile(r'^(def|theorem|end|mutual|abbrev|structure|inductive|instance|#|/-)')
opener = re.compile(r'^(def|theorem|abbrev|structure)\b')
cur = None; ind = 0; mode = None; seen = 0; indoc = False
for line in lines:
    s = line.strip()
    if indoc:
        if '-/' in s: indoc = False
        continue
    m = re.match(r'^(\s*)-- \[(arm|change):([^\]]+)\]', line)
    if m:
        cur = f'{m.group(2)}:{m.group(3)}'; ind = len(m.group(1)); mode = None; seen = 0; continue
    if cur is None: continue
    if s.startswith('/-'):
        if '-/' not in s: indoc = True
        if mode is None: continue
        cur = None; continue
    if s == '':
        cur = None; continue
    if s.startswith('--'): continue
    if mode is None:
        mode = 'decl' if opener.match(line) else 'arm'
    elif top.match(line):
        cur = None; continue
    lead = len(line) - len(line.lstrip())
    if mode == 'arm' and seen > 0 and s.startswith('|') and lead <= ind:
        cur = None; continue
    counts[cur] += 1; seen += 1
for k in sorted(counts): print(f'{k}\t{counts[k]}')
print('total\t' + str(sum(counts.values())))
