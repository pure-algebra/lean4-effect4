#!/usr/bin/env python3
"""Seat TREE measurement: which declarations mention a set of names, split into
statement mentions and proof-only mentions. Rough Lean splitter (column-0 declaration
keywords), good enough for counting; every count is printed with its file list so a reader
can check it by eye.

usage: python3 measure.py <root> <name>[,<name>...] [path ...]
"""
import re
import sys
import os

DECL = re.compile(
    r'^\s{0,2}(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |partial |unsafe )*'
    r'(theorem|lemma|def|abbrev|inductive|structure|instance|class|opaque)\s+([^\s:({\[]+)')
STOP = re.compile(r'^(end\b|namespace\b|section\b|#|/-!|attribute\b|open\b|variable\b|mutual\b|set_option\b)')


def decls(path):
    with open(path, encoding='utf-8') as f:
        lines = f.read().split('\n')
    cur = None
    for i, line in enumerate(lines):
        m = DECL.match(line)
        if m:
            if cur:
                yield cur
            cur = {'kind': m.group(1), 'name': m.group(2), 'line': i + 1, 'text': [line]}
            continue
        if cur and STOP.match(line):
            yield cur
            cur = None
            continue
        if cur:
            cur['text'].append(line)
    if cur:
        yield cur


def split_statement(d):
    text = '\n'.join(d['text'])
    if d['kind'] in ('inductive', 'structure', 'class'):
        return text, ''
    # statement: up to the first ':=' or a match-arm line ('  |' at the start)
    idx = text.find(':=')
    arm = re.search(r'\n\s*\|', text)
    cut = len(text)
    if idx >= 0:
        cut = idx
    if arm and arm.start() < cut and d['kind'] in ('def', 'abbrev'):
        cut = arm.start()
    return text[:cut], text[cut:]


def main():
    root = sys.argv[1]
    names = sys.argv[2].split(',')
    paths = sys.argv[3:] or ['src', 'Test']
    pat = re.compile(r'(?<![A-Za-z0-9_.])(' + '|'.join(map(re.escape, names)) + r')(?![A-Za-z0-9_])')
    stmt, proof = [], []
    for base in paths:
        for dp, _, fs in os.walk(os.path.join(root, base)):
            for fn in sorted(fs):
                if not fn.endswith('.lean'):
                    continue
                p = os.path.join(dp, fn)
                rel = os.path.relpath(p, root)
                for d in decls(p):
                    s, b = split_statement(d)
                    if pat.search(s):
                        stmt.append((rel, d['line'], d['kind'], d['name']))
                    elif pat.search(b):
                        proof.append((rel, d['line'], d['kind'], d['name']))
    print(f'names: {names}')
    print(f'declarations whose statement mentions a name: {len(stmt)}')
    byfile = {}
    for r in stmt:
        byfile.setdefault(r[0], []).append(r)
    for f in sorted(byfile):
        print(f'  {f}: {len(byfile[f])}  ' + ', '.join(f'{n}@{l}' for _, l, _, n in byfile[f]))
    print(f'declarations mentioning a name only in the proof/body: {len(proof)}')
    byfile = {}
    for r in proof:
        byfile.setdefault(r[0], []).append(r)
    for f in sorted(byfile):
        print(f'  {f}: {len(byfile[f])}  ' + ', '.join(f'{n}@{l}' for _, l, _, n in byfile[f]))


if __name__ == '__main__':
    main()
