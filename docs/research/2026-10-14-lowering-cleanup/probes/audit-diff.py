#!/usr/bin/env python3
"""Compare two `#axiom_audit` logs, one command a module, written for the same module list.

    audit-diff.py BASE.log BASE.lean HEAD.log HEAD.lean

Each `.lean` file names the modules in the order of its `#axiom_audit` lines. For each module the
script prints the walked and offending counts at base and head, the offenders that are new at
head, and every toolchain constant that a head path enters `Classical.choice` through (the first
constant of each path that is not one of this tree's).
"""
import re
import sys


def modules(path):
    out = {}
    for number, line in enumerate(open(path).read().splitlines(), 1):
        m = re.match(r'#axiom_audit (\S+)$', line)
        if m:
            out[number] = m.group(1)
    return out


def blocks(path, numbers):
    """Each command prints one message, in command order: an error that names its line, or an
    information line with no position. Messages are matched to the commands in that order."""
    text = open(path).read()
    starts = [m.start() for m in re.finditer(r'^(\S*\.lean:\d+:\d+: error: )?#axiom_audit:', text, re.M)]
    messages = [text[a:b] for a, b in zip(starts, starts[1:] + [len(text)])]
    return dict(zip(numbers, messages))


def summary(block):
    if block is None:
        return None
    m = re.search(r'(\d+) of (\d+) declarations reach', block)
    if m:
        offenders = set(re.findall(r'^  (\S+) reaches \[', block, re.M))
        return int(m.group(2)), int(m.group(1)), offenders
    m = re.search(r'#axiom_audit: (\d+) declarations within', block)
    if m:
        return int(m.group(1)), 0, set()
    return None


def entries(block):
    """The first toolchain constant of each path: the line after the last line of this tree."""
    found = set()
    lines = block.splitlines()
    for i, line in enumerate(lines):
        m = re.match(r'\s+→ (\S+)\s+\((\S+)\)', line)
        if m and not m.group(2).startswith(('OCaml5', 'Conform', 'Effect4', 'Tools', 'Test')):
            prev = lines[i - 1] if i else ''
            p = re.match(r'\s+(?:→ )?(\S+)\s+\((\S+)\)', prev)
            if p and p.group(2).startswith(('OCaml5', 'Conform', 'Effect4', 'Tools', 'Test')):
                found.add(m.group(1))
    return found


def main():
    base_log, base_lean, head_log, head_lean = sys.argv[1:5]
    def by_module(log, lean):
        names = modules(lean)
        return {names[n]: m for n, m in blocks(log, list(names)).items()}
    base, head = by_module(base_log, base_lean), by_module(head_log, head_lean)
    for module in list(dict.fromkeys(list(modules(head_lean).values()) + list(modules(base_lean).values()))):
        b, h = summary(base.get(module)), summary(head.get(module))
        def text(s):
            return 'absent' if s is None else f'{s[1]} of {s[0]} outside'
        print(f'{module}: base {text(b)}, head {text(h)}')
        if h is not None:
            new = sorted(h[2] - (b[2] if b else set()))
            if new:
                print('  new offenders: ' + ', '.join(new))
        if b is not None:
            gone = sorted(b[2] - (h[2] if h else set()))
            if gone:
                print('  offenders gone: ' + ', '.join(gone))
        if head.get(module):
            e = sorted(entries(head[module]))
            if e:
                print('  entries into the toolchain: ' + ', '.join(e))


main()
