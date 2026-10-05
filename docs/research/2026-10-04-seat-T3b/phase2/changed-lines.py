#!/usr/bin/env python3
"""The lines of each Lean module under src/ and Test/ that the seat's own commits wrote.

    python3 docs/research/2026-10-04-seat-T3b/phase2/changed-lines.py 917d4b5d

Reads `git blame` at HEAD for every `.lean` file a non-merge first-parent commit since the base
touched, and writes `changed-lines.json` beside this file: module name to line numbers.
`AxiomsOfChanged.lean` reads it. Run from the repository root.
"""
import json, os, re, subprocess, sys

base = sys.argv[1] if len(sys.argv) > 1 else '917d4b5d'
here = os.path.dirname(os.path.abspath(__file__))
seat = subprocess.check_output(
    ['git', 'log', '--no-merges', '--first-parent', '--format=%H', f'{base}..HEAD'], text=True).split()
files = set()
for commit in seat:
    out = subprocess.check_output(['git', 'show', '--name-only', '--format=', commit], text=True)
    files |= {f for f in out.split('\n') if f.endswith('.lean')}
modules = {}
for f in sorted(files):
    if not os.path.exists(f):
        continue
    if f.startswith('src/'):
        module = f[4:-5].replace('/', '.')
    elif f.startswith('Test/'):
        module = f[:-5].replace('/', '.')
    else:
        continue
    blame = subprocess.check_output(['git', 'blame', '--line-porcelain', 'HEAD', '--', f],
                                    text=True, errors='replace')
    lines = [int(m.group(2)) for m in re.finditer(r'^([0-9a-f]{40}) \d+ (\d+)', blame, re.M)
             if m.group(1) in set(seat)]
    if lines:
        modules[module] = sorted(set(lines))
json.dump(modules, open(os.path.join(here, 'changed-lines.json'), 'w'))
print(f'{len(seat)} commits, {len(modules)} modules, {sum(len(v) for v in modules.values())} lines')
