#!/usr/bin/env python3
"""Seat G: compare the fully explicit signatures printed by probes/Statements.lean in two logs.
Usage: compare-statements.py BEFORE.log AFTER.log  (prints SAME/DIFF per declaration; exit 1 on a
difference or a missing declaration)."""
import re, sys
def sigs(path):
    blocks, cur = {}, None
    for line in open(path, encoding="utf-8").read().splitlines():
        m = re.match(r"^(Effect4\.[\w.']+) :$", line)
        if m:
            cur = m.group(1); blocks[cur] = []; continue
        if cur is not None:
            if line.startswith("  "):
                blocks[cur].append(line)
            else:
                cur = None
    return blocks
b, a = sigs(sys.argv[1]), sigs(sys.argv[2])
bad = 0
print(f"{len(b)} signatures in {sys.argv[1]}; {len(a)} in {sys.argv[2]}")
for k in b:
    same = b[k] == a.get(k)
    bad += not same
    print(("SAME " if same else "DIFF ") + k + f" ({len(b[k])} lines)")
sys.exit(1 if bad else 0)
