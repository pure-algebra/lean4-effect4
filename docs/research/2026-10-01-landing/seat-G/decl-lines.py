#!/usr/bin/env python3
"""Seat G: the line span (declaration line through the last line before the next blank line) of
named theorems in a Lean file at two git revisions. Usage: decl-lines.py FILE REV_A REV_B NAME..."""
import subprocess, sys
path, ra, rb, names = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
def text(rev):
    if rev == "WORKTREE":
        return open(path, encoding="utf-8").read()
    return subprocess.run(["git", "show", f"{rev}:{path}"], capture_output=True, text=True, check=True).stdout
def span(src, name):
    lines = src.splitlines()
    for i, l in enumerate(lines):
        if l.startswith(f"theorem {name} ") or l.startswith(f"theorem {name}\n"):
            j = i
            while j + 1 < len(lines) and lines[j + 1].strip() != "":
                j += 1
            return i + 1, j + 1
    return None
A, B = text(ra), text(rb)
tot_a = tot_b = 0
for n in names:
    sa, sb = span(A, n), span(B, n)
    la = sa[1] - sa[0] + 1 if sa else 0
    lb = sb[1] - sb[0] + 1 if sb else 0
    tot_a += la; tot_b += lb
    print(f"{n}: {ra} {path}:{sa[0]}-{sa[1]} ({la} lines) -> {rb} :{sb[0]}-{sb[1]} ({lb} lines)" if sa and sb else f"{n}: {sa} -> {sb}")
print(f"total {tot_a} -> {tot_b} lines")
