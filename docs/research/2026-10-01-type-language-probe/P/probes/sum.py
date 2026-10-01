#!/usr/bin/env python3
"""Totals of logs/measure.log's two tables, each declaration counted once per side."""
named = False; ps = {}; ns = {}; prod = cop = 0
for l in open("logs/measure.log"):
    if l.startswith("| what |"): named = True; continue
    if not l.startswith("| ") or l.startswith("| ---") or l.startswith("| production"): continue
    c = [x.strip() for x in l.strip().strip("|").split("|")]
    if named:
        ps[c[1]] = int(c[2]); ns[c[3]] = int(c[4])
    elif "decl." not in c[1]:
        prod += int(c[2]); cop += int(c[4])
print(f"named-vs-positional: positional {sum(ps.values())} lines in {len(ps)} declarations, "
      f"named {sum(ns.values())} lines in {len(ns)} declarations, difference {sum(ns.values()) - sum(ps.values()):+d}")
print(f"production-vs-copy rows: today {prod}, copy {cop}, difference {cop - prod:+d}")
