#!/usr/bin/env python3
"""Seat G: compare two `#exhaustive_gate` outputs. Each report's rows of BEFORE are rewritten the
way the printer change should print them (a `_private.<module>.0.` holder or matcher by its written
name, the holder marked ` [private]`); then each report's header and row multiset are compared with
AFTER. Usage: compare-exhaustive.py BEFORE.log AFTER.log"""
import re, sys
PRIV = re.compile(r"_private\.(?:[^.\t]+\.)*?0\.")
def reports(path):
    out, cur, header = {}, None, None
    for line in open(path, encoding="utf-8").read().splitlines():
        if line.startswith("#exhaustive_gate"):
            cur, header = None, line
        elif header is not None and cur is None and not line.startswith("  "):
            header += line
        elif header is not None and cur is None and "match(es) read it" not in header:
            header += line
        if header is not None and cur is None and "match(es) read it" in header:
            m = re.match(r"^#exhaustive_gate (\S+) .*? under (\S+): (\d+) match\(es\) read it, (\d+) with", header)
            cur = (m.group(1), m.group(2)); out[cur] = {"counts": (m.group(3), m.group(4)), "rows": []}
            continue
        if cur and line.startswith("  ") and "\tdiscr " in line:
            out[cur]["rows"].append(line.strip())
    return out
def rewrite(row):
    holder, rest = row.split("\t", 1)
    private = holder.startswith("_private.")
    holder = PRIV.sub("", holder) + (" [private]" if private else "")
    return holder + "\t" + PRIV.sub("", rest)
b, a = reports(sys.argv[1]), reports(sys.argv[2])
bad = 0
for key in sorted(set(b) | set(a)):
    rb = sorted(rewrite(r) for r in b.get(key, {}).get("rows", []))
    ra = sorted(a.get(key, {}).get("rows", []))
    extra = [r for r in ra if r not in rb]
    missing = [r for r in rb if r not in ra]
    privates = sum("[private]" in r for r in ra)
    print(f"{key[0]} under {key[1]}: counts before {b.get(key, {}).get('counts')} after {a.get(key, {}).get('counts')}; "
          f"{len(ra)} rows after, {privates} marked [private]; only after: {extra}; only before: {missing}")
    leftover = [r for r in ra if "_private" in r]
    if leftover:
        bad += 1
        print("  MANGLED NAMES REMAIN:", leftover)
sys.exit(1 if bad else 0)
