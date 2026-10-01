#!/usr/bin/env python3
"""Seat F (2026-10-01): parse `#traversal_census` output into rows and counts.

Usage: census-rows.py LOG [LOG2]
  one log:  per family, the summary counts and the hand-traversal arithmetic of
            docs/core/traversal-census.md (structural + wf rows, less the nine members of the two
            fold definitions, `Checker.check`'s seven and `argTy`/`argsTy`);
  two logs: per family, every row whose class differs between LOG and LOG2, and rows in only one.
"""
import re, sys

FOLD_MEMBERS = {  # the two fold definitions' members, rows the document does not count (§7.8–7.9)
    "Effect4.Program.Checker.check", "Effect4.Program.Checker.checkLayer",
    "Effect4.Program.Checker.checkLayers", "Effect4.Program.Checker.checkStmts",
    "Effect4.Program.Checker.checkEffs", "Effect4.Program.Checker.checkAction",
    "Effect4.Program.Checker.checkStmt",
    "Effect4.Program.argTy", "Effect4.Program.argsTy",
}

def parse(path):
    text = open(path).read()
    fams = {}
    # each report starts at '#traversal_census <root>' and its rows are lines starting with two spaces
    for m in re.finditer(r"#traversal_census (\S+) \(family", text):
        root = m.group(1)
        start = m.end()
        nxt = text.find("#traversal_census", start)
        nxt2 = text.find("#exhaustive_gate", start)
        end = min([x for x in (nxt, nxt2, len(text)) if x != -1])
        block = text[start:end]
        rows = {}
        for line in block.splitlines():
            if not line.startswith("  "):
                continue
            parts = line.strip().split("\t")
            if len(parts) < 3:
                continue
            kind, where, name = parts[0], parts[1], parts[2]
            if kind not in ("fold", "generated", "structural", "wf", "one-level", "delegates", "opaque"):
                continue
            base = name.replace(" [instance]", "").replace(" [private]", "")
            detail = parts[4] if len(parts) > 4 else ""
            rows[base] = (kind, where, name, "converted:" in detail)
        fams[root] = rows
    return fams

def arithmetic(fams):
    total = conn = 0
    for root, rows in fams.items():
        k = {}
        for base, (kind, where, name, conv) in rows.items():
            k.setdefault(kind, []).append((base, conv, name))
        hand = [r for kk in ("structural", "wf") for r in k.get(kk, [])]
        counted = [r for r in hand if r[0] not in FOLD_MEMBERS]
        with_conn = [r for r in counted if r[1]]
        total += len(counted); conn += len(with_conn)
        summary = ", ".join(f"{kk} {len(v)}" for kk, v in sorted(k.items()))
        print(f"{root}: {len(rows)} rows; {summary}")
        print(f"  hand traversals (structural+wf less fold members): {len(counted)}, with a fold beside them {len(with_conn)}, without {len(counted)-len(with_conn)}")
        for base, conv, name in sorted(counted):
            if not conv:
                print(f"    without: {name}")
    print(f"ALL: hand traversals {total}, with a fold and connector {conn}, without {total-conn}")

def diff(a, b):
    for root in sorted(set(a) | set(b)):
        ra, rb = a.get(root, {}), b.get(root, {})
        print(f"== {root}")
        for base in sorted(set(ra) | set(rb)):
            ka = ra.get(base, ("-",))[0]; kb = rb.get(base, ("-",))[0]
            if ka != kb:
                print(f"  {ka:>10} -> {kb:<10} {base}")

if __name__ == "__main__":
    if len(sys.argv) == 2:
        arithmetic(parse(sys.argv[1]))
    else:
        diff(parse(sys.argv[1]), parse(sys.argv[2]))
