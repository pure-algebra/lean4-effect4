#!/usr/bin/env python3
"""Seat A401: the status of every declaration of one pin file against the release.

Run: A401_SCRATCH=<scratch> python3 unit_status.py <pin file> [--all]
Prints the units whose compiled JavaScript differs (`code`), that only one build has (`absent`,
`new`), and the counts of the rest. With --all, prints every unit.
"""
import json
import sys

import a401lib as lib
import map_citations as mc

pin_rel = sys.argv[1]
pin_src, rel_src = lib.facts("pin-src"), lib.facts("rel-src")
release_files = set(rel_src)
path_map = {p: lib.counterpart(p, release_files) for p in pin_src}
path_map = {p: r for p, r in path_map.items() if r is not None}
units = {name: mc.load_units(name) for name in ("pin-src", "rel-src", "pin-dist", "rel-dist")}
mc.PIN_DIST = __import__("os").environ.get("A401_PIN_DIST", "")
mc.REL_DIST = __import__("os").environ.get("A401_REL_DIST", "")
fm = mc.FileMap(pin_rel, path_map[pin_rel], path_map, units)
counts = {}
for u in fm.pin_units:
    st = fm.pin_status[u["key"]]
    counts[st] = counts.get(st, 0) + 1
    if "--all" in sys.argv or st in ("code", "absent"):
        print(f"{st}\t{u['key']}\t{u['kind']}\t{u['start']}-{u['end']}")
for u in fm.rel_units:
    if fm.rel_status[u["key"]] == "absent":
        counts["new"] = counts.get("new", 0) + 1
        print(f"new\t{u['key']}\t{u['kind']}\trelease {u['start']}-{u['end']}")
print(f"# {pin_rel}: {len(fm.pin_units)} units in the pin; {counts}", file=sys.stderr)
