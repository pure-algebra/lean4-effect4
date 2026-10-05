#!/usr/bin/env python3
"""Seat A401: print one declaration of the pin beside the same declaration of the release.

Run: A401_SCRATCH=<scratch> python3 unitdiff.py <pin file> <unit key> [<unit key> ...]
     A401_SCRATCH=<scratch> python3 unitdiff.py --lines <pin file> <pin first>-<pin last> <release first>-<release last>

The output is a unified diff of the source text (comments kept), with the line numbers of both
trees in the header. A unit that only one build has is printed whole.
"""
import difflib
import json
import os
import sys

import a401lib as lib


def text(root, rel):
    with open(os.path.join(root, rel), encoding="utf8") as handle:
        return handle.read().split("\n")


def show(pin_rel, rel_rel, a_range, b_range, title):
    a = text(lib.PIN_SRC, pin_rel)[a_range[0] - 1:a_range[1]] if a_range else []
    b = text(lib.REL_SRC, rel_rel)[b_range[0] - 1:b_range[1]] if b_range else []
    print(f"=== {title}: pin {pin_rel}:{a_range[0]}-{a_range[1] if a_range else ''}"
          if a_range else f"=== {title}: not in the pin", end="")
    print(f" | release {rel_rel}:{b_range[0]}-{b_range[1]}" if b_range else " | not in the release")
    if a == b:
        print("    (equal text)")
        return
    for line in difflib.unified_diff(a, b, lineterm="", n=200):
        if line.startswith(("---", "+++", "@@")):
            continue
        print(line)


def main():
    args = sys.argv[1:]
    release_files = set(lib.tree_files(lib.REL_SRC))
    if args[0] == "--lines":
        pin_rel = args[1]
        a = tuple(int(x) for x in args[2].split("-"))
        b = tuple(int(x) for x in args[3].split("-"))
        show(pin_rel, lib.counterpart(pin_rel, release_files), a, b, "lines")
        return
    pin_rel, keys = args[0], args[1:]
    rel_rel = lib.counterpart(pin_rel, release_files)
    with open(lib.scratch("pin-src.units.json")) as handle:
        pin_units = {u["key"]: u for u in json.load(handle)[pin_rel]}
    with open(lib.scratch("rel-src.units.json")) as handle:
        rel_units = {u["key"]: u for u in json.load(handle)[rel_rel]}
    for key in keys:
        a, b = pin_units.get(key), rel_units.get(key)
        show(pin_rel, rel_rel, (a["start"], a["end"]) if a else None, (b["start"], b["end"]) if b else None, key)


if __name__ == "__main__":
    main()
