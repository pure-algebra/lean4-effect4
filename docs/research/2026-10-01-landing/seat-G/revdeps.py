#!/usr/bin/env python3
"""Seat G: count the modules that import a given module, directly and transitively, over the
lake roots' sources (src/ and Test/). Reading only: parses `import` lines.
Usage: revdeps.py <Module.Name> [...]"""
import os, re, sys
root = os.path.dirname(os.path.abspath(__file__))
while not os.path.exists(os.path.join(root, "lakefile.toml")):
    root = os.path.dirname(root)
mods = {}
for base in ("src", "Test"):
    for d, _, fs in os.walk(os.path.join(root, base)):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(d, f)
                rel = os.path.relpath(p, os.path.join(root, "src") if base == "src" else root)
                name = rel[:-5].replace(os.sep, ".")
                imps = []
                with open(p, encoding="utf-8") as h:
                    for line in h:
                        m = re.match(r"^import\s+(\S+)", line)
                        if m:
                            imps.append(m.group(1))
                mods[name] = imps
rev = {}
for m, imps in mods.items():
    for i in imps:
        rev.setdefault(i, set()).add(m)
for target in sys.argv[1:]:
    direct = sorted(rev.get(target, ()))
    seen, todo = set(), list(direct)
    while todo:
        x = todo.pop()
        if x in seen:
            continue
        seen.add(x)
        todo.extend(rev.get(x, ()))
    print(f"{target}: {len(direct)} direct importers, {len(seen)} transitive importers "
          f"({sum(1 for s in seen if s.startswith('Effect4'))} src, {sum(1 for s in seen if s.startswith('Test'))} Test)")
    for d in direct:
        print(f"  direct: {d}")
