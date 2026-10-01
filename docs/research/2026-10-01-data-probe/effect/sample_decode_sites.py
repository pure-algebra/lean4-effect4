#!/usr/bin/env python3
"""A seeded random sample of 40 `Schema.decodeUnknown*(` call sites in the v4 corpus application
subset (count_schema.py's subsets), printed with 2 lines of context each, for a reading
classification of what the decoded input is. Seed 20261001."""
import json, os, random, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_schema import CENSUS, project_dir, subset_of
rx = re.compile(r"\bSchema\.decodeUnknown\w*\(")
sites = []
dirs = {}
with open(CENSUS) as f:
    for line in f:
        r = json.loads(line)
        if r.get("generation") != "v4" or r["file"].endswith(".d.ts"):
            continue
        p = r["project"]
        if p not in dirs:
            dirs[p] = project_dir(p)
        path = os.path.join(dirs[p], r["file"])
        try:
            lines = open(path, encoding="utf-8", errors="replace").read().splitlines()
        except OSError:
            continue
        if subset_of(r["file"], path) != "app":
            continue
        for i, l in enumerate(lines):
            if rx.search(l):
                sites.append((p, r["file"], i, lines[max(0, i - 2): i + 3]))
random.seed(20261001)
print(f"{len(sites)} line sites; sample of 40")
for p, f, i, ctx in random.sample(sites, 40):
    print(f"--- {p} {f}:{i + 1}")
    for l in ctx:
        print("    " + l[:160])
