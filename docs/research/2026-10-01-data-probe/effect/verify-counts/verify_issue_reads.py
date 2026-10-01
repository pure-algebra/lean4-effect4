#!/usr/bin/env python3
"""Verifier of seat EFFECT (2026-10-01): the seat's `.issue read` count (36 / 12 files / 4 projects in
schemaerror_consumers.log) matches any `.issue` property. This prints every match with its line so
each can be classified: a SchemaError's issue, or another object's `issue` field."""
import json, os, re, sys
sys.path.insert(0, "/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-data-probe/effect")
from count_schema import CENSUS, project_dir, subset_of
rx = re.compile(r"\.issue\b")
dirs = {}; n = 0
for line in open(CENSUS):
    r = json.loads(line)
    if r.get("generation") != "v4" or r["file"].endswith(".d.ts"): continue
    p = r["project"]
    if p not in dirs: dirs[p] = project_dir(p)
    path = os.path.join(dirs[p], r["file"])
    if subset_of(r["file"], path) not in ("app", "test"): continue
    text = open(path, encoding="utf-8", errors="replace").read()
    if "SchemaError" not in text and "SchemaIssue" not in text and "decodeUnknown" not in text: continue
    for i, l in enumerate(text.splitlines(), 1):
        for _ in rx.finditer(l):
            n += 1
            print(f"{p} {r['file']}:{i}: {l.strip()[:150]}")
print(f"total {n}")
