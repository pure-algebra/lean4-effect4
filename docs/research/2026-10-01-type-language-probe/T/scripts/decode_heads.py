#!/usr/bin/env python3
"""Seat T: v4 units outside repos/effect/ refused by engine 1 as E-OP-UNKNOWN at a `Schema.decode*` or
`Schema.encode*` head (running a schema), by head, with the union of projects.
Input: the ingest census units.jsonl (main checkout, read-only). Usage: python3 decode_heads.py"""
import json, re
from collections import Counter, defaultdict
UNITS = "/Users/pooks/Dev/lean4-effect4/docs/research/ingest-delivery/commit-4/census/units.jsonl"
heads = Counter(); projs = defaultdict(set); allp = defaultdict(set); total = Counter()
for line in open(UNITS):
    r = json.loads(line)
    if r.get("generation") != "v4" or re.search(r"(^|/)repos/effect/", r.get("file", "")):
        continue
    e = r.get("engine1") or {}
    if e.get("code") != "E-OP-UNKNOWN":
        continue
    h = (e.get("detail") or "").removeprefix("unknown head: ")
    m = re.match(r"Schema\.(decode|encode)\w*$", h)
    if m:
        heads[h] += 1; projs[h].add(r["project"])
        total[m.group(1)] += 1; allp[m.group(1)].add(r["project"])
for h, n in heads.most_common():
    print(f"{h:<36} {n:>5} {len(projs[h]):>3}")
for k in ("decode", "encode"):
    print(f"all Schema.{k}* heads: {total[k]} units, {len(allp[k])} projects")
