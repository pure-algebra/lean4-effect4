#!/usr/bin/env python3
"""Verifier of seat EFFECT (2026-10-01): an independent recount of the ingest census's unknown
heads (docs/research/ingest-delivery/commit-4/census/units.jsonl, dated 2026-09-08), by engine 1,
by engine 2, and by either, with and without the vendored repos/effect/ tree."""
import json, re
from collections import Counter, defaultdict
CENSUS = "/Users/pooks/Dev/lean4-effect4/docs/research/ingest-delivery/commit-4/census/units.jsonl"
rows = [json.loads(l) for l in open(CENSUS)]
def run(label, keep, engines):
    total = unknown = 0; heads = Counter(); projs = defaultdict(set)
    for r in rows:
        if r.get("generation") != "v4" or not keep(r): continue
        total += 1
        hs = set()
        for e in engines:
            x = r.get(e) or {}
            if x.get("code") == "E-OP-UNKNOWN":
                hs.add((x.get("detail") or "").removeprefix("unknown head: "))
        if hs:
            unknown += 1
            for h in hs:
                heads[h] += 1; projs[h].add(r["project"])
    schema_units = sum(1 for r in rows if False)
    sch = sum(n for h, n in heads.items() if h.startswith("Schema."))
    top = ", ".join(f"{h} {n}/{len(projs[h])}p" for h, n in heads.most_common(5))
    print(f"{label}: v4 units {total}; units with an unknown head {unknown}; head-answers at Schema.* {sch} "
          f"({100*sch/max(1,sum(heads.values())):.1f}% of {sum(heads.values())} head-answers); top: {top}")
outside = lambda r: not re.search(r"(^|/)repos/effect/", r.get("file", ""))
everything = lambda r: True
run("engine1, outside repos/effect/", outside, ["engine1"])
run("engine2, outside repos/effect/", outside, ["engine2"])
run("either engine, outside repos/effect/", outside, ["engine1", "engine2"])
run("engine1, all v4", everything, ["engine1"])
# how many v4 units are refused for any reason, and what share of ALL v4 units is a Schema.* unknown head
tot = sum(1 for r in rows if r.get("generation") == "v4" and outside(r))
codes = Counter((r.get("engine1") or {}).get("code") for r in rows if r.get("generation") == "v4" and outside(r))
print("engine1 codes, v4 outside repos/effect/:", ", ".join(f"{c} {n}" for c, n in codes.most_common(12)))
lifted = codes.get(None, 0)
