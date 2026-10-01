#!/usr/bin/env python3
"""From the ingest census (docs/research/ingest-delivery/commit-4/census/units.jsonl), the
v4 declaration units refused E-OP-UNKNOWN ("unknown head: H"), ranked by head, excluding units in
the vendored Effect repository (repos/effect/ in tim-smart-lalph). Engine 1's verdict is used
(the compiler reader); the census pairs it with oxc's, and agreement is not required here."""
import json, re
from collections import Counter
CENSUS = "/Users/pooks/Dev/lean4-effect4/docs/research/ingest-delivery/commit-4/census/units.jsonl"
heads = Counter(); total_units = 0; unknown_units = 0; projects = {}
for line in open(CENSUS):
    r = json.loads(line)
    if r.get("generation") != "v4" or re.search(r"(^|/)repos/effect/", r.get("file", "")):
        continue
    total_units += 1
    e = r.get("engine1") or {}
    if e.get("code") == "E-OP-UNKNOWN":
        unknown_units += 1
        h = (e.get("detail") or "").removeprefix("unknown head: ")
        heads[h] += 1
        projects.setdefault(h, set()).add(r["project"])
schema = sum(n for h, n in heads.items() if h.startswith("Schema."))
print(f"v4 units outside repos/effect/: {total_units}; refused E-OP-UNKNOWN by engine 1: {unknown_units}; "
      f"of those at a Schema.* head: {schema} ({100*schema/unknown_units:.1f}%)")
print("rank head occurrences projects")
for i, (h, n) in enumerate(heads.most_common(30), 1):
    print(f"{i:>3} {h:<45} {n:>6} {len(projects[h]):>3}")
