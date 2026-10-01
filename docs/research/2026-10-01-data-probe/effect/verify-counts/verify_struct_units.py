#!/usr/bin/env python3
"""Verifier of seat EFFECT (2026-10-01): what kind of unit the census refuses at the head
Schema.Struct (engine 1, v4, outside repos/effect/). A unit whose source text begins with
`Schema.Struct(` (after `export const X =` / `const X =`) is a schema DECLARATION (a type), not
an Effect program; this script counts how many of the refused units are that, from the source span."""
import json, os, re, sys
from collections import Counter
sys.path.insert(0, "/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-data-probe/effect")
from count_schema import project_dir
CENSUS = "/Users/pooks/Dev/lean4-effect4/docs/research/ingest-delivery/commit-4/census/units.jsonl"
kinds = Counter(); shapes = Counter(); bsamples = {}; dirs = {}; cache = {}; n = 0; samples = []
for line in open(CENSUS):
    r = json.loads(line)
    if r.get("generation") != "v4" or re.search(r"(^|/)repos/effect/", r.get("file", "")): continue
    e = r.get("engine1") or {}
    if e.get("code") != "E-OP-UNKNOWN": continue
    head = (e.get("detail") or "").removeprefix("unknown head: ")
    if not head.startswith("Schema."): continue
    n += 1
    kinds[r.get("kind")] += 1
    p = r["project"]
    if p not in dirs: dirs[p] = project_dir(p)
    path = os.path.join(dirs[p], r["file"])
    if path not in cache:
        try: cache[path] = open(path, encoding="utf-8", errors="replace").read()
        except OSError: cache[path] = None
    text = cache[path]
    if text is None: shapes["unreadable"] += 1; continue
    s = r["unit"]["span"]
    src = text[s["start"]:s["end"]]
    # the census span starts at the declarator name: `Name = <initializer>` (or a type alias / interface)
    body = re.sub(r"^\s*[\w$]+\s*(:\s*[^=]+)?=\s*", "", src, count=1)
    alias = r"(?:Schema|S|Sch|EffectSchema)"
    def note(bucket):
        shapes[bucket] += 1
        bsamples.setdefault(bucket, [])
        if len(bsamples[bucket]) < 3: bsamples[bucket].append(f"{p} {r['file']}: {head} :: {src[:100]!r}")
    if r.get("kind") != "variable": note(f"census kind {r.get('kind')}")
    elif re.match(alias + r"\.[A-Z]\w*", body) and "=>" not in body.split("(")[0]: note("initializer is a Schema constructor expression (a schema DECLARATION)")
    elif re.match(alias + r"\.(decode|encode|is|asserts|validate)\w*", body): note("initializer is a decoder/encoder value (Schema.decode*/encode*(...))")
    elif re.match(alias + r"\.[a-z]\w*", body): note("initializer is another Schema.* function call (check/brand/optional/...)")
    else:
        shapes["other (a Schema.* call inside a larger body)"] += 1
        if len(samples) < 8: samples.append(f"{p} {r['file']}: {src[:120]!r}")
print(f"v4 units outside repos/effect/ refused E-OP-UNKNOWN at a Schema.* head (engine 1): {n}")
print("by census unit kind:", dict(kinds))
print("by source shape:", dict(shapes))
print("samples of 'other':"); print("\n".join(samples))
for b, xs in bsamples.items():
    print(f"samples of {b}:"); print("\n".join("  " + x for x in xs))
