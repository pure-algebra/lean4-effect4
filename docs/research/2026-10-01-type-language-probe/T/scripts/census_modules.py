#!/usr/bin/env python3
"""Seat T (type-language probe, 2026-10-01): what the ingest census refuses, by module, and which
declaration units use each Effect module.

Input: the ingest census (docs/research/ingest-delivery/commit-4/census/units.jsonl, main checkout,
read-only), v4 units outside the vendored Effect repository (repos/effect/ in tim-smart-lalph), engine
1's verdict, as the data probe's census_heads.py reads it. Three tables:

 1. engine-1 verdicts by code (units, projects), with the detail for the codes the note ranks;
 2. E-OP-UNKNOWN heads grouped by module (the text before the head's last `.member`), units and
    projects, with each module's top heads;
 3. for every module in MODULES, the units whose source span mentions `Module.<member>` (a regex over
    the span's text read from the corpus file; spans are the census's offsets, read as Python string
    indices, so a non-ASCII file can be off by a few characters), with the verdicts those units got.

Usage: python3 census_modules.py > ../logs/census_modules.log
"""
import json
import os
import re
import sys
from collections import Counter, defaultdict

EFFECT = "/Users/pooks/Dev/lean4-effect4-probe-T/docs/research/2026-10-01-data-probe/effect"
sys.path.insert(0, EFFECT)
from count_schema import project_dir  # noqa: E402

UNITS = "/Users/pooks/Dev/lean4-effect4/docs/research/ingest-delivery/commit-4/census/units.jsonl"
MODULES = ["Layer", "Config", "ConfigProvider", "Schedule", "Stream", "Sink", "Channel", "Queue", "PubSub",
           "Mailbox", "Metric", "Logger", "Tracer", "Semaphore", "Latch", "Cache", "ScopedCache", "Pool",
           "KeyValueStore", "SynchronizedRef", "SubscriptionRef", "TxRef", "FiberMap", "FiberSet",
           "FiberHandle", "RcMap", "RcRef", "Request", "RequestResolver", "Schema", "Redacted", "Duration",
           "DateTime", "Clock", "Random", "Ref", "Deferred", "Fiber", "Scope", "Option", "Result", "Exit",
           "Cause", "Match", "Data", "Console", "HttpClient", "HttpApiBuilder", "Atom", "Command"]


def module_of(head):
    # "Schema.String.check" -> "Schema"; "unstable/cli.Command.make" -> "unstable/cli.Command"
    if head.startswith("unstable/") or head.startswith("platform/"):
        parts = head.split(".")
        return ".".join(parts[:2]) if len(parts) > 2 else parts[0]
    return head.split(".")[0] if "." in head else "(bare)"


def main():
    codes = Counter(); code_projects = defaultdict(set); details = Counter()
    heads = Counter(); head_projects = defaultdict(set)
    mod_units = Counter(); mod_projects = defaultdict(set); mod_heads = defaultdict(Counter)
    uses_units = Counter(); uses_files = defaultdict(set); uses_projects = defaultdict(set)
    uses_verdicts = defaultdict(Counter)
    rx = {m: re.compile(r"\b" + re.escape(m) + r"\.[A-Za-z_]") for m in MODULES}
    dirs = {}; texts = {}; total = 0; missing = 0
    for line in open(UNITS):
        r = json.loads(line)
        if r.get("generation") != "v4" or re.search(r"(^|/)repos/effect/", r.get("file", "")):
            continue
        total += 1
        p = r["project"]
        e = r.get("engine1") or {}
        code = e.get("code") or e.get("kind") or "none"
        codes[code] += 1; code_projects[code].add(p)
        if code in ("E-PARAM-SHAPE", "E-TYPE-PARAM", "E-PROGRAM", "E-NODE", "E-SPINE-ESCAPE", "E-ARG-DYNAMIC"):
            details[(code, (e.get("detail") or "")[:60])] += 1
        if code == "E-OP-UNKNOWN":
            h = (e.get("detail") or "").removeprefix("unknown head: ")
            heads[h] += 1; head_projects[h].add(p)
            m = module_of(h)
            mod_units[m] += 1; mod_projects[m].add(p); mod_heads[m][h] += 1
        if p not in dirs:
            dirs[p] = project_dir(p)
        path = os.path.join(dirs[p], r["file"]) if dirs[p] else None
        if path not in texts:
            try:
                texts.clear()
                texts[path] = open(path, encoding="utf-8", errors="replace").read()
            except (OSError, TypeError):
                texts[path] = None
        text = texts.get(path)
        if text is None:
            missing += 1
            continue
        span = (r.get("unit") or {}).get("span") or {}
        body = text[span.get("start", 0):span.get("end", 0)]
        for m, pat in rx.items():
            if pat.search(body):
                uses_units[m] += 1; uses_files[m].add(path); uses_projects[m].add(p)
                uses_verdicts[m][code] += 1
    print(f"v4 declaration units outside repos/effect/: {total}; unreadable spans: {missing}")
    print()
    print("## 1. engine-1 verdicts (units, projects)")
    for c, n in codes.most_common():
        print(f"{c:<22} {n:>7} {len(code_projects[c]):>3}")
    print()
    print("### details of the ranked codes")
    for (c, d), n in details.most_common(25):
        print(f"{c:<16} {n:>7}  {d}")
    print()
    print("## 2. E-OP-UNKNOWN heads by module (units, projects); top heads per module")
    for m, n in mod_units.most_common():
        top = ", ".join(f"{h} {k}" for h, k in mod_heads[m].most_common(6))
        print(f"{m:<34} {n:>6} {len(mod_projects[m]):>3}  {top}")
    print()
    print("## 3. units whose span mentions Module.<member> (units, files, projects; verdicts)")
    for m in sorted(MODULES, key=lambda m: -uses_units[m]):
        v = ", ".join(f"{c} {k}" for c, k in uses_verdicts[m].most_common(4))
        print(f"{m:<18} {uses_units[m]:>6} {len(uses_files[m]):>6} {len(uses_projects[m]):>3}  {v}")


if __name__ == "__main__":
    main()
