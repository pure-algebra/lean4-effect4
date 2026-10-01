#!/usr/bin/env python3
"""Histogram of `Schema.<member>` spellings (regex \\bSchema\\.([A-Za-z_]\\w*)) per corpus subset,
using count_schema.py's file list and subsets. Also the histogram of `Schema.is<X>` members alone."""
import json, os, re, sys
from collections import Counter, defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_schema import CENSUS, project_dir, subset_of
rx = re.compile(r"\bSchema\.([A-Za-z_]\w*)")
hist = defaultdict(Counter)
files = defaultdict(lambda: defaultdict(set))
projects = defaultdict(lambda: defaultdict(set))
dirs = {}
with open(CENSUS) as f:
    for line in f:
        r = json.loads(line)
        gen = r.get("generation") or "none"
        if gen not in ("v4", "v3") or r["file"].endswith(".d.ts"):
            continue
        p = r["project"]
        if p not in dirs:
            dirs[p] = project_dir(p)
        path = os.path.join(dirs[p], r["file"])
        try:
            text = open(path, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        sub = gen + "/" + subset_of(r["file"], path)
        for m in rx.findall(text):
            hist[sub][m] += 1
            files[sub][m].add(path)
            projects[sub][m].add(p)
for sub in ["v4/app", "v4/test", "v3/app"]:
    h = hist[sub]
    print(f"## {sub}: {sum(h.values())} occurrences of Schema.<member>, {len(h)} distinct members")
    print(f"{'member':<34} {'occ':>6} {'files':>6} {'projects':>8}")
    for m, n in h.most_common(80):
        print(f"{m:<34} {n:>6} {len(files[sub][m]):>6} {len(projects[sub][m]):>8}")
    print()
    print(f"### {sub}: Schema.is<X> members")
    for m, n in sorted(((m, n) for m, n in h.items() if re.match(r"is[A-Z]", m)), key=lambda x: -x[1]):
        print(f"{m:<34} {n:>6} {len(files[sub][m]):>6} {len(projects[sub][m]):>8}")
    print()
