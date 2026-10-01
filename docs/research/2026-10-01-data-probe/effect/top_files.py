#!/usr/bin/env python3
"""Top files by Schema.Struct( count in the v4 corpus, with a generated-file marker check
(first 400 bytes mention 'generated' / 'do not edit' / 'auto-generated', case-insensitive)."""
import json, os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from count_schema import CORPUS, CENSUS, project_dir
rx = re.compile(r"\bSchema\.Struct\(")
gen_rx = re.compile(r"generated|do not edit|auto-generated|@generated", re.I)
dirs = {}
rows = []
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
            text = open(path, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        n = len(rx.findall(text))
        if n:
            rows.append((n, p, r["file"], bool(gen_rx.search(text[:400])), len(text.splitlines())))
rows.sort(reverse=True)
tot = sum(r[0] for r in rows)
gtot = sum(r[0] for r in rows if r[3])
print(f"v4 files with Schema.Struct(: {len(rows)}; occurrences {tot}; in files marked generated in their first 400 bytes: {gtot} ({sum(1 for r in rows if r[3])} files)")
for r in rows[:40]:
    print(f"{r[0]:>6} {'GEN' if r[3] else '   '} {r[4]:>6} lines  {r[1]}  {r[2]}")
