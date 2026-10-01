#!/usr/bin/env python3
"""How v4 corpus code consumes a SchemaError (finite grep, v4 app+test subsets):
catchTag("SchemaError"), isSchemaError, `.issue` reads, SchemaIssue formatter use,
and `mapError` right after a decode on the same or next line."""
import json, os, re, sys
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from count_schema import CENSUS, project_dir, subset_of
pats = {
    'catchTag("SchemaError"': re.compile(r"catchTag\(\s*[\"']SchemaError[\"']"),
    "Schema.isSchemaError(": re.compile(r"\bisSchemaError\("),
    ".issue read": re.compile(r"\.issue\b"),
    "SchemaIssue.<formatter>": re.compile(r"\bSchemaIssue\.(?:makeFormatter\w*|defaultFormatter|\w*Formatter\w*)"),
    "SchemaIssue.<any>": re.compile(r"\bSchemaIssue\.\w+"),
    "decode...(...).pipe(Effect.mapError / orDie / catch*)": re.compile(r"decodeUnknown\w*\([^)]*\)\([^)]*\)\s*\.pipe\(\s*Effect\.(?:mapError|orDie|catch\w*)"),
    "Effect.orDie": re.compile(r"\bEffect\.orDie\b"),
}
occ = Counter(); files = Counter(); projs = {k: set() for k in pats}
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
        if subset_of(r["file"], path) not in ("app", "test"):
            continue
        text = open(path, encoding="utf-8", errors="replace").read()
        if "SchemaError" not in text and "SchemaIssue" not in text and "decodeUnknown" not in text:
            continue
        for k, rx in pats.items():
            n = len(rx.findall(text))
            if n:
                occ[k] += n; files[k] += 1; projs[k].add(p)
print("v4 app+test files that mention SchemaError, SchemaIssue or decodeUnknown; occurrences / files / projects")
for k in pats:
    print(f"{k:<60} {occ[k]:>6} {files[k]:>6} {len(projs[k]):>4}")
