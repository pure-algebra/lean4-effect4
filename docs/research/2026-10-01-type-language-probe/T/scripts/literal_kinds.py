#!/usr/bin/env python3
"""Seat T: the kinds of Schema literal arguments in v4 application code (regex over raw text, comments
included, as the data probe's count_schema.py counts): Schema.Literal(x) / Schema.Literals([...]) by the
kind of each literal (string, number, boolean, bigint, null), with files and projects.
Input: logs/files-v4-app.tsv (set, project, path). Usage: python3 literal_kinds.py logs/files-v4-app.tsv"""
import re, sys
from collections import Counter, defaultdict
lit1 = re.compile(r"\bSchema\.Literal\(\s*([^,)]+?)\s*[,)]")
lits = re.compile(r"\bSchema\.Literals\(\s*\[([^\]]*)\]")
def kind(tok):
    tok = tok.strip()
    if re.fullmatch(r"""(["'`]).*\1""", tok, re.S): return "string"
    if re.fullmatch(r"-?\d[\d_]*n", tok): return "bigint"
    if re.fullmatch(r"-?(\d[\d_]*\.?\d*([eE][-+]?\d+)?|0[xX][0-9a-fA-F]+)", tok): return "number"
    if tok in ("true", "false"): return "boolean"
    if tok == "null": return "null"
    return "other"
occ = Counter(); files = defaultdict(set); projs = defaultdict(set)
for line in open(sys.argv[1]):
    _, proj, path = line.rstrip("\n").split("\t")
    text = open(path, encoding="utf-8", errors="replace").read()
    for m in lit1.finditer(text):
        k = "Literal:" + kind(m.group(1)); occ[k] += 1; files[k].add(path); projs[k].add(proj)
    for m in lits.finditer(text):
        for tok in [t for t in m.group(1).split(",") if t.strip()]:
            k = "Literals:" + kind(tok); occ[k] += 1; files[k].add(path); projs[k].add(proj)
print("kind occurrences files projects")
for k, n in sorted(occ.items(), key=lambda kv: -kv[1]):
    print(f"{k:<20} {n:>6} {len(files[k]):>6} {len(projs[k]):>3}")
