#!/usr/bin/env python3
"""Verifier of seat EFFECT (2026-10-01): an independent recount of a few corpus kinds.
Independent of the seat's file list: the corpus is walked with os.walk (every .ts/.tsx/.mts/.cts,
no .d.ts, no node_modules), each file's generation is looked up in the census files.jsonl by
(project folder, relative path), and test files are classified by this script's own rule
(a path segment test/tests/__tests__/spec or a .test./.spec. name). Two sensitivity columns:
with and without the vendored repos/effect/ tree, and with tests included."""
import json, os, re
from collections import Counter, defaultdict
CORPUS = "/Users/pooks/Dev/foldlab/corpus"
CENSUS = "/Users/pooks/Dev/lean4-effect4/docs/research/ingest-delivery/commit-4/census/files.jsonl"
gen = {}
for line in open(CENSUS):
    r = json.loads(line)
    gen[(r["project"], r["file"])] = r.get("generation")
def norm(name): return re.sub(r"-+", "-", name.replace("_", "-").lower())
KINDS = {
    "Schema.Struct(": r"\bSchema\.Struct\(",
    "optional/optionalKey/optionalWith(": r"\bSchema\.(?:optional|optionalKey|optionalWith)\(",
    "decodeUnknown*(": r"\bSchema\.decodeUnknown\w*\(",
    "Data.TaggedError(": r"\bData\.TaggedError\(",
    "Schema.TaggedError(Class)?": r"\bSchema\.TaggedError(?:Class)?\b",
    "Schema.Number": r"\bSchema\.Number\b",
    "Schema.suspend(": r"\bSchema\.suspend\(",
    "JSON.parse(": r"\bJSON\.parse\(",
    "catchTag(\"SchemaError\"": r"catchTag\(\s*[\"']SchemaError[\"']",
}
RX = {k: re.compile(v) for k, v in KINDS.items()}
TEST = re.compile(r"(^|/)(test|tests|__tests__|spec|typetest)/|\.(test|spec)\.[cm]?tsx?$")
occ = defaultdict(Counter); files = defaultdict(Counter); projs = defaultdict(lambda: defaultdict(set))
nfiles = Counter(); unknown_gen = 0
for proj in sorted(os.listdir(CORPUS)):
    pdir = os.path.join(CORPUS, proj)
    if not os.path.isdir(pdir): continue
    pid = norm(proj)
    for dp, dns, fns in os.walk(pdir):
        dns[:] = [d for d in dns if d not in ("node_modules", ".git")]
        for fn in fns:
            if not re.search(r"\.[cm]?tsx?$", fn) or fn.endswith(".d.ts"): continue
            ap = os.path.join(dp, fn); rel = os.path.relpath(ap, pdir)
            g = gen.get((pid, rel))
            if g is None: unknown_gen += 1; continue
            if g != "v4": continue
            lib = bool(re.search(r"(^|/)repos/effect/", rel)); test = bool(TEST.search(rel))
            sets = ["v4 all"]
            if not lib: sets.append("v4 outside repos/effect/")
            if not lib and not test: sets.append("v4 outside repos/effect/, no tests")
            try: text = open(ap, encoding="utf-8", errors="replace").read()
            except OSError: continue
            for s in sets: nfiles[s] += 1
            for k, rx in RX.items():
                n = len(rx.findall(text))
                if n:
                    for s in sets:
                        occ[s][k] += n; files[s][k] += 1; projs[s][k].add(proj)
print(f"files not in the census (skipped): {unknown_gen}")
for s in ["v4 outside repos/effect/, no tests", "v4 outside repos/effect/", "v4 all"]:
    print(f"## {s}: {nfiles[s]} files")
    for k in KINDS:
        print(f"  {k:<36} {occ[s][k]:>6} occ {files[s][k]:>5} files {len(projs[s][k]):>3} projects")
