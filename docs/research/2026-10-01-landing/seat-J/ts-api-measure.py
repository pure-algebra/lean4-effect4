#!/usr/bin/env python3
"""Seat J, step 7 (ii): which TypeScript compiler-API members the ingest recognizer's six files
use, and whether each is declared, with the same calling form, by the TypeScript 7 packages.

Reads only: the six files, and the shipped declaration files of `typescript@7.0.2` (bun's cache
copy, the version harness/schema-host pins) and of the installed `@typescript/native-preview`
(ts/eff/node_modules). Runs no compiler. Run from the worktree root."""
import os, re, sys
from pathlib import Path

FILES = ["ts/eff/check-styles.ts", "ts/eff/ingest/ck.ts", "ts/eff/ingest/census/corpus.ts",
         "ts/eff/ingest/census/legs.ts", "ts/eff/ingest/census/decls-ck.ts",
         "ts/eff/ingest/fidelity/source.ts"]
PACKAGES = {
    "typescript@7.0.2": Path(os.path.expanduser("~/.bun/install/cache/typescript@7.0.2@@@1/dist")),
    "@typescript/native-preview@7.0.0-dev.20260629.1": Path("ts/eff/node_modules/@typescript/native-preview/dist"),
}
used = {}
for f in FILES:
    for m in re.findall(r"\bts\.([A-Za-z_][A-Za-z0-9_]*)", Path(f).read_text()):
        used.setdefault(m, set()).add(f)
# Members called as free functions on the namespace (`ts.f(`), as the TS 5 API spells them.
calls = sorted({m for f in FILES for m in re.findall(r"\bts\.([a-z][A-Za-z0-9_]*)\s*\(", Path(f).read_text())})
print(f"members of `ts` used by the six files: {len(used)}; called as functions: {len(calls)}")
for name, root in PACKAGES.items():
    decls = "\n".join(p.read_text() for p in root.rglob("*.d.ts"))
    print(f"\n== {name}")
    for fn in calls:
        free = re.search(rf"export declare function {fn}\s*[<(]([^)]*)", decls)
        method = re.search(rf"^\s+{fn}\s*[<(]", decls, re.M)
        if free:
            sig = free.group(1).strip()
            print(f"  {fn}: free function ({sig[:90]})")
        elif method:
            print(f"  {fn}: MISSING as a free function (a method of the same name exists)")
        else:
            print(f"  {fn}: MISSING")
