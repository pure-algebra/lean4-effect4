#!/usr/bin/env python3
"""Per-module tables from the probe log's `probe: module` lines.

    python3 module_tables.py PROBE_LOG

Each line is `probe: module<TAB>name<TAB>theorems<TAB>goals<TAB>definitions<TAB>load-bearing<TAB>unconsumed`
(`ProofGraphProbe.lean`, `#probe_modules`). The script prints the totals by area, the law-graph
modules that no registry root reaches, the largest modules by theorem count, and the codegen's
modules. It asserts nothing.
"""
import collections
import sys


def area(name: str, depth: int) -> str:
    return ".".join(name.split(".")[:depth])


def main() -> int:
    rows = []
    for line in open(sys.argv[1], errors="replace"):
        line = line.rstrip("\n")
        if "probe: module\t" not in line:
            continue
        parts = line.split("probe: module\t", 1)[1].split("\t")
        name, thms, goals, defs, load, unconsumed = parts[0], *map(int, parts[1:6])
        rows.append((name, thms, goals, defs, load, unconsumed))
    print(f"modules {len(rows)}")
    laws = [r for r in rows if r[0].startswith("Effect4.Laws")]
    core = [r for r in rows if r[0].startswith("Effect4.") and not r[0].startswith("Effect4.Laws")]
    for label, group in [("law graph (Effect4.Laws.*)", laws), ("core (Effect4.* less Laws)", core),
                         ("Test.*", [r for r in rows if r[0].startswith("Test.")]),
                         ("Tools.* and ProofGraph.*", [r for r in rows if r[0].startswith(("Tools.", "ProofGraph."))])]:
        t = sum(r[1] for r in group)
        lb = sum(r[4] for r in group)
        un = sum(r[5] for r in group)
        print(f"{label}: {len(group)} modules, {t} theorems, {sum(r[2] for r in group)} goals, "
              f"{sum(r[3] for r in group)} definitions, {lb} load-bearing, {un} unconsumed")
    with_thms = [r for r in laws if r[1] > 0]
    unreached = [r for r in with_thms if r[4] == 0]
    print(f"\nlaw-graph modules with theorems: {len(with_thms)}; of them no root reaches any theorem: "
          f"{len(unreached)} ({sum(r[1] for r in unreached)} theorems)")
    for r in sorted(unreached, key=lambda r: -r[1]):
        print(f"  unreached\t{r[0]}\t{r[1]} theorems\t{r[5]} unconsumed")
    print("\nby area (depth 3): modules, theorems, load-bearing, unconsumed")
    by = collections.defaultdict(lambda: [0, 0, 0, 0])
    for r in laws:
        a = by[area(r[0], 3)]
        a[0] += 1; a[1] += r[1]; a[2] += r[4]; a[3] += r[5]
    for k, v in sorted(by.items(), key=lambda kv: -kv[1][1]):
        print(f"  {k}\t{v[0]}\t{v[1]}\t{v[2]}\t{v[3]}")
    print("\nlargest law-graph modules by theorems")
    for r in sorted(laws, key=lambda r: -r[1])[:25]:
        print(f"  {r[0]}\t{r[1]} theorems\t{r[4]} load-bearing\t{r[5]} unconsumed")
    print("\ncodegen modules")
    for r in rows:
        if ".Codegen" in r[0] or r[0].startswith("Effect4.Ingest"):
            print(f"  {r[0]}\t{r[1]} theorems\t{r[3]} definitions\t{r[4]} load-bearing\t{r[5]} unconsumed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
