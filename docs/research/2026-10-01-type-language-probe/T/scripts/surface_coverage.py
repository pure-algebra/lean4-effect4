#!/usr/bin/env python3
"""Seat T (type-language probe, 2026-10-01): the Effect surface the corpus uses against what the ingest
reader admits.

Admitted heads are read from the generated ingest README's three tables (`ts/eff/ingest/README.md`,
worktree: "Direct heads", "Native rows" (Head column), "Derived forms" (Head column)). Used members are
the v4/app member accesses `M.<Module>.<member>` with >= 3 occurrences from logs/form_census.log
(the census's member table; occurrences / files / projects). For each module named in MODULES: the
members used, how many of them (and of their occurrences) the reader admits, and the top refused
members. A member is admitted when `Module.member` is one of the admitted heads.

Usage: python3 surface_coverage.py ../logs/form_census.log > ../logs/surface_coverage.log
"""
import re
import sys

README = "/Users/pooks/Dev/lean4-effect4-probe-T/ts/eff/ingest/README.md"
MODULES = ["Effect", "Layer", "Schema", "Schedule", "Stream", "Config", "ConfigProvider", "Option", "Result",
           "Exit", "Cause", "Data", "Context", "Scope", "Fiber", "Ref", "Deferred", "Queue", "PubSub", "Semaphore",
           "Cache", "Duration", "DateTime", "Clock", "Random", "Redacted", "Logger", "Metric", "Sink", "Match",
           "Console", "SynchronizedRef", "SubscriptionRef", "FiberSet", "FiberMap", "KeyValueStore"]


def admitted_heads():
    heads = set()
    section = None
    for line in open(README):
        if line.startswith("## "):
            section = line[3:].strip()
            continue
        if not line.startswith("| ") or line.startswith("| ---"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if section == "Direct heads" and cells[0] != "Head":
            heads.add(cells[0])
        elif section == "Native rows" and cells[0] != "Operation":
            heads.add(cells[1])
        elif section == "Derived forms" and cells[0] != "Form":
            heads.add(cells[1])
    return heads


def used_members(log):
    rows = []
    in_table = False
    for line in open(log):
        if line.startswith("### v4-app: module members"):
            in_table = True
            continue
        if in_table and line.startswith("###"):
            break
        if in_table:
            parts = line.rstrip("\n").split("\t")
            if len(parts) == 5 and parts[0].startswith("M."):
                _, module, member = parts[0].split(".", 2)
                rows.append((module, member, int(parts[1]), int(parts[2]), int(parts[3])))
    return rows


def main():
    heads = admitted_heads()
    rows = used_members(sys.argv[1])
    print(f"admitted heads read from the ingest README: {len(heads)}")
    print("module  used-members(>=3 occ)  admitted-members  occurrences  admitted-occurrences  share  top refused (occ/files/projects)")
    for m in MODULES:
        mine = [r for r in rows if r[0] == m]
        if not mine:
            print(f"{m:<16} 0")
            continue
        adm = [r for r in mine if f"{m}.{r[1]}" in heads]
        occ = sum(r[2] for r in mine)
        aocc = sum(r[2] for r in adm)
        refused = sorted((r for r in mine if f"{m}.{r[1]}" not in heads), key=lambda r: -r[2])[:(20 if m == "Effect" else 6)]
        top = ", ".join(f"{r[1]} {r[2]}/{r[3]}/{r[4]}" for r in refused)
        print(f"{m:<16} {len(mine):>4} {len(adm):>4} {occ:>7} {aocc:>7} {100 * aocc / occ:5.1f}%  {top}")


if __name__ == "__main__":
    main()
