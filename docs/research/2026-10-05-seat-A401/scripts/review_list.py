#!/usr/bin/env python3
"""Seat A401: list the `cont` rows whose file the checks did not confirm, for a reading by hand.

Run: python3 review_list.py [all|live] > ../out/cont-to-read.txt
Each entry gives the citing line, the file the script chose, and the first cited line there.
"""
import os
import sys

import a401lib as lib

scope = sys.argv[1] if len(sys.argv) > 1 else "live"
rows = [line.rstrip("\n").split("\t") for line in open(os.path.join(lib.HERE, "..", "out", "citations.tsv"))][1:]
cache = {}
DEFAULTS = {}
for row in open(os.path.join(lib.HERE, "defaults.tsv"), encoding="utf8"):
    if not row.startswith("#") and row.strip():
        DEFAULTS[row.split("\t")[0]] = row.split("\t")[1]


def text(root, rel):
    key = (root, rel)
    if key not in cache:
        try:
            cache[key] = open(os.path.join(root, rel), encoding="utf8").read().split("\n")
        except OSError:
            cache[key] = []
    return cache[key]


last = None
for domain, archive, path, line, form, token, pin_file, start, end, how, check in rows:
    if form != "cont" or (scope == "live" and archive != "live"):
        continue
    kind = how.split(":")[0]
    verdict = check.split(";")[0]
    if not ((verdict == "unconfirmed" and kind != "default") or "skipped" in check):
        continue
    if verdict == "unconfirmed" and pin_file != "-" and DEFAULTS.get(path) == pin_file:
        continue        # the file's own default; the convention is the evidence
    if path != last:
        print(f"=== {path}")
        last = path
    citing = text(lib.REPO, path)[int(line) - 1].strip()
    if pin_file != "-":
        source = text(lib.PIN_SRC, pin_file)
        cited = source[int(start) - 1].strip()[:70] if int(start) <= len(source) else "<out of range>"
    else:
        cited = ""
    print(f"{line} {token} -> {pin_file if pin_file != '-' else how} [{how.split(':')[0]}|{check[:40]}] «{cited}»")
    print(f"    {citing[:190]}")
