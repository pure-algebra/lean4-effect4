#!/usr/bin/env python3
"""Seat A401: citations that name a declaration of the pin and point at other lines of the pin.

Run: A401_SCRATCH=<scratch> python3 stale_in_pin.py > ../out/stale-in-pin.tsv

A row is a candidate, not a verdict. It is listed when the code span just before the citation is
one identifier (`fiberJoin`, `Effect.succeed`), the cited file declares that identifier at the top
level, the cited lines and five lines around them do not hold the identifier, and the declaration
lies outside the cited lines. The pin's own text decides this; the release plays no part.
"""
import json
import os
import re
import sys

import a401lib as lib

rows = [line.rstrip("\n").split("\t") for line in open(os.path.join(lib.HERE, "..", "out", "citations.tsv"))][1:]
units = json.load(open(lib.scratch("pin-src.units.json")))
cache = {}


def text(root, rel):
    if (root, rel) not in cache:
        cache[(root, rel)] = open(os.path.join(root, rel), encoding="utf8").read().split("\n")
    return cache[(root, rel)]


SPAN = re.compile(r"`([^`\n]+)`")
print("\t".join(["citing_file", "citing_line", "token", "pin_file", "cited", "name", "declared_at"]))
count = 0
for domain, archive, path, number, form, token, pin_file, start, end, how, check in rows:
    if pin_file == "-" or int(start) == 0 or form == "census-row" or archive != "live":
        continue
    line = text(lib.REPO, path)[int(number) - 1]
    at = line.find(token)
    spans = [m.group(1) for m in SPAN.finditer(line[:at if at >= 0 else len(line)])]
    spans = [s for s in spans if not re.fullmatch(r"[\w./@-]*\.(ts|lean|md)(:[\d,–-]+)?|(?:[\w$.]* )?:[\d,–\s-]+", s.strip())]
    if not spans:
        continue
    name = spans[-1].strip()
    name = re.sub(r"^(Effect|Fiber|Scope|Layer|Deferred|Queue|Ref|Cause|Exit|Context)\.", "", name)
    if not re.fullmatch(r"[A-Za-z_$][\w$]*", name):
        continue
    decls = [u for u in units.get(pin_file, []) if u["key"].split("#")[0] == name and "member" not in u["kind"]]
    if not decls:
        continue
    source = text(lib.PIN_SRC, pin_file)
    a, b = int(start), int(end)
    window = "\n".join(source[max(0, a - 6):min(len(source), b + 5)])
    if re.search(r"(?<![\w$])" + re.escape(name) + r"(?![\w$])", window):
        continue
    if any(u["start"] <= b and u["end"] >= a for u in decls):
        continue
    count += 1
    print("\t".join([path, number, token, pin_file, f"{start}-{end}", name,
                     ",".join(f"{u['start']}-{u['end']}" for u in decls)]))
print(f"candidates {count}", file=sys.stderr)
