#!/usr/bin/env python3
"""Seat A401: what rests on the changed citations.

Run (after classify.py and census_against_release.py): python3 dependents.py

It reads the tree as text (no Lean build) and writes under ../out/:

  census-dependents.tsv   every census row with its verdict against the release, the class of the
                          change its span meets, and its coverage row of
                          `Test/Audit/RuntimeCoverage.lean` (disposition, coverage, witnesses)
  declarations.tsv        every Lean declaration that carries a changed citation, with the strongest
                          class and the census rows its docstring tags
  registry-direct.tsv     the claims of `tools/Tools/SemanticsRegistry.lean` whose pointer is such a
                          declaration or a witness of a census row that changed in code
  register-rows.tsv       the rows of `Test/Counterexamples/REGISTER.md` that hold a changed citation

A claim that rests on a changed declaration through other theorems is not found here: that needs
the proof graph of a Lean build.
"""
import os
import re
import sys

import a401lib as lib

OUT = os.path.join(lib.HERE, "..", "out")
ORDER = ["behaviour", "api", "host", "refactor", "cosmetic", ""]
REACH = ["main", "budget", "corner", "outside", "none", ""]


def read(path):
    with open(os.path.join(lib.REPO, path), encoding="utf8") as handle:
        return handle.read()


def table(name):
    with open(os.path.join(OUT, name), encoding="utf8") as handle:
        header, *rows = [line.rstrip("\n").split("\t") for line in handle]
    return header, rows


def coverage_rows():
    text = read("Test/Audit/RuntimeCoverage.lean")
    out = {}
    for match in re.finditer(r'\{ id := "([^"]+)", kind := "([^"]+)", disposition := "([^"]+)", coverage := "([^"]+)"(.*?)\}\s*(?=,\s*\{ id|\])',
                             text, re.S):
        row_id, kind, disposition, coverage, rest = match.groups()
        witnesses = re.findall(r"`([A-Za-z0-9_.']+)", rest.split("witnesses :=", 1)[1] if "witnesses :=" in rest else "")
        out[row_id] = (disposition, coverage, witnesses)
    return out


def registry_claims():
    text = read("tools/Tools/SemanticsRegistry.lean")
    claims = []
    for match in re.finditer(r'\{ id := "([^"]+)"\s*,?\s*concept := "([^"]+)"(.*?)(?=\{ id := "|\Z)', text, re.S):
        claim_id, concept, rest = match.groups()
        pointer = re.search(r"pointer := \.(witness|refutedBy|absent|assumed)\s*(?:\"([^\"]*)\"\s*)?(?:`([A-Za-z0-9_.']+))?", rest)
        if pointer:
            claims.append((claim_id, concept, pointer.group(1), pointer.group(3) or ""))
    return claims


def main():
    _, changed = table("changed-citations.tsv")
    _, census = table("census-against-release.tsv")
    coverage = coverage_rows()

    by_token = {}
    for row in changed:
        if row[5] == "census-row":
            by_token[row[6]] = (row[14], row[15])
    affected_witnesses = {}
    with open(os.path.join(OUT, "census-dependents.tsv"), "w", encoding="utf8") as out:
        out.write("\t".join(["id", "file", "pin_lines", "verdict", "code", "class", "reach", "disposition",
                             "coverage", "witnesses", "witness_names"]) + "\n")
        for kind, row_id, file, pin_lines, verdict, _, code, _, _ in census:
            klass, reach = by_token.get(row_id, ("", ""))
            disposition, cov, witnesses = coverage.get(row_id, ("?", "?", []))
            out.write("\t".join([row_id, file, pin_lines, verdict, code, klass, reach, disposition, cov,
                                 str(len(witnesses)), " ".join(witnesses)]) + "\n")
            if klass in ("behaviour", "api", "host", "refactor"):
                for name in witnesses:
                    affected_witnesses.setdefault(name, set()).add(f"{row_id}:{klass}")

    declarations = {}
    for row in changed:
        if row[1] != "live" or not row[4]:
            continue
        key = (row[2], row[4])
        entry = declarations.setdefault(key, {"classes": set(), "reaches": set(), "cites": 0, "files": set()})
        entry["classes"].add(row[14])
        entry["reaches"].add(row[15])
        entry["cites"] += 1
        entry["files"].add(row[7])
    with open(os.path.join(OUT, "declarations.tsv"), "w", encoding="utf8") as out:
        out.write("\t".join(["citing_file", "declaration", "class", "reach", "changed_citations", "pin_files"]) + "\n")
        for (path, declaration), entry in sorted(declarations.items()):
            klass = next(c for c in ORDER if c in entry["classes"])
            reach = next(r for r in REACH if r in entry["reaches"])
            out.write("\t".join([path, declaration, klass, reach, str(entry["cites"]), ",".join(sorted(entry["files"]))]) + "\n")

    names = {}
    for (path, declaration), entry in declarations.items():
        name = declaration.split(" ", 1)[1] if " " in declaration else declaration
        klass = next(c for c in ORDER if c in entry["classes"])
        names.setdefault(name, set()).add(f"cites:{klass}")
    for name, tags in affected_witnesses.items():
        names.setdefault(name, set()).update(tags)
    with open(os.path.join(OUT, "registry-direct.tsv"), "w", encoding="utf8") as out:
        out.write("\t".join(["claim", "concept", "pointer_kind", "pointer", "why"]) + "\n")
        hits = 0
        for claim_id, concept, kind, pointer in registry_claims():
            if pointer in names:
                hits += 1
                out.write("\t".join([claim_id, concept, kind, pointer, ";".join(sorted(names[pointer]))]) + "\n")

    register = {}
    text = read("Test/Counterexamples/REGISTER.md").split("\n")
    for row in changed:
        if row[2] == "Test/Counterexamples/REGISTER.md":
            line = text[int(row[3]) - 1]
            ident = re.match(r"\|\s*`([^`]+)`\s*\|\s*([A-Z]+)", line)
            key = (ident.group(1), ident.group(2)) if ident else (f"line {row[3]}", "")
            entry = register.setdefault(key, {"classes": set(), "cites": []})
            entry["classes"].add(row[14])
            entry["cites"].append(f"{row[7]}:{row[8]}-{row[9]}")
    with open(os.path.join(OUT, "register-rows.tsv"), "w", encoding="utf8") as out:
        out.write("id\tstatus\tclass\tchanged_citations\n")
        for (ident, status), entry in sorted(register.items()):
            klass = next(c for c in ORDER if c in entry["classes"])
            out.write(f"{ident}\t{status}\t{klass}\t{' '.join(entry['cites'])}\n")

    print(f"census rows {len(census)}; declarations with a changed citation {len(declarations)}; "
          f"registry claims joined directly {hits}; register rows {len(register)}", file=sys.stderr)


if __name__ == "__main__":
    main()
