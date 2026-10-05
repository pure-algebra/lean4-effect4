#!/usr/bin/env python3
"""Seat A401: give every changed citation its class, and name the declaration that carries it.

Run (after map_citations.py): python3 classify.py

It joins `citations-mapped.tsv` and `ranges.tsv` with the hand table `hunk-classes.tsv`, and writes
under ../out/:

  changed-citations.tsv   one row per citation whose status is `changed` or `removed`
  class-summary.tsv       the counts by cited file, class and reach
  unclassified.tsv        the hunks that a cited range meets and that the hand table lacks (must be empty)

The class of a citation is the strongest class among the hunks its range meets
(behaviour, api, host, refactor, cosmetic), and its reach the widest (main, budget, corner,
outside, none). `declaration` is the Lean declaration that carries the citing line, found by
text: the declaration after a docstring, or the one that encloses a comment. It is a name read
from the source text, not from the environment.
"""
import os
import re
import sys

import a401lib as lib

OUT = os.path.join(lib.HERE, "..", "out")
CLASS_ORDER = ["behaviour", "api", "host", "refactor", "cosmetic"]
REACH_ORDER = ["main", "budget", "corner", "outside", "none"]
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |partial |unsafe |public )*"
                  r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|proof_goal|example|opaque|axiom)\s+"
                  r"([^\s:({\[]+)?")
NAMESPACE = re.compile(r"^\s*namespace\s+(\S+)")
END = re.compile(r"^\s*end\s+(\S+)")


def load_classes():
    table = {}
    with open(os.path.join(lib.HERE, "hunk-classes.tsv"), encoding="utf8") as handle:
        for line in handle:
            if line.startswith("#") or not line.strip():
                continue
            file, hunks, klass, reach, note = line.rstrip("\n").split("\t", 4)
            for hunk in hunks.split(","):
                table[(file, int(hunk))] = (klass, reach, note)
    return table


class LeanFile:
    """The declarations of one Lean file, by line, read from the text."""

    def __init__(self, path):
        with open(os.path.join(lib.REPO, path), encoding="utf8") as handle:
            self.lines = handle.read().split("\n")
        self.decls = []          # (line, full name, keyword)
        stack = []
        depth = 0
        for number, line in enumerate(self.lines, start=1):
            opens, closes = line.count("/-"), line.count("-/")
            if depth == 0:
                space = NAMESPACE.match(line)
                if space:
                    stack.append(space.group(1))
                closing = END.match(line)
                if closing and stack and stack[-1].split(".")[-1] == closing.group(1).split(".")[-1]:
                    stack.pop()
                decl = DECL.match(line)
                if decl and not line.lstrip().startswith(("--", "/-")):
                    name = decl.group(2) or "(anonymous)"
                    if name.startswith("_root_."):
                        full = name[len("_root_."):]
                    else:
                        full = ".".join(stack + [name]) if decl.group(1) != "example" else "(example)"
                    self.decls.append((number, full, decl.group(1)))
            depth = max(0, depth + opens - closes)

    def carrier(self, number):
        """The declaration that carries line `number`: the next one when the line is in a docstring
        that a declaration follows, else the one before the line."""
        line = self.lines[number - 1]
        in_doc = False
        for back in range(number, 0, -1):
            text = self.lines[back - 1]
            if "-/" in text and back != number:
                break
            if "/--" in text or "/-!" in text:
                in_doc = "/--" in text
                break
        if in_doc or line.lstrip().startswith("/--"):
            for decl_line, name, keyword in self.decls:
                if decl_line >= number:
                    return name, keyword
        before = [d for d in self.decls if d[0] <= number]
        return (before[-1][1], before[-1][2]) if before else ("(module)", "")


def strongest(values, order):
    for value in order:
        if value in values:
            return value
    return ""


def main():
    classes = load_classes()
    ranges = {}
    with open(os.path.join(OUT, "ranges.tsv"), encoding="utf8") as handle:
        for line in list(handle)[1:]:
            cells = line.rstrip("\n").split("\t")
            ranges[(cells[0], cells[1], cells[2])] = cells
    with open(os.path.join(OUT, "citations-mapped.tsv"), encoding="utf8") as handle:
        header, *rows = [line.rstrip("\n").split("\t") for line in handle]
    lean, missing, summary = {}, {}, {}
    out_rows = []
    for row in rows:
        domain, archive, path, number, form, token, pin_file, start, end = row[:9]
        status = row[11]
        if status not in ("changed", "removed"):
            continue
        cells = ranges[(pin_file, start, end)]
        hunk_ids = [int(h.split(":")[0]) for h in cells[11].split(",") if h]
        found = []
        for hunk in hunk_ids:
            entry = classes.get((pin_file, hunk))
            if entry is None:
                missing.setdefault((pin_file, hunk), 0)
                missing[(pin_file, hunk)] += 1
            else:
                found.append(entry)
        klass = strongest({e[0] for e in found}, CLASS_ORDER) or "UNCLASSIFIED"
        reach = strongest({e[1] for e in found}, REACH_ORDER)
        declaration = ""
        if path.endswith(".lean"):
            if path not in lean:
                lean[path] = LeanFile(path)
            name, keyword = lean[path].carrier(int(number))
            declaration = f"{keyword} {name}".strip()
        out_rows.append([domain, archive, path, number, declaration, form, token, pin_file, start, end, status,
                         row[13], row[14], row[15], klass, reach, ",".join(str(h) for h in hunk_ids)])
        key = (pin_file, klass, reach)
        summary[key] = summary.get(key, 0) + 1
    with open(os.path.join(OUT, "changed-citations.tsv"), "w", encoding="utf8") as out:
        out.write("\t".join(["domain", "archive", "citing_file", "citing_line", "declaration", "form", "token",
                             "pin_file", "start", "end", "status", "release_file", "new_start", "new_end",
                             "class", "reach", "hunks"]) + "\n")
        for row in out_rows:
            out.write("\t".join(row) + "\n")
    with open(os.path.join(OUT, "class-summary.tsv"), "w", encoding="utf8") as out:
        out.write("pin_file\tclass\treach\tcitations\n")
        for (pin_file, klass, reach), count in sorted(summary.items()):
            out.write(f"{pin_file}\t{klass}\t{reach}\t{count}\n")
    with open(os.path.join(OUT, "unclassified.tsv"), "w", encoding="utf8") as out:
        out.write("pin_file\thunk\tcitations\n")
        for (pin_file, hunk), count in sorted(missing.items()):
            out.write(f"{pin_file}\t{hunk}\t{count}\n")
    totals = {}
    for (_, klass, reach), count in summary.items():
        totals[(klass, reach)] = totals.get((klass, reach), 0) + count
    print(f"changed or removed citations {len(out_rows)}; unclassified hunks {len(missing)}", file=sys.stderr)
    for (klass, reach), count in sorted(totals.items(), key=lambda kv: -kv[1]):
        print(f"  {count}\t{klass}\t{reach}", file=sys.stderr)


if __name__ == "__main__":
    main()
