#!/usr/bin/env python3
"""Seat A401: run the runtime census's own row test against the release's source.

Run (after map_citations.py): python3 census_against_release.py > ../out/census-against-release.tsv

The census generator (`scripts/generate-effect-runtime-census.sh`) locates each row by a literal
anchor that must stand on exactly one line of its file, takes the span at fixed offsets from that
line, and compares the SHA-256 of the span's bytes with the digest it embeds. This script reads
the rows out of the generator and applies the same three steps to `vendor/effect-4.0.1/src`.
It changes nothing, and it is not the census: the census stays on the pin.

The verdict of a row:

  equal             the anchor stands once and the span's bytes have the pinned digest
  drifted           the anchor stands once and the span's bytes differ
  anchor-absent     the anchor stands on no line of the release's file
  anchor-ambiguous  the anchor stands on more than one line

`code` is the status of the row's pinned line range from `ranges.tsv` (`same`, `changed`, ...),
which ignores comments and layout, with the strongest class of the hunks the range meets.
"""
import hashlib
import os
import re
import sys

import a401lib as lib


def rows_of_generator():
    path = os.path.join(lib.REPO, "scripts", "generate-effect-runtime-census.sh")
    with open(path, encoding="utf8") as handle:
        text = handle.read()
    body = re.search(r"census_rows\(\) \{\n  cat <<'ROWS'\n(.*?)\nROWS\n", text, re.S).group(1)
    for line in body.split("\n"):
        if not line.strip():
            continue
        kind, row_id, file, anchor, first, last, digest, summary = line.split("|", 7)
        yield kind, row_id, file, anchor, int(first), int(last), digest, summary


def spans_of_table():
    out = {}
    with open(os.path.join(lib.REPO, "generated", "effect-runtime-census.tsv"), encoding="utf8") as handle:
        for line in handle:
            cells = line.rstrip("\n").split("\t")
            if cells[0] == "mechanism":
                start, end = cells[4].split("-")
                out[cells[2]] = (cells[3], int(start), int(end))
    return out


def main():
    ranges = {}
    with open(os.path.join(lib.HERE, "..", "out", "ranges.tsv"), encoding="utf8") as handle:
        for line in list(handle)[1:]:
            cells = line.rstrip("\n").split("\t")
            ranges[(cells[0], int(cells[1]), int(cells[2]))] = cells
    spans = spans_of_table()
    release_files = set(lib.tree_files(lib.REL_SRC))
    print("\t".join(["kind", "id", "file", "pin_lines", "verdict", "release_lines", "code", "hunks", "units"]))
    counts = {}
    for kind, row_id, file, anchor, first, last, digest, _ in rows_of_generator():
        target = lib.counterpart(file, release_files)
        with open(os.path.join(lib.REL_SRC, target), encoding="utf8") as handle:
            lines = handle.read().split("\n")
        hits = [i for i, line in enumerate(lines, start=1) if anchor in line]
        release_lines = ""
        if not hits:
            verdict = "anchor-absent"
        elif len(hits) > 1:
            verdict = f"anchor-ambiguous({len(hits)})"
        else:
            start, end = hits[0] + first, hits[0] + last
            span = "".join(line + "\n" for line in lines[start - 1:end])
            verdict = "equal" if hashlib.sha256(span.encode("utf8")).hexdigest() == digest else "drifted"
            release_lines = f"{start}-{end}"
        pin_file, pin_start, pin_end = spans[row_id]
        cells = ranges.get((pin_file, pin_start, pin_end))
        code = f"{cells[4]}{(':' + cells[5]) if cells and cells[5] else ''}" if cells else "?"
        counts[verdict.split("(")[0]] = counts.get(verdict.split("(")[0], 0) + 1
        print("\t".join([kind, row_id, file, f"{pin_start}-{pin_end}", verdict, release_lines, code,
                         cells[11] if cells else "", cells[12] if cells else ""]))
    print(f"census rows against the release: {dict(sorted(counts.items()))}", file=sys.stderr)


if __name__ == "__main__":
    main()
