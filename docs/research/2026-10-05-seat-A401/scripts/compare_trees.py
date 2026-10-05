#!/usr/bin/env python3
"""Seat A401: compare every source file of the pin with its counterpart in the release.

Run (after strip.mjs): A401_SCRATCH=<scratch> python3 compare_trees.py > ../out/files.tsv

One row per file of the pin, then one row per file that only the release has. The status of a row:

  identical        the source bytes are equal
  comments-layout  the bytes differ; the syntax tree is equal (comments and layout only)
  moved-only       the file moved; its code lines are equal once import paths are tree paths
  types-only       the source code differs; the compiled JavaScript is equal (types are erased)
  runtime-code     the compiled JavaScript differs
  absent           the release has no file at the path or at the moved path
  new              only the release has the file

The line counts are code lines (comments stripped, blank lines dropped) of a histogram line diff.
"""
import sys

import a401lib as lib


def main():
    pin_src, rel_src = lib.facts("pin-src"), lib.facts("rel-src")
    pin_dist, rel_dist = lib.facts("pin-dist"), lib.facts("rel-dist")
    release_files = set(rel_src)
    path_map = {p: lib.counterpart(p, release_files) for p in pin_src}
    path_map = {p: r for p, r in path_map.items() if r is not None}

    print("\t".join(["status", "pin_path", "release_path", "src_removed", "src_added", "src_hunks",
                     "js_removed", "js_added", "js_hunks"]))
    counts = {}
    matched = set()
    for pin_rel in sorted(pin_src):
        rel_rel = path_map.get(pin_rel)
        if rel_rel is None:
            status, row = "absent", [pin_rel, "-", "", "", "", "", "", ""]
        else:
            matched.add(rel_rel)
            js = lambda p: p[:-3] + ".js"
            if pin_src[pin_rel]["sha256"] == rel_src[rel_rel]["sha256"]:
                status, row = "identical", [pin_rel, rel_rel, 0, 0, 0, 0, 0, 0]
            else:
                src = lib.Pair(pin_rel, rel_rel, path_map, "src")
                dist = lib.Pair(pin_rel, rel_rel, path_map, "dist")
                same_ast = pin_src[pin_rel]["ast"] == rel_src[rel_rel]["ast"]
                same_js = pin_dist[js(pin_rel)]["ast"] == rel_dist[js(rel_rel)]["ast"] or not dist.hunks
                if same_ast:
                    status = "comments-layout"
                elif not src.hunks:
                    status = "moved-only" if pin_rel != rel_rel else "comments-layout"
                elif same_js:
                    status = "types-only"
                else:
                    status = "runtime-code"
                row = [pin_rel, rel_rel, src.removed, src.added, len(src.hunks),
                       dist.removed, dist.added, len(dist.hunks)]
        counts[status] = counts.get(status, 0) + 1
        print("\t".join([status] + [str(x) for x in row]))
    for rel_rel in sorted(release_files - matched):
        counts["new"] = counts.get("new", 0) + 1
        print("\t".join(["new", "-", rel_rel, "", "", "", "", "", ""]))
    moved = sum(1 for p, r in path_map.items() if p != r)
    print(f"pin files {len(pin_src)}; release files {len(rel_src)}; matched {len(path_map)} "
          f"(moved {moved}); by status {dict(sorted(counts.items()))}", file=sys.stderr)


if __name__ == "__main__":
    main()
