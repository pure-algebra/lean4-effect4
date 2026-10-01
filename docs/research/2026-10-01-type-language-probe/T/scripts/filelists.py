#!/usr/bin/env python3
"""Seat T (type-language probe, 2026-10-01): the file sets the form census reads.

The sets are the data probe's own (effect seat, `count_schema.py`): its PROBE and DOGFOOD lists and
the ingest census's corpus files split by generation and subset with its `project_dir` and
`subset_of`, imported from that script unchanged. One TSV line per file: set, project, absolute path.
`.d.ts` files are excluded, as there.

Cross-check: the v4/app set must equal the effect seat's `v4-app-files.txt` line for line (printed
as `v4/app cross-check`); a difference exits 1.

Usage: python3 filelists.py OUT_DIR   (writes OUT_DIR/files-<set>.tsv, prints a summary)
"""
import json
import os
import sys

EFFECT = "/Users/pooks/Dev/lean4-effect4-probe-T/docs/research/2026-10-01-data-probe/effect"
sys.path.insert(0, EFFECT)
from count_schema import CENSUS, DOGFOOD, PROBE, ROOT, project_dir, subset_of  # noqa: E402

SETS = ["probe", "dogfood", "v4-app", "v4-test", "v3-app"]


def main(out_dir):
    rows = {s: [] for s in SETS}
    for p in PROBE:
        rows["probe"].append(("probe", os.path.join(ROOT, p)))
    for p in DOGFOOD:
        rows["dogfood"].append((p.split("/")[2], os.path.join(ROOT, p)))
    dirs = {}
    with open(CENSUS) as f:
        for line in f:
            r = json.loads(line)
            gen = r.get("generation") or "none"
            if gen not in ("v4", "v3") or r["file"].endswith(".d.ts"):
                continue
            proj = r["project"]
            if proj not in dirs:
                dirs[proj] = project_dir(proj)
            if dirs[proj] is None:
                continue
            path = os.path.join(dirs[proj], r["file"])
            if not os.path.isfile(path):
                continue
            key = gen + "-" + subset_of(r["file"], path)
            if key in rows:
                rows[key].append((proj, path))
    os.makedirs(out_dir, exist_ok=True)
    for s in SETS:
        with open(os.path.join(out_dir, f"files-{s}.tsv"), "w") as out:
            for proj, path in rows[s]:
                out.write(f"{s}\t{proj}\t{path}\n")
        print(f"{s}: {len(rows[s])} files, {len({p for p, _ in rows[s]})} projects")
    mine = [path for _, path in rows["v4-app"]]
    theirs = open(os.path.join(EFFECT, "v4-app-files.txt")).read().splitlines()
    same = mine == theirs
    print(f"v4/app cross-check against the effect seat's v4-app-files.txt: "
          f"{'identical' if same else 'DIFFERENT'} ({len(mine)} vs {len(theirs)} lines)")
    return 0 if same else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
