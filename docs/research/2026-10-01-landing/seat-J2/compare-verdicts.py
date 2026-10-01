#!/usr/bin/env python3
"""Seat J2: compare two verdict dumps of `engine-verdicts.ts` file by file.

    compare-verdicts.py <left.jsonl> <right.jsonl> [--loops <program-names-file>]

Prints the number of files whose lines are identical and, for the rest, the file names with the
two lines' `class`/`oracle`/`verdicts` summaries; `--loops` names programs whose files are tallied
separately (the 45 loop programs). Reads only."""
import json, sys
from collections import Counter
left = {json.loads(l)["file"]: l.strip() for l in open(sys.argv[1]) if l.strip()}
right = {json.loads(l)["file"]: l.strip() for l in open(sys.argv[2]) if l.strip()}
loops = set()
if "--loops" in sys.argv:
    loops = set(open(sys.argv[sys.argv.index("--loops") + 1]).read().split())
assert left.keys() == right.keys(), (len(left), len(right), sorted(left.keys() ^ right.keys())[:5])
program = lambda f: f.split("-", 1)[1] if "-" in f and not f.startswith("g") and f.split("-", 1)[0] not in ("g",) else f
def prog(f):
    # foreign files are <style>-<program>; printed ones are <program>
    return f.split("-", 1)[1] if "-" in f else f
same = [f for f in left if left[f] == right[f]]
diff = [f for f in left if left[f] != right[f]]
print(f"files {len(left)}; identical {len(same)}; different {len(diff)}")
if loops:
    in_loops = [f for f in diff if prog(f) in loops]
    print(f"  of the different: {len(in_loops)} are loop programs, {len(diff) - len(in_loops)} are not")
def summary(line):
    r = json.loads(line)
    out = {k: r[k] for k in ("class", "oracle", "parsed", "stable", "drift") if k in r}
    if "verdicts" in r:
        out["verdicts"] = [ (lambda v: v["kind"] + (":" + v["code"] + ":" + v["detail"] if v["kind"] == "refusal" else ""))(json.loads(v)) for v in r["verdicts"]]
    return out
kinds = Counter()
for f in diff:
    kinds[(json.dumps(summary(left[f])), json.dumps(summary(right[f])))] += 1
for (a, b), n in kinds.most_common(12):
    print(f"  x{n}\n    left  {a}\n    right {b}")
nonloop = [f for f in diff if prog(f) not in loops]
if nonloop:
    print("  non-loop differences (first 10):", nonloop[:10])
