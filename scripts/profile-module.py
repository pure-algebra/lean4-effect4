#!/usr/bin/env python3
"""Profile one built module: where its elaboration spends time, and what its aesop calls do.

    python3 scripts/profile-module.py src/Effect4/Laws/Program/Typed/Seq.lean

The module's imports are built first (`lake build <module>`), then the one file is re-elaborated,
with the precompiled libraries loaded as `lake build` loads them, under Lean's profiler (`-Dprofiler=true`) and aesop's statistics file (`aesop.collectStats`,
`aesop.stats.file`, one JSON record per aesop invocation). Outputs go to `.lake/gen/profile/`:
the raw profiler log, the aesop records, and a summary printed here:

- the profiler's cumulative times by category, and the slowest single steps;
- per declaration, its aesop calls, their total time and whether they closed their goals;
- the rules whose applications took the most time, with their success counts.

It answers the reference scout's "tier 1, per module, on demand" (docs/research/
2026-10-04-reference-scout/environment.md, recommendation 2) and serves the slow proofs of the
tooling map's item 1.11. Nothing it prints is evidence; it is a measurement for rewriting proofs
and tuning rule banks. Every Lean process runs with the bound the Makefile exports.
"""
import json
import pathlib
import re
import subprocess
import sys
from collections import defaultdict

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / ".lake" / "gen" / "profile"


def module_of(path: pathlib.Path) -> str:
    rel = path.resolve().relative_to(ROOT)
    parts = list(rel.with_suffix("").parts)
    if parts[0] in ("src", "tools"):
        parts = parts[1:]
    return ".".join(parts)


def ms(nanos) -> float:
    return (nanos or 0) / 1e6


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__.strip().split("\n\n")[1])
        return 2
    path = pathlib.Path(sys.argv[1])
    module = module_of(path)
    OUT.mkdir(parents=True, exist_ok=True)
    log = OUT / f"{module}.profile.txt"
    stats = OUT / f"{module}.aesop.jsonl"
    stats.unlink(missing_ok=True)
    build = subprocess.run(["lake", "build", module], cwd=ROOT)
    if build.returncode != 0:
        return build.returncode
    # the precompiled tactic and proof-graph libraries (lakefile `precompileModules`): `lake build`
    # loads them into the elaborator, `lake env lean` does not unless asked
    dynlibs = [f"--load-dynlib={lib}" for lib in sorted((ROOT / ".lake" / "build" / "lib").glob("libeffect4_*.dylib"))
               + sorted((ROOT / ".lake" / "build" / "lib").glob("libeffect4_*.so"))]
    with log.open("w") as out:
        run = subprocess.run(
            ["lake", "env", "lean", "-M6144", *dynlibs, "-Dprofiler=true", "-Dprofiler.threshold=100",
             "-Dweak.aesop.collectStats=true", f"-Dweak.aesop.stats.file={stats}", str(path)],
            cwd=ROOT, stdout=out, stderr=subprocess.STDOUT)
    text = log.read_text()
    print(f"profile of {module} (exit {run.returncode}); log {log.relative_to(ROOT)}")

    cumulative = text.split("cumulative profiling times:", 1)
    if len(cumulative) == 2:
        rows = [line.strip() for line in cumulative[1].strip().split("\n") if line.strip()]
        print("\ncumulative times by category:")
        for row in rows[:12]:
            print(f"  {row}")
    steps = re.findall(r"^(.*) took ([\d.]+)(m?s)\s*$", text, re.M)
    timed = sorted(((float(v) * (1 if unit == "ms" else 1000), what) for what, v, unit in steps),
                   reverse=True)
    if timed:
        print("\nslowest steps over 100 ms:")
        for t, what in timed[:12]:
            print(f"  {t:9.0f} ms  {what.strip()[:110]}")

    if not stats.exists():
        print("\nno aesop invocation in this module")
        return run.returncode
    per_decl = defaultdict(lambda: [0, 0.0, 0])
    per_rule = defaultdict(lambda: [0, 0, 0.0])
    for line in stats.read_text().splitlines():
        record = json.loads(line)
        decl = record.get("declaration") or "<none>"
        entry = per_decl[decl]
        entry[0] += 1
        entry[1] += ms(record.get("total"))
        entry[2] += 1 if record.get("goalSolved") else 0
        for rule in record.get("ruleStats", []):
            name = json.dumps(rule.get("rule"), sort_keys=True)[:100]
            r = per_rule[name]
            r[0] += 1
            r[1] += 1 if rule.get("successful") else 0
            r[2] += ms(rule.get("elapsed"))
    print(f"\naesop: {sum(v[0] for v in per_decl.values())} invocations in {len(per_decl)} declarations")
    for decl, (calls, total, solved) in sorted(per_decl.items(), key=lambda kv: -kv[1][1])[:12]:
        print(f"  {total:9.0f} ms  {calls:3d} call(s), {solved} closed  {decl}")
    print("\nrules by time (applications, successes):")
    for name, (apps, ok, total) in sorted(per_rule.items(), key=lambda kv: -kv[1][2])[:12]:
        print(f"  {total:9.0f} ms  {apps:5d} {ok:5d}  {name}")
    return run.returncode


if __name__ == "__main__":
    sys.exit(main())
