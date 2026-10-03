#!/usr/bin/env python3
"""build-profile: where a Lake build spent its time, and which chain of modules bounds it.

    python3 scripts/build-profile.py [LOG]      default LOG: .lake/gen/build.log (make build writes it)

Reads Lake's per-module lines (`Built <module> (<time>)`) from the log, joins them with the import
graph read from the source headers (src/, tools/, Test/) and prints the modules rebuilt and their
summed time, the critical path (the chain of imports whose rebuilt times sum highest, which no
parallelism can shorten) and the slowest modules; the same Markdown goes to
.lake/gen/build-profile.md. Times are wall times under whatever else ran, so compare two profiles
taken under similar load (scripts/lib/build_profile.py).
"""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts" / "lib"))

from build_profile import profile  # noqa: E402


def main() -> int:
    log = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / ".lake/gen/build.log"
    if not log.is_file():
        print(f"FAIL build-profile: no build log at {log}; run `make build` (it writes one)")
        return 1
    result = profile(log)
    if result is None:
        print(f"build-profile: {log} rebuilt no module; nothing to profile")
        return 0
    times, ranked = result["times"], result["ranked"]
    shown = log.relative_to(ROOT) if log.is_relative_to(ROOT) else log
    lines = [
        f"# Build profile ({shown})",
        "",
        f"{len(times)} modules rebuilt, {result['summed']:.0f} s summed; the slowest is "
        f"{ranked[0][0]} at {ranked[0][1]:.0f} s.",
        "",
        f"Critical path: {result['critical']:.0f} s over {len(result['path'])} modules (rebuilt modules "
        "only; a module the build reused counts zero).",
        "",
        "| s | module |",
        "| ---: | --- |",
    ]
    lines += [f"| {times.get(name, 0.0):.1f} | {name} |" for name in result["path"] if times.get(name, 0.0) >= 1.0]
    lines += ["", "Slowest modules:", "", "| s | module |", "| ---: | --- |"]
    lines += [f"| {seconds:.1f} | {name} |" for name, seconds in ranked[:15]]
    text = "\n".join(lines) + "\n"
    print(text, end="")
    out = ROOT / ".lake/gen/build-profile.md"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())
