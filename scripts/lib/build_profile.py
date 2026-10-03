"""build_profile: Lake's per-module build times joined with the import graph (scripts/build-profile.py,
scripts/status.py). The critical path is the chain of imports whose rebuilt times sum highest; a
module the build reused counts zero."""
from __future__ import annotations

import functools
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ANSI = re.compile(r"\x1b\[[0-9;]*[A-Za-z]")
BUILT = re.compile(r"Built ([A-Za-z0-9_.'«»]+) \(([0-9.]+)(ms|s)\)")


def module_sources() -> dict[str, Path]:
    found: dict[str, Path] = {}
    for base in ("src", "tools"):
        for path in (ROOT / base).rglob("*.lean"):
            found[".".join(path.relative_to(ROOT / base).with_suffix("").parts)] = path
    for path in (ROOT / "Test").rglob("*.lean"):
        found[".".join(path.relative_to(ROOT).with_suffix("").parts)] = path
    return found


def imports_of(path: Path, known: dict[str, Path]) -> list[str]:
    out: list[str] = []
    for line in path.read_text(errors="replace").split("\n"):
        stripped = line.strip()
        if stripped.startswith("import "):
            out += [name for name in stripped[len("import "):].split() if name in known]
        elif stripped and not stripped.startswith(("--", "/-", "module", "prelude", "public", "meta")):
            break
    return out


def parse(log: Path) -> dict[str, float]:
    times: dict[str, float] = {}
    for match in BUILT.finditer(ANSI.sub("", log.read_text(errors="replace"))):
        name, value, unit = match.groups()
        if ":" in name:
            continue
        times[name] = float(value) / (1000 if unit == "ms" else 1)
    return times



def profile(log: Path) -> dict | None:
    """The profile of one build log, or None when the log rebuilt nothing."""
    times = parse(log)
    if not times:
        return None
    sources = module_sources()
    graph = {name: imports_of(path, sources) for name, path in sources.items()}
    sys.setrecursionlimit(10000)

    @functools.lru_cache(maxsize=None)
    def heaviest(name: str) -> tuple[float, tuple[str, ...]]:
        best: tuple[float, tuple[str, ...]] = (0.0, ())
        for imported in graph.get(name, []):
            candidate = heaviest(imported)
            if candidate[0] > best[0]:
                best = candidate
        return best[0] + times.get(name, 0.0), best[1] + (name,)

    critical, path = max((heaviest(name) for name in times), key=lambda item: item[0])
    return {"times": times, "critical": critical, "path": path,
            "summed": sum(times.values()),
            "ranked": sorted(times.items(), key=lambda item: -item[1])}
