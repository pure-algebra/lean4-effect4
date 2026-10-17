#!/usr/bin/env python3
"""Count the modules that import a module, directly or through others.

    python3 docs/research/2026-10-17-proof-scout/probes/revdeps.py Effect4.Api.Codegen ...

It reads the import header of every `.lean` file under `src/`, `tools/` and `Test/` with the
tree's one header reader (`scripts/lib/lean_imports.py`), inverts the graph, and prints, per named
module, how many modules reach it, split into `Test`, `Effect4` and tool modules. It is the
measurement behind the rebuild costs of the proof scout's slices; it builds nothing.
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'scripts'))
from lib.lean_imports import header_imports  # noqa: E402


def module_of(path: Path) -> str:
    parts = list(path.relative_to(ROOT).with_suffix('').parts)
    if parts[0] in ('src', 'tools'):
        parts = parts[1:]
    return '.'.join(parts)


def importers() -> dict[str, set[str]]:
    rev: dict[str, set[str]] = {}
    for top in ('src', 'tools', 'Test'):
        for f in (ROOT / top).rglob('*.lean'):
            if '.lake' in f.parts or 'node_modules' in f.parts:
                continue
            for imported in header_imports(f.read_text()):
                rev.setdefault(imported, set()).add(module_of(f))
    return rev


def dependents(rev: dict[str, set[str]], module: str) -> set[str]:
    seen: set[str] = set()
    stack = [module]
    while stack:
        for m in rev.get(stack.pop(), ()):
            if m not in seen:
                seen.add(m)
                stack.append(m)
    return seen


def main() -> None:
    rev = importers()
    tool_roots = ('Tools', 'Drivers', 'ProofGraph', 'Conform', 'OCaml5')
    for module in sys.argv[1:]:
        d = dependents(rev, module)
        tests = sum(1 for m in d if m.startswith('Test'))
        core = sum(1 for m in d if m.startswith('Effect4'))
        tools = sum(1 for m in d if m.startswith(tool_roots))
        print(f"{module}: {len(d)} dependents ({tests} Test, {core} Effect4, {tools} tools)")


if __name__ == '__main__':
    main()
