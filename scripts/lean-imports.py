#!/usr/bin/env python3
"""Print the workspace modules that the given Lean files import, on one line.

A recipe that runs `lake env lean --run FILE` builds exactly these first (`build_imports` in the
`Makefile`): `lake env` builds nothing. The header is read by the one shared reader,
`scripts/lib/lean_imports.py`, which reads comments as Lean's header grammar does. This adapter
keeps only the workspace's modules (a toolchain module needs no build) and drops repeats. A file
that cannot be read stops the recipe with exit 1, before Lake runs.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lib.lean_imports import imports_of  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
SOURCE_DIRS = [ROOT / 'src', ROOT / 'tools', ROOT]


def is_workspace(module: str) -> bool:
    relative = Path(*module.split('.')).with_suffix('.lean')
    return any((base / relative).is_file() for base in SOURCE_DIRS)


def main(argv: list[str]) -> int:
    if not argv:
        print('usage: lean-imports.py FILE...', file=sys.stderr)
        return 2
    seen: list[str] = []
    for name in argv:
        try:
            modules = imports_of(Path(name))
        except OSError as error:
            print(f'lean-imports: cannot read {name}: {error}', file=sys.stderr)
            return 1
        for module in modules:
            if module not in seen and is_workspace(module):
                seen.append(module)
    print(' '.join(seen))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
