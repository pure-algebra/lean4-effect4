#!/usr/bin/env python3
"""Print the workspace modules that the given Lean files import, on one line; or, with
`--closure`, the workspace source files of their whole import closure; or, with `--dynlibs`, the
`--load-dynlib` flags of the native libraries that Lake loads for those modules.

A recipe that runs `lake env lean --run FILE` builds exactly these first (`build_imports` in the
`Makefile`): `lake env` builds nothing. The header is read by the one shared reader,
`scripts/lib/lean_imports.py`, which reads comments as Lean's header grammar does. This adapter
keeps only the workspace's modules (a toolchain module needs no build) and drops repeats. A file
that cannot be read stops the recipe with exit 1, before Lake runs.

`--closure [--manifest PATH] ROOT...` prints the source files, one line, sorted, of every
workspace module that the roots reach by imports. A root is a module name or a `.lean` file;
with `--manifest`, the imports of every group of that derived manifest are roots too
(`tools/Effect4Gen/manifest.json`, the `Imports` field). A producer's marker depends on these
files and on no other Lean source: an edit outside the closure cannot change what the producer
reads (the derived and fixtures groups, LC-4). A file that cannot be read prints a prerequisite
that no rule makes, so the Makefile stops instead of reading an empty closure.

`--dynlibs FILE...` prints, on one line, the flags with which `lake env lean` runs the files with
the core as native code, not interpreted (`native_flags`, `scripts/generate.py`). The Makefile's
producers that run the machine take them (`native_flags` in the `Makefile`). The modules must be
built first, as `build_imports` builds them.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lib.lean_imports import imports_of, source_closure, workspace_source  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
UNREADABLE = 'lean-imports-closure-unreadable'


def source_of(module: str) -> Path | None:
    """The workspace file of `module`, or None for a module of the toolchain or a package."""
    return workspace_source(ROOT, module)


def is_workspace(module: str) -> bool:
    return source_of(module) is not None


def closure(roots: list[str], manifest: str | None) -> list[str]:
    """The workspace source files the roots reach, relative to the repository, sorted."""
    return source_closure(ROOT, roots, manifest)


def main(argv: list[str]) -> int:
    if argv[:1] == ['--closure']:
        rest, manifest = argv[1:], None
        if rest[:1] == ['--manifest'] and len(rest) >= 2:
            manifest, rest = rest[1], rest[2:]
        try:
            print(' '.join(closure(rest, manifest)))
        except (OSError, ValueError, KeyError) as error:
            print(f'lean-imports: {error}', file=sys.stderr)
            print(UNREADABLE)
            return 1
        return 0
    if argv[:1] == ['--dynlibs']:
        from generate import native_flags
        print(' '.join(native_flags(argv[1:])))
        return 0
    if not argv:
        print('usage: lean-imports.py FILE... | --closure [--manifest PATH] ROOT... | --dynlibs FILE...',
              file=sys.stderr)
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
