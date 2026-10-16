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

`--touched [--base REV]` prints, on one line, the batteries (`Test/` modules) that a change reaches
by name: each battery the change edits, each battery that imports an edited module, and each
battery that names a declaration whose text the change edits or removes. The change is the working
tree against REV (default `HEAD`). It is a near check for a landing (`make batteries-touched`): a
battery that reaches an edited declaration only through another declaration is not printed, so the
whole battery run stays the sweep's.
"""
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lib.lean_imports import header_imports, imports_of, source_closure, workspace_source  # noqa: E402

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


# A declaration's first line: attributes and modifiers, a declaring keyword, then its name.
_DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|public|nonrec)\s+)*"
                   r"(?:def|theorem|lemma|abbrev|structure|inductive|class|instance|opaque|axiom|proof_goal)\s+"
                   r"([^\s(:{\[]+)")
_HUNK = re.compile(r'^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@')
# The batteries the whole-tree gates and the slow lane own (`Test/Slow.lean`): the sweep runs them.
_SWEEP_ONLY = {'Test.All', 'Test.Slow', 'Test.Audit.AxiomGate'}


def _module_of(path: str) -> str | None:
    """The module a workspace source path holds, by `SOURCE_DIRS`' order."""
    p = Path(path)
    if p.suffix != '.lean':
        return None
    parts = p.with_suffix('').parts
    if parts[:1] in (('src',), ('tools',)):
        parts = parts[1:]
    return '.'.join(parts)


def _short(name: str) -> str:
    """The last component of a declaration name, without guillemets."""
    return name.split('.')[-1].strip('«»')


def touched(base: str) -> list[str]:
    """The battery modules the working tree's change against `base` edits, imports or names."""
    diff = subprocess.run(['git', 'diff', '-U0', base, '--', '*.lean'], cwd=ROOT, check=True,
                          capture_output=True, text=True).stdout
    edited: dict[str, list[int]] = {}
    names: set[str] = set()
    path = None
    for line in diff.splitlines():
        if line.startswith('+++ '):
            path = None if line[4:] == '/dev/null' else line[6:]
            if path is not None:
                edited.setdefault(path, [])
        elif (m := _HUNK.match(line)) and path is not None:
            start, count = int(m.group(1)), int(m.group(2) or '1')
            edited[path].extend(range(start, start + max(count, 1)))
        elif line.startswith('-') and not line.startswith('---') and (m := _DECL.match(line[1:])):
            names.add(_short(m.group(1)))
    for path, lines in edited.items():
        source = ROOT / path
        if not source.is_file():
            continue
        text_lines = source.read_text(encoding='utf-8', errors='replace').splitlines()
        starts = [(i + 1, _short(m.group(1)), 'private' in text.split(m.group(1))[0])
                  for i, text in enumerate(text_lines) if (m := _DECL.match(text))]
        hidden: set[str] = set()
        for line in lines:
            enclosing = [(name, private) for start, name, private in starts if start <= line]
            if enclosing:
                names.add(enclosing[-1][0])
                if enclosing[-1][1]:
                    hidden.add(enclosing[-1][0])
        # No battery names a private declaration, so an edited one reaches the batteries through
        # the declarations of its file that name it: a public wrapper reads its private helper.
        blocks = [(name, '\n'.join(text_lines[start - 1:(starts[k + 1][0] - 1) if k + 1 < len(starts) else None]))
                  for k, (start, name, _) in enumerate(starts)]
        private = {name for _, name, p in starts if p}
        while hidden:
            pattern = re.compile(r"(?<![\w'?!])(?:" + '|'.join(sorted(map(re.escape, hidden))) + r")(?![\w'?!])")
            hidden = {name for name, block in blocks if name not in names and pattern.search(block)}
            names |= hidden
            hidden &= private
    modules = {m for p in edited if (m := _module_of(p))}
    word = re.compile(r"(?<![\w'?!])(?:" + '|'.join(sorted(map(re.escape, names))) + r")(?![\w'?!])") \
        if names else None
    sweep = _SWEEP_ONLY | set(imports_of(ROOT / 'Test' / 'Slow.lean'))
    out = []
    for battery in sorted((ROOT / 'Test').rglob('*.lean')):
        module = _module_of(str(battery.relative_to(ROOT)))
        if module in sweep:
            continue
        text = battery.read_text(encoding='utf-8', errors='replace')
        if (module in modules or any(i in modules for i in header_imports(text))
                or (word is not None and word.search(text))):
            out.append(module)
    return out


def main(argv: list[str]) -> int:
    if argv[:1] == ['--touched']:
        base = argv[2] if argv[1:2] == ['--base'] and len(argv) > 2 else 'HEAD'
        print(' '.join(touched(base)))
        return 0
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
        print('usage: lean-imports.py FILE... | --closure [--manifest PATH] ROOT... | --dynlibs FILE... | --touched [--base REV]',
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
