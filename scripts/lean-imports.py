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
by name: each battery the change edits, and each battery whose `.ilean` names a declaration whose
statement or definition the change edits or removes. A change to an instance, an attribute or a
notation reaches every battery that imports its module. The change is the working tree against
REV (default `HEAD`); build the edited modules first, so that their `.ilean` files are current. It
is a near check for a landing (`make batteries-touched`): a battery that reaches an edited
declaration only through another declaration is not printed, so the whole battery run stays the
sweep's.
"""
import json
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
_HUNK = re.compile(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@')
# A declaration whose statement alone a battery can see: its proof is invisible to every reader.
_PROOF = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|nonrec)\s+)*(?:theorem|lemma)\b")
# A change that acts on every importer, not through a name: an instance, an attribute, a notation.
_AMBIENT = re.compile(r"^\s*(?:@\[[^\]]*\b(?:simp|aesop|macro|term_elab|command_elab|instance|reducible|irreducible)\b"
                      r"|(?:scoped\s+|local\s+)?(?:instance|notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules|attribute|set_option)\b)")
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


def _main_root() -> Path:
    """The main checkout of this repository: a worktree shares its references, not its builds."""
    common = subprocess.run(['git', 'rev-parse', '--path-format=absolute', '--git-common-dir'], cwd=ROOT,
                            check=True, capture_output=True, text=True).stdout.strip()
    return Path(common).parent


def _ilean(module: str, roots: list[Path]) -> tuple[dict, Path] | None:
    """Lake's reference file of `module` (`.ilean`): its declarations' ranges and the constants it
    names, each with its defining module. The first root that holds one answers."""
    rel = Path('.lake/build/lib/lean', *module.split('.')).with_suffix('.ilean')
    for root in roots:
        if (root / rel).is_file():
            try:
                return json.loads((root / rel).read_text(encoding='utf-8')), root / rel
            except (OSError, ValueError):
                return None
    return None


def _statement_end(lines: list[str], line: int, col: int) -> int:
    """The line of a declaration's first `:=` outside brackets, from its name: where its
    statement ends."""
    depth = 0
    for i in range(line - 1, len(lines)):
        text = lines[i][col:] if i == line - 1 else lines[i]
        for j, ch in enumerate(text):
            if ch in '([{⟨':
                depth += 1
            elif ch in ')]}⟩':
                depth -= 1
            elif depth == 0 and text.startswith(':=', j):
                return i + 1
    return len(lines)


def _edits(base: str) -> tuple[dict[str, list[int]], dict[str, set[str]]]:
    """The working tree's change against `base`: each edited file's new lines, and the names of
    the declarations whose first line the change removed, by the module that held them."""
    diff = subprocess.run(['git', 'diff', '-U0', base, '--', '*.lean'], cwd=ROOT, check=True,
                          capture_output=True, text=True).stdout
    edited: dict[str, list[int]] = {}
    removed: dict[str, set[str]] = {}
    old = path = None
    for line in diff.splitlines():
        if line.startswith('--- '):
            old = None if line[4:] == '/dev/null' else line[6:]
        elif line.startswith('+++ '):
            path = None if line[4:] == '/dev/null' else line[6:]
            if path is not None:
                edited.setdefault(path, [])
        elif (m := _HUNK.match(line)) and path is not None:
            start, count = int(m.group(3)), int(m.group(4) or '1')
            edited[path].extend(range(start, start + max(count, 1)))
        elif line.startswith('-') and not line.startswith('---') and old and (m := _DECL.match(line[1:])):
            if (module := _module_of(old)) is not None:
                removed.setdefault(module, set()).add(_short(m.group(1)))
    return edited, removed


def touched(base: str) -> list[str]:
    """The battery modules the working tree's change against `base` edits or names.

    A battery names a declaration when its `.ilean` lists the constant: Lean's own record of the
    names it elaborated, not a text search. A declaration is changed when the change edits a
    line of its range, except a theorem whose edits all lie in its proof. A changed private
    declaration reaches the batteries through the declarations of its file that name it. A
    change to an instance, an attribute or a notation reaches each battery that imports the module.
    A file whose `.ilean` is older than its source, or a battery with none, is read by the earlier
    text rules, and stderr names it."""
    roots = [ROOT] + ([main] if (main := _main_root()) != ROOT else [])
    edited, removed = _edits(base)
    changed: set[str] = set()
    ambient: set[str] = set()
    by_text: set[str] = set()
    stale: list[str] = []
    for path, lines in edited.items():
        source = ROOT / path
        module = _module_of(path)
        if module is None or not source.is_file() or module.startswith('Test.'):
            continue
        text_lines = source.read_text(encoding='utf-8', errors='replace').splitlines()
        current = {_short(m.group(1)) for t in text_lines if (m := _DECL.match(t))}
        removed[module] = removed.get(module, set()) - current
        found = _ilean(module, [ROOT])
        if found is None or found[1].stat().st_mtime < source.stat().st_mtime:
            stale.append(module)
            starts = [(i + 1, _short(m.group(1))) for i, t in enumerate(text_lines) if (m := _DECL.match(t))]
            for line in lines:
                enclosing = [name for start, name in starts if start <= line]
                if enclosing:
                    by_text.add(enclosing[-1])
            continue
        ilean = found[0]
        ranges = [(name, r) for name, r in ilean.get('decls', {}).items()]
        hit: dict[str, list[int]] = {}
        for line in lines:
            inside = [(r[2] - r[0], name, r) for name, r in ranges if r[0] <= line <= r[2]]
            if inside:
                _, name, _ = min(inside, key=lambda x: x[0])
                hit.setdefault(name, []).append(line)
            elif line <= len(text_lines) and _AMBIENT.match(text_lines[line - 1]):
                ambient.add(module)
        for name, at in hit.items():
            r = ilean['decls'][name]
            head = text_lines[r[0] - 1:r[4]]
            if any(_AMBIENT.match(t) for t in head):
                ambient.add(module)
            if any(_PROOF.match(t) for t in head) and \
                    min(at) > _statement_end(text_lines, r[4], r[5]):
                continue
            changed.add(name)
        # A private declaration reaches the batteries through its file's declarations that name it.
        users: dict[str, set[str]] = {}
        for key, ref in ilean.get('references', {}).items():
            n = json.loads(key).get('c', {}).get('n')
            if n is not None:
                users[n] = {u[4] for u in ref.get('usages', []) if len(u) > 4}
        frontier = {n for n in changed if n.startswith('_private.')}
        while frontier:
            reached = set().union(*(users.get(n, set()) for n in frontier)) - changed
            changed |= reached
            frontier = {n for n in reached if n.startswith('_private.')}
    word = re.compile(r"(?<![\w'?!])(?:" + '|'.join(sorted(map(re.escape, by_text))) + r")(?![\w'?!])") \
        if by_text else None
    modules = {m for p in edited if (m := _module_of(p))}
    sweep = _SWEEP_ONLY | set(imports_of(ROOT / 'Test' / 'Slow.lean'))
    out, unread = [], []
    for battery in sorted((ROOT / 'Test').rglob('*.lean')):
        module = _module_of(str(battery.relative_to(ROOT)))
        if module in sweep:
            continue
        text = battery.read_text(encoding='utf-8', errors='replace')
        imports = header_imports(text)
        found = _ilean(module, roots)
        reached = module in modules or any(i in ambient for i in imports) \
            or (word is not None and word.search(text))
        if not reached and found is None:
            unread.append(module)
            reached = any(i in modules for i in imports)
        elif not reached:
            for key in found[0].get('references', {}):
                c = json.loads(key).get('c', {})
                n, m = c.get('n'), c.get('m')
                if n in changed or (n is not None and _short(n) in removed.get(m, ())):
                    reached = True
                    break
        if reached:
            out.append(module)
    for module in stale:
        print(f'lean-imports: {module} is newer than its .ilean; its edits are read by name', file=sys.stderr)
    if unread:
        print(f'lean-imports: {len(unread)} batteries have no .ilean; each is read by its imports', file=sys.stderr)
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
