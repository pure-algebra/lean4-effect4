"""The imports of a Lean source's header, read as Lean's header grammar reads them.

The header is an optional `module`, an optional `prelude`, then imports. Each import is
`[public] [meta] import [all] Name`: one module per `import` keyword (Lean 4.33,
`Lean.Parser.Module`). Comments may stand anywhere in it: `--` to the end of the line, and
`/- … -/`, which nest. The header ends at the first other token. A documentation comment
(`/--` or `/-!`) is such a token, not a comment (HCF-02). A name part in `«…»` whose text is a
plain identifier reads as that identifier, so `«Effect4».Program.Ty` is `Effect4.Program.Ty`
(HCF-01); any other quoted part keeps its guillemets. Every script that needs a module's imports
reads them here (the build profile's graph missed `public import` lines and the imports below a
block comment until 2026-10-09, Codex's review HC-R8).
"""
import json
import re
from pathlib import Path

_MODIFIERS = ('public', 'meta')
_PLAIN = re.compile(r"[A-Za-z_][\w'!?]*", re.ASCII)


def _tokens(text: str):
    """The words of `text`, with its comments skipped, up to a documentation comment; a `«…»`
    name part is one word."""
    i, n = 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j + 1
        elif text.startswith(('/--', '/-!'), i):
            return
        elif text.startswith('/-', i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith('/-', i):
                    depth, i = depth + 1, i + 2
                elif text.startswith('-/', i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            j = i
            while j < n and not text[j].isspace() and not text.startswith(('--', '/-'), j):
                if text[j] == '«':
                    k = text.find('»', j)
                    j = n if k < 0 else k + 1
                else:
                    j += 1
            yield text[i:j]
            i = j


def _name(word: str) -> str:
    """The module name that `word` spells. It splits at each `.` outside `«…»`. A quoted part whose
    text is a plain identifier loses its guillemets."""
    parts, part, quoted = [], '', False
    for ch in word:
        if ch == '.' and not quoted:
            parts.append(part)
            part = ''
            continue
        if ch == '«':
            quoted = True
        elif ch == '»':
            quoted = False
        part += ch
    parts.append(part)
    return '.'.join(p[1:-1] if len(p) > 2 and p[0] == '«' and p[-1] == '»' and _PLAIN.fullmatch(p[1:-1]) else p
                    for p in parts)


def header_imports(text: str) -> list[str]:
    """The modules the header of `text` imports, in order."""
    words = _tokens(text)
    word = next(words, None)
    for keyword in ('module', 'prelude'):
        if word == keyword:
            word = next(words, None)
    out: list[str] = []
    while word is not None:
        while word in _MODIFIERS:
            word = next(words, None)
        if word != 'import':
            break
        word = next(words, None)
        if word == 'all':
            word = next(words, None)
        if word is None:
            break
        out.append(_name(word))
        word = next(words, None)
    return out


def imports_of(path: Path) -> list[str]:
    """The modules the Lean source at `path` imports."""
    return header_imports(Path(path).read_text(encoding='utf-8', errors='replace'))


# Where a workspace module's source stands: the library roots `src` and `tools`, then the
# repository itself (`Test`, `harness`).
SOURCE_DIRS = ('src', 'tools', '.')


def workspace_source(root: Path, module: str) -> Path | None:
    """The workspace file of `module` under `root`, or None for a module of the toolchain or a
    package."""
    relative = Path(*module.split('.')).with_suffix('.lean')
    for base in SOURCE_DIRS:
        if (root / base / relative).is_file():
            return root / base / relative
    return None


def source_closure(root: Path, roots: list[str], manifest: str | None = None) -> list[str]:
    """Sorted workspace sources reached by module names or Lean files, including file roots.

    Package and toolchain modules are represented by the caller's build pins. A missing file
    root is an error; it must never turn a failed dependency scan into an empty cache key.
    """
    root = root.resolve()
    pending: list[str] = []
    files: set[Path] = set()
    for entry in roots:
        if entry.endswith('.lean'):
            source = (root / entry).resolve()
            pending.extend(imports_of(source))
            files.add(source)
        else:
            source = workspace_source(root, entry)
            if source is None:
                raise FileNotFoundError(f'workspace root module not found: {entry}')
            pending.append(entry)
    if manifest is not None:
        for group in json.loads((root / manifest).read_text(encoding='utf-8'))['groups']:
            pending.extend(m for m in group['Imports'].split(',') if m)
    seen: set[str] = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        source = workspace_source(root, module)
        if source is None:
            continue
        files.add(source.resolve())
        pending.extend(imports_of(source))
    return sorted(path.relative_to(root).as_posix() for path in files)
