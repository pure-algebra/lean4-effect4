"""The imports of a Lean source's header, read as Lean's header grammar reads them.

The header is an optional `module`, an optional `prelude`, then imports. Each import is
`[public] [meta] import [all] Name`: one module per `import` keyword (Lean 4.33,
`Lean.Parser.Module`). Comments may stand anywhere in it: `--` to the end of the line, and
`/- … -/`, which nest. The header ends at the first other token. Every script that needs a
module's imports reads them here (the build profile's graph missed `public import` lines and the
imports below a block comment until 2026-10-09, Codex's review HC-R8).
"""
from pathlib import Path

_MODIFIERS = ('public', 'meta')


def _tokens(text: str):
    """The words of `text`, with its comments skipped; a `«…»` name part is one word."""
    i, n = 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j + 1
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
        out.append(word)
        word = next(words, None)
    return out


def imports_of(path: Path) -> list[str]:
    """The modules the Lean source at `path` imports."""
    return header_imports(Path(path).read_text(encoding='utf-8', errors='replace'))
