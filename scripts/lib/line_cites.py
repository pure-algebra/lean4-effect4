"""line_cites: rewrite a line citation into a citation by declaration name (W25 of
docs/core/controlled-english.md), or say why it cannot be rewritten.

A citation `path:N` in a code span of prose (`N` may be a range `N-M` or a list `N,M`) names a
line of a file whose lines move. The rewrite keeps the pointer and drops the number:

    `name` (`path:N`)   ->  `name` (`file`)     `file` is the one candidate that declares `name`
    `path:N`            ->  `file`              `decl` held line N of `file` when the citation was
                                                written, the paragraph names `decl`, and `file`
                                                (or the one file `decl` moved to) declares it
    `name` (`:N`)       ->  `name` (`file`)     a continuation after `path`, named in place
    `path:N`, `:M`      ->  `file`              the continuation dropped when the paragraph names
                                                the declaration that held line M

The candidates of `path` are the tracked files it names: itself, or each tracked path it ends.
`file` is written from the root. A declaration that left `file` for exactly one other tracked
Lean file is cited at its new file.

When was a citation written? Its earliest revision is the first commit whose Markdown history
adds the citation (the same file name and line, in any spelling of the path). A range names the
declaration that held most of its lines then. That declaration is written into the document
only when the paragraph (or the table row) also names it in code. When history alone names it,
the citation is left and the candidate is listed: a citation can be wrong on the day it was
written (a line of `docs/core/semantics.md` cited `Scope.lean:750` for the `Scope` structure,
and line 750 then held `removeUnsafe_not_open`), and no revision shows that. Candidates are
listed only when the revision that last wrote the citing line (git blame) agrees.

Everything else is left in place and listed with its reason. Prose citations outside code spans
are left too.
"""
from __future__ import annotations

import os
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable

from language import BARE_LINE, CODE_SPAN, LINE_CITE, units

# A Lean declaration header: attributes, modifiers, a keyword and (when it has one) the name.
HEADER = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|public|meta|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\b"
    r"(?:\s+\([^)]*\))?"           # `instance (priority := low)`
    r"\s*(?P<name>[^\s:({\[⦃\"]+)?")
LEADING = re.compile(r"^\s*(?:@\[|set_option\b.*\bin\s*$|/--|-/|\S.*-/\s*$)")
NAMED_BEFORE = re.compile(r"`(?P<name>[^`]+)`\s*\(\s*$")
RANGE_REST = re.compile(r"(?:[-–,]\s?\d+)*")
HISTORY_CITE = re.compile(r"(?<![\w@./+-])([\w@./+-]+\.lean):(\d+)")
ZERO = "0" * 40


def last_component(name: str) -> str:
    """The declaration's own name: the first word of a code span, after its last dot."""
    words = name.split()
    return (words[0] if words else name).strip("«»").rsplit(".", 1)[-1]


def headers(text: str) -> list[tuple[int, str]]:
    """Each named declaration header of a Lean file: (1-based line, name)."""
    found = []
    for number, line in enumerate(text.split("\n"), start=1):
        match = HEADER.match(line)
        if match and match.group("name") and not match.group("name").startswith(("·", "_")):
            found.append((number, match.group("name")))
    return found


def in_docstring(lines: list[str], line: int) -> bool:
    """`line` lies inside a `/-- … -/` comment."""
    for above in range(line, 0, -1):
        text = lines[above - 1]
        if "-/" in text and above != line:
            return False
        if "/--" in text:
            return True
    return False


def in_block_comment(lines: list[str], line: int) -> bool:
    """`line` lies inside a `/-! … -/` or `/- … -/` comment that is not a docstring."""
    for above in range(line, 0, -1):
        text = lines[above - 1]
        if "-/" in text and above != line:
            return False
        if "/-!" in text or re.search(r"/-(?![-!])", text):
            return True
    return False


def declaration_at(text: str, line: int) -> str | None:
    """The declaration that holds `line`: the one whose docstring, attributes or header the line
    is part of, or else the last header above it. None inside a module or section comment, and
    on a blank, `end`, `namespace`, `section`, `open` or `variable` line."""
    lines = text.split("\n")
    if not 1 <= line <= len(lines):
        return None
    marks = headers(text)
    for number, name in marks:     # a docstring or attribute block belongs to the header below it
        if number >= line:
            above = number - 1
            while above >= line and (LEADING.match(lines[above - 1]) or in_docstring(lines, above)):
                above -= 1
            if above < line:
                return name
            break
    if in_block_comment(lines, line):
        return None
    stripped = lines[line - 1].strip()
    if not stripped or stripped.startswith(("end ", "namespace ", "section", "open ", "variable")):
        return None
    before = [name for number, name in marks if number <= line]
    return before[-1] if before else None


def cited_lines(cited: str) -> list[int]:
    """The lines a citation names: `N`, a range `N-M`, or a list `N, M`."""
    numbers: list[int] = []
    for part in re.split(r",\s*", cited.lstrip(":")):
        bounds = [int(b) for b in re.split(r"[-–]", part) if b.strip().isdigit()]
        if len(bounds) == 2 and bounds[0] <= bounds[1] <= bounds[0] + 2000:
            numbers += range(bounds[0], bounds[1] + 1)
        elif bounds:
            numbers.append(bounds[0])
    return numbers


def declaration_of(text: str, lines: list[int]) -> str | None:
    """The declaration that holds most of the cited lines; on a tie, the one at the first line."""
    owners = [declaration_at(text, line) for line in lines]
    named = [owner for owner in owners if owner is not None]
    if not named:
        return None
    counts = {owner: named.count(owner) for owner in named}
    best = max(counts.values())
    leaders = [owner for owner in named if counts[owner] == best]
    return leaders[0]


def declares(text: str, name: str) -> bool:
    """A header of the file declares `name` as written, or declares exactly one name with its
    last component (the same declaration written with or without its namespace)."""
    names = [found for _, found in headers(text)]
    if name in names:
        return True
    wanted = last_component(name)
    return sum(1 for found in names if last_component(found) == wanted) == 1


def mentions(text: str, name: str) -> bool:
    """The text contains the name's last component as a whole word."""
    word = last_component(name)
    return re.search(r"(?<![\w'.])" + re.escape(word) + r"(?![\w'])", text) is not None


def names_in_code(text: str, name: str) -> bool:
    """A code span of the text ends with the name's last component: the prose names it."""
    word = re.escape(last_component(name))
    return re.search(r"`(?:[^`]*[^\w'])?" + word + r"`", text) is not None


@dataclass
class Left:
    doc: str
    line: int
    cite: str
    reason: str


@dataclass
class Result:
    rewritten: int = 0
    left: list[Left] = field(default_factory=list)
    # how each rewrite was confirmed: "named", "paragraph", "history" or "continuation"
    kinds: dict[str, int] = field(default_factory=dict)
    history: list[Left] = field(default_factory=list)   # the history-only rewrites, for review

    def count(self, kind: str) -> None:
        self.rewritten += 1
        self.kinds[kind] = self.kinds.get(kind, 0) + 1


class Fixer:
    """Rewrites the line citations of documents.

    `file_at(revision, path)` gives a file's text at a revision (ZERO is the working tree; None
    when the file is absent); `blame(doc)` gives, per 1-based line of the document, the revision
    that last wrote it; `first_seen(path, line)` gives the earliest revision whose Markdown history
    adds a citation of that file name and line, or None."""

    def __init__(self, tracked: list[str], ours: Callable[[str], bool],
                 file_at: Callable[[str, str], str | None], blame: Callable[[str], dict[int, str]],
                 first_seen: Callable[[str, int], str | None]):
        self.tracked = [p for p in tracked if not p.startswith("vendor/")]
        self.ours = ours
        self.file_at = file_at
        self.blame = blame
        self.first_seen = first_seen
        self._index: dict[str, list[str]] | None = None

    def candidates(self, path: str) -> list[str]:
        if path in self.tracked:
            return [path]
        return [p for p in self.tracked if p.endswith("/" + path)]

    def moved(self, name: str, away_from: str) -> str | None:
        """The one other tracked Lean file that declares `name` at HEAD, if exactly one does."""
        if self._index is None:
            self._index = {}
            for path in self.tracked:
                if path.endswith(".lean") and path.startswith(("src/", "Test/", "tools/")):
                    text = self.file_at(ZERO, path)
                    if text is not None:
                        for _, found in headers(text):
                            self._index.setdefault(found, []).append(path)
                            self._index.setdefault("." + last_component(found), []).append(path)
        exact = [p for p in self._index.get(name, []) if p != away_from]
        if "." in name:
            homes = sorted(set(exact))
        else:
            homes = sorted(set(exact) | {p for p in self._index.get("." + name, []) if p != away_from})
        return homes[0] if len(homes) == 1 else None

    def fix(self, doc: str, text: str) -> tuple[str, Result]:
        result = Result()
        context: dict[int, str] = {}
        for unit in units(text):
            joined = unit.row if unit.kind == "cell" else " ".join(line for _, line in unit.lines)
            for number, _ in unit.lines:
                context[number] = joined
        revisions: dict[int, str] | None = None
        out = []
        for number, line in enumerate(text.split("\n"), start=1):
            if number not in context or "`" not in line or ":" not in line:
                out.append(line)
                continue
            pieces: list[str] = []
            last = 0
            current: tuple[str, str | None, str] | None = None     # file, earliest revision, blame
            for span in CODE_SPAN.finditer(line):
                content = span.group(2).strip()
                cite = LINE_CITE.match(content)
                replacement = None
                if cite and self.ours(cite.group("path")):
                    if RANGE_REST.fullmatch(content[cite.end():]) is None:
                        result.left.append(Left(doc, number, content, "the code span holds more than the citation"))
                        current = None
                        continue
                    if revisions is None:
                        revisions = self.blame(doc)
                    replacement, current = self.rewrite(
                        doc, number, context[number], line[:span.start()], content,
                        cite.group("path"), content[cite.start("line"):], revisions.get(number, ZERO), result)
                elif BARE_LINE.match(content) and current is not None:
                    replacement = self.rewrite_continuation(doc, number, context[number],
                                                            line[:span.start()], content, current, result)
                elif cite:
                    current = None
                if replacement is not None:
                    gap = line[last:span.start()]
                    if replacement == "":      # the paragraph names it: drop the span and its separator
                        gap = re.sub(r"(?:,|;|\s+and)\s*$", "", gap)
                    pieces.append(gap)
                    pieces.append(replacement)
                    last = span.end()
            pieces.append(line[last:])
            out.append("".join(pieces))
        return "\n".join(out), result

    def rewrite(self, doc: str, number: int, unit: str, before: str, content: str, path: str,
                cited: str, blamed: str, result: Result
                ) -> tuple[str | None, tuple[str, str | None, str] | None]:
        """The replacement for one `path:N` span, and what a continuation after it needs."""
        candidates = self.candidates(path)
        if not candidates:
            result.left.append(Left(doc, number, content, "the path names no tracked file"))
            return None, None
        earliest = self.first_seen(os.path.basename(path), cited_lines(cited)[0])
        named = NAMED_BEFORE.search(before)
        if named:
            replacement = self.rewrite_named(doc, number, content, named.group("name"), candidates, result)
            chosen = replacement.strip("`") if replacement else (candidates[0] if len(candidates) == 1 else None)
            return replacement, ((chosen, earliest, blamed) if chosen else None)
        lean = [c for c in candidates if c.endswith(".lean")]
        if not lean:
            result.left.append(Left(doc, number, content, "not a Lean file; name the section by hand"))
            return None, None
        options: list[tuple[str, str]] = []
        doubts: list[str] = []
        for candidate in lean:
            then = self.declaration(candidate, cited, earliest)
            if then is None:
                continue
            again = self.declaration(candidate, cited, blamed)
            if names_in_code(unit, then) or then == again:
                options.append((candidate, then))
            else:
                doubts.append(f"`{then}` when written ({(earliest or '?')[:8]}), `{again}` at the "
                              f"line's last edit ({blamed[:8]}) in {candidate}")
        file = options[0][0] if len(options) == 1 else None
        if file is None:
            reason = (f"several files fit: {', '.join(c for c, _ in options)}" if options
                      else "; ".join(doubts) if doubts
                      else f"no declaration held line {cited} when the citation was written")
            result.left.append(Left(doc, number, content, reason))
            return None, None
        declaration = options[0][1]
        home = self.home(file, declaration)
        if home is None:
            result.left.append(Left(doc, number, content, f"`{declaration}` is no longer declared in {file}"))
            return None, (file, earliest, blamed)
        follow = (file, earliest, blamed)
        if names_in_code(unit, declaration):
            result.count("paragraph")
            return f"`{home}`", follow
        result.left.append(Left(doc, number, content, f"history alone names `{declaration}` (`{home}`): "
                                                     f"confirm it by hand"))
        result.history.append(Left(doc, number, content, f"`{declaration}` (`{home}`)"))
        return None, follow

    def rewrite_named(self, doc: str, number: int, content: str, name: str, candidates: list[str],
                      result: Result) -> str | None:
        heads = {c: self.file_at(ZERO, c) for c in candidates}
        declaring = [c for c, text in heads.items() if text is not None and c.endswith(".lean") and declares(text, name)]
        if len(declaring) != 1:
            declaring = [c for c, text in heads.items() if text is not None and mentions(text, name)]
        if len(declaring) == 1:
            result.count("named")
            return f"`{declaring[0]}`"
        if not declaring and all(c.endswith(".lean") for c in candidates):
            home = self.moved(name, "")
            if home is not None:
                result.count("named")
                return f"`{home}`"
        reason = (f"several files hold `{name}`: {', '.join(declaring)}" if declaring
                  else f"`{name}` is in no candidate file at HEAD: {', '.join(candidates)}")
        result.left.append(Left(doc, number, content, reason))
        return None

    def rewrite_continuation(self, doc: str, number: int, unit: str, before: str, content: str,
                             current: tuple[str, str | None, str], result: Result) -> str | None:
        """`name` (`:N`) becomes `name` (`file`); a bare `:N` whose declaration the paragraph names
        is dropped with its separator (the empty replacement); any other is left."""
        file, earliest, blamed = current
        named = NAMED_BEFORE.search(before)
        if named:
            head = self.file_at(ZERO, file)
            if head is not None and mentions(head, named.group("name")):
                result.count("continuation")
                return f"`{file}`"
            result.left.append(Left(doc, number, content, f"`{named.group('name')}` is not in {file} at HEAD"))
            return None
        cited = content.lstrip(":")
        then = self.declaration(file, cited, earliest)
        if then is None or not names_in_code(unit, then):
            reason = (f"history alone names `{then}`: confirm it by hand" if then is not None
                      else f"no declaration held line {cited} of {file} when it was cited")
            result.left.append(Left(doc, number, content, reason))
            return None
        if self.home(file, then) != file:
            result.left.append(Left(doc, number, content, f"`{then}` is no longer declared in {file}"))
            return None
        result.count("continuation")
        return ""

    def home(self, file: str, declaration: str) -> str | None:
        """Where `declaration` is declared at HEAD: `file`, or the one file it moved to."""
        head = self.file_at(ZERO, file)
        if head is not None and declares(head, declaration):
            return file
        return self.moved(declaration, file)

    def declaration(self, path: str, cited: str, revision: str | None) -> str | None:
        if revision is None:
            return None
        text = self.file_at(revision, path)
        return None if text is None else declaration_of(text, cited_lines(cited))


def git_file_at(root: Path) -> Callable[[str, str], str | None]:
    cache: dict[tuple[str, str], str | None] = {}

    def file_at(revision: str, path: str) -> str | None:
        key = (revision, path)
        if key not in cache:
            if revision == ZERO:
                target = root / path
                cache[key] = target.read_text(errors="replace") if target.is_file() else None
            else:
                shown = subprocess.run(["git", "show", f"{revision}:{path}"], cwd=root,
                                       capture_output=True, text=True, errors="replace")
                cache[key] = shown.stdout if shown.returncode == 0 else None
        return cache[key]
    return file_at


def git_blame(root: Path) -> Callable[[str], dict[int, str]]:
    def blame(doc: str) -> dict[int, str]:
        out = subprocess.run(["git", "blame", "--porcelain", "--", doc], cwd=root,
                             capture_output=True, text=True, errors="replace")
        revisions: dict[int, str] = {}
        if out.returncode != 0:
            return revisions
        for row in out.stdout.split("\n"):
            match = re.match(r"^([0-9a-f]{40}) \d+ (\d+)", row)
            if match:
                revisions[int(match.group(2))] = match.group(1)
        return revisions
    return blame


def git_first_seen(root: Path) -> Callable[[str, int], str | None]:
    """The earliest commit whose Markdown history adds a citation of a Lean file name and line:
    one pass over `git log -p --reverse` of every tracked Markdown file."""
    seen: dict[tuple[str, int], str] | None = None

    def first_seen(name: str, line: int) -> str | None:
        nonlocal seen
        if seen is None:
            seen = {}
            log = subprocess.run(["git", "log", "-p", "--reverse", "--no-color", "--format=commit %H",
                                  "--", "*.md"], cwd=root, capture_output=True, text=True, errors="replace")
            commit = ""
            for row in log.stdout.split("\n"):
                if row.startswith("commit "):
                    commit = row[7:].strip()
                elif row.startswith("+") and not row.startswith("+++"):
                    for match in HISTORY_CITE.finditer(row):
                        key = (os.path.basename(match.group(1)), int(match.group(2)))
                        seen.setdefault(key, commit)
        return seen.get((name, line))
    return first_seen
