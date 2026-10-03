"""language: the controlled-English checks of `docs/core/controlled-english.md`.

The specification is the one source. `load_spec(root)` reads, from that file only:

  - its dictionary tables (header `| Term | Meaning here | Tree anchor | Literature | Do not use |
    Qualifier |`): each term with its other forms, the words not to use instead of it, and its
    qualifier rule ("Every use:" or "First use:", then "in code" and quoted qualifier words);
  - its filler table (header `| Filler | Write instead |`);
  - its procedure verbs (the one-column table headed `| Procedure verbs |`);
  - its two sentence limits (the line that starts `Sentence limits:`).

`Checker.check(path, text)` returns the findings a reader can measure in one Markdown document,
one rule each:

  length     a sentence longer than its limit (procedural when it opens with a procedure verb)
  qualifier  a qualified word used without its qualifier in the same sentence
  avoid      a word the dictionary says not to use
  filler     a filler word
  line-cite  a line number in a citation of a file of this repository
  anchor     a name in a dictionary table that its cited file does not contain (the
             specification only)

Only prose is read. Fenced blocks, code spans, HTML comments and blockquotes are skipped; words
inside double quotes are mentions, not uses (a bold label that opens a list item, and an italic
title in title case, are mentions too); identifiers outside code (a name with `_`, `/`, `#`, an inner dot or inner capitals) are
never matched as words. Table cells are exempt from `length`, and the specification's
dictionary tables from every word rule.
"""
from __future__ import annotations

import os
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

SPEC = "docs/core/controlled-english.md"
DICT_HEADER = ["Term", "Meaning here", "Tree anchor", "Literature", "Do not use", "Qualifier"]
TREE_HEADER = ["Tree name (site)", "Literature name", "Mark", "The law that makes it that thing",
               "Correction applied"]
FILLER_HEADER = ["Filler", "Write instead"]
VERBS_HEADER = ["Procedure verbs"]
RULES = ("length", "qualifier", "avoid", "filler", "line-cite", "anchor")

# A line may be cited only where the file cannot move under the citation: the pinned vendored
# source (AGENTS.md requires its lines), the pinned toolchain and packages, and history.
PINNED_PREFIXES = ("vendor/", "Lean/", "Init/", "Std/", "Lake/", ".lake/", "docs/research/",
                   "Effects/", "plf/")
REPO_ROOTS = ("src", "docs", "Test", "tools", "scripts", "ts", "harness", "ocaml", "generated",
              "workshop", ".github")
CITED_EXTENSIONS = ("lean", "py", "sh", "ts", "tsx", "mjs", "js", "ml", "mli", "json", "toml",
                    "md", "txt", "yml", "yaml")
LINE_CITE = re.compile(r"^(?P<path>[\w@./+-]+\.(?:" + "|".join(CITED_EXTENSIONS) + r")):(?P<line>\d+)")
BARE_LINE = re.compile(r"^:\d+(?:[-–,]\d+)*$")
PROSE_LINE_CITE = re.compile(r"(?<![\w/.])([\w./-]+\.(?:lean|py|ts|sh|ml)):\d+")

ABBREVIATIONS = {"e.g", "i.e", "etc", "vs", "cf", "ch", "chs", "pp", "p", "al", "fig", "thm",
                 "def", "prop", "eq", "approx", "resp", "vol", "ed", "eds", "sec", "st", "dr",
                 "mr", "ms", "op", "cit", "ibid", "viz"}
PUNCTUATION_TOKEN = re.compile(r"^[\W_]+$")
CODE_SPAN = re.compile(r"(`+)(.+?)\1")
LINK = re.compile(r"!?\[([^\]]*)\]\((?:[^()\s]|\([^()]*\))*\)")
AUTOLINK = re.compile(r"<(?:https?|mailto):[^>]+>")
QUOTE = re.compile(r"\"[^\"\n]*\"|“[^”\n]*”")
ITALIC = re.compile(r"(?<![*\w])\*(?!\*)([^*\n]+?)(?<!\*)\*(?![*\w])")
RAW_LABEL = re.compile(r"^(\s*)(?:\*\*([^*]+)\*\*|__([^_]+)__)(\s*[:.—–-])")
QUOTED_LABEL = re.compile(r"^\s*(?:\"[^\"]*\"|“[^”]*”)\s*[:.—–-]\s*")
LIST_MARKER = re.compile(r"^(\s*)(?:[-*+]|\d+[.)])\s+")
HEADING = re.compile(r"^#{1,6}\s")
SEPARATOR = re.compile(r":?-{2,}:?")
SENTENCE_END = re.compile(r"[.!?][\"”')\]]*(?=\s+[A-Z0-9\"“(⟨\[*_#§])")
CODE_TOKEN = "⟨code⟩"
QUOTE_TOKEN = "⟨quote⟩"


@dataclass
class Entry:
    term: str
    forms: list[str]
    avoid: list[str]
    scope: str | None          # "every", "first" or None
    qualifiers: list[str]
    code_ok: bool
    line: int


@dataclass
class Spec:
    entries: list[Entry]
    fillers: list[tuple[str, str]]
    verbs: set[str]
    descriptive: int
    procedural: int


@dataclass
class Finding:
    path: str
    line: int
    rule: str
    text: str
    hint: str = ""

    def render(self) -> str:
        hint = f" ({self.hint})" if self.hint else ""
        return f"{self.path}:{self.line}: {self.rule}: {self.text}{hint}"


@dataclass
class Unit:
    kind: str                  # "para", "item", "heading", "cell"
    lines: list[tuple[int, str]] = field(default_factory=list)
    table: str = ""            # for a cell: "dict", "tree", "filler", "verbs", or "" for any other table
    column: int = -1
    row: str = ""              # for a cell: its whole row, the context a qualifier may stand in


# ------------------------------------------------------------------------------- blocks

def split_cells(row: str) -> list[str]:
    """The cells of a table row; a `|` inside a code span or escaped as `\\|` is not a border."""
    body = row.strip()
    if body.startswith("|"):
        body = body[1:]
    if body.endswith("|") and not body.endswith("\\|"):
        body = body[:-1]
    cells: list[str] = []
    current: list[str] = []
    in_code = False
    i = 0
    while i < len(body):
        ch = body[i]
        if ch == "\\" and i + 1 < len(body) and body[i + 1] == "|":
            current.append("|")
            i += 2
            continue
        if ch == "`":
            in_code = not in_code
        if ch == "|" and not in_code:
            cells.append("".join(current).strip())
            current = []
        else:
            current.append(ch)
        i += 1
    cells.append("".join(current).strip())
    return cells


def is_separator(cells: list[str]) -> bool:
    return all(SEPARATOR.fullmatch(c.replace(" ", "")) for c in cells if c)


def units(text: str) -> list[Unit]:
    """The prose units of a Markdown text (paragraphs, list items, headings, table cells), each
    with its source lines; fences, HTML comments and blockquotes are dropped."""
    out: list[Unit] = []
    current: Unit | None = None
    fence: str | None = None
    comment = False
    header: list[str] | None = None
    kind = ""

    def close() -> None:
        nonlocal current
        if current is not None and current.lines:
            out.append(current)
        current = None

    for number, raw in enumerate(text.split("\n"), start=1):
        stripped = raw.strip()
        if fence is not None:
            if stripped.startswith(fence):
                fence = None
            continue
        if comment:
            if "-->" in stripped:
                comment = False
            continue
        if stripped.startswith("```") or stripped.startswith("~~~"):
            close()
            header = None
            fence = stripped[:3]
            continue
        if stripped.startswith("<!--"):
            close()
            comment = "-->" not in stripped
            continue
        if not stripped:
            close()
            header = None
            continue
        if stripped.startswith("|"):
            close()
            cells = split_cells(stripped)
            if is_separator(cells):
                continue
            if header is None:
                header = cells
                kind = ("dict" if cells == DICT_HEADER else "tree" if cells == TREE_HEADER
                        else "filler" if cells == FILLER_HEADER
                        else "verbs" if cells == VERBS_HEADER else "")
                continue
            for column, cell in enumerate(cells):
                if cell:
                    out.append(Unit("cell", [(number, cell)], kind, column, " ; ".join(cells)))
            continue
        header = None
        if stripped.startswith(">"):
            close()
            continue
        if HEADING.match(stripped):
            close()
            out.append(Unit("heading", [(number, stripped.lstrip("#").strip())]))
            continue
        marker = LIST_MARKER.match(raw)
        if marker:
            close()
            current = Unit("item", [(number, raw[marker.end():])])
            continue
        if current is None:
            current = Unit("para")
        current.lines.append((number, stripped))
    close()
    return out


# ------------------------------------------------------------------------------- prose

def is_identifier(token: str) -> bool:
    """A name, not a word: it holds `_`, `/`, `#`, `@`, an inner dot, inner capitals, or a
    hyphen beside digits or capitals (`E4-TYPED-CE-030`)."""
    core = token.strip(".,;:!?()[]{}'\"“”‘’*")
    if not core:
        return False
    if any(ch in core for ch in "_/#@") or "::" in core:
        return True
    if re.search(r"\w\.\w", core):
        return True
    if re.search(r"[a-z][A-Z]", core) or re.search(r"[A-Z].*[A-Z].*[a-z]", core):
        return True
    return "-" in core and bool(re.search(r"[0-9A-Z]", core)) and not core.isupper()


def names_declaration(token: str) -> bool:
    """An identifier written without backticks that still names a declaration: `fits_subN`,
    `Ty.subN`, `Effect4.Program.Typed.Fits`, `cataFam`. A capitalized word alone (`TypeScript`,
    `OCaml`) does not count; write a declaration in code (W13)."""
    core = token.strip(".,;:!?()[]{}'\"“”‘’*")
    return ("_" in core or bool(re.fullmatch(r"[A-Z]\w*(?:\.[A-Za-z]\w*)+", core))
            or bool(re.fullmatch(r"[a-z][a-z0-9]*[A-Z]\w*", core)))


def title_mention(match: re.Match[str]) -> str:
    """An italic span in title case (two capitalized words or more) is a title: a mention."""
    words = match.group(1).split()
    capitalized = sum(1 for w in words if w[:1].isupper())
    return f"\"{match.group(1)}\"" if len(words) >= 2 and capitalized >= 2 else match.group(0)


def prose_line(line: str, first: bool) -> str:
    """One source line as prose: a code span becomes one placeholder word, a link its text, an
    opening bold label or an italic title a quoted mention; emphasis markers go."""
    if first:
        line = RAW_LABEL.sub(lambda m: f"{m.group(1)}\"{m.group(2) or m.group(3)}\"{m.group(4)}", line)
    line = AUTOLINK.sub(" ", line)
    line = CODE_SPAN.sub(CODE_TOKEN, line)
    line = LINK.sub(lambda m: m.group(1), line)
    line = ITALIC.sub(title_mention, line)
    return re.sub(r"\*\*|__|(?<![\w*])\*(?=\S)|(?<=\S)\*(?![\w*])", "", line)


@dataclass
class Sentence:
    line: int
    words: int
    procedural: bool
    prose: str        # code and quotes as placeholders: where qualifiers are looked for
    plain: str        # identifiers removed as well: where terms are looked for
    has_code: bool


def make_sentence(piece: str, line: int, verbs: set[str]) -> Sentence:
    tokens = [t for t in piece.split() if CODE_TOKEN in t or not PUNCTUATION_TOKEN.match(t)]
    opening = QUOTED_LABEL.sub("", piece).lstrip(" (\"“").split()
    head = opening[0].strip(",.:;").lower() if opening else ""
    pair = " ".join(w.strip(",.:;").lower() for w in opening[:2])
    procedural = head in verbs or head in ("never", "always") or pair in ("do not", "don't")
    prose = QUOTE.sub(QUOTE_TOKEN, piece)
    plain = " ".join(t for t in prose.split() if not is_identifier(t))
    named = CODE_TOKEN in piece or any(names_declaration(t) for t in prose.split())
    return Sentence(line, len(tokens), procedural, prose, plain, named)


def sentences_of(unit: Unit, verbs: set[str]) -> list[Sentence]:
    joined = ""
    offsets: list[tuple[int, int]] = []
    for index, (number, line) in enumerate(unit.lines):
        offsets.append((len(joined), number))
        joined += prose_line(line, index == 0) + " "
    out: list[Sentence] = []
    start = 0
    ends = [m.end() for m in SENTENCE_END.finditer(joined)] + [len(joined)]
    for end in ends:
        piece = joined[start:end]
        if end != len(joined):
            last = re.search(r"(\S+)[.!?][\"”')\]]*$", piece)
            word = last.group(1).strip("(\"“[") if last else ""
            if word.lower() in ABBREVIATIONS or re.fullmatch(r"[A-Za-z]", word):
                continue
        if piece.strip():
            at = start + len(piece) - len(piece.lstrip())
            line = unit.lines[0][0]
            for offset, number in offsets:
                if offset <= at:
                    line = number
            out.append(make_sentence(piece.strip(), line, verbs))
        start = end
    return out


# ------------------------------------------------------------------------------- the spec

def form_pattern(form: str) -> re.Pattern[str]:
    words = [re.escape(w) for w in form.split()]
    return re.compile(r"(?<![\w-])" + r"\s+".join(words) + r"(?![\w-])", re.I)


def qualifier_pattern(word: str) -> re.Pattern[str]:
    """A qualifier may stand inside a hyphenated compound: "typed-module admission"."""
    escaped = re.escape(word).replace(re.escape("<n>"), r"\d+")
    return re.compile(r"(?<!\w)" + escaped + r"(?!\w)", re.I)


def quoted(cell: str) -> list[str]:
    return [q.strip() for pair in re.findall(r"\"([^\"]+)\"|“([^”]+)”", cell) for q in pair if q.strip()]


def parse_term(cell: str) -> tuple[str, list[str]]:
    """`**term** (form, form)`: the bold head and the forms in the parentheses after it."""
    head = re.search(r"\*\*([^*]+)\*\*", cell)
    term = head.group(1).strip() if head else cell.strip()
    rest = cell[head.end():] if head else ""
    forms = [term]
    others = re.match(r"\s*\(([^)]*)\)", rest)
    if others:
        forms += [f.strip() for f in others.group(1).split(",") if f.strip()]
    return term, forms


def load_spec(root: Path) -> Spec:
    text = (root / SPEC).read_text()
    entries: list[Entry] = []
    fillers: list[tuple[str, str]] = []
    verbs: set[str] = set()
    descriptive, procedural = 25, 20
    header: list[str] | None = None
    fence = False
    for number, raw in enumerate(text.split("\n"), start=1):
        stripped = raw.strip()
        if stripped.startswith("```"):
            fence = not fence
            continue
        if fence:
            continue
        limits = re.match(r"Sentence limits:\s*(\d+)\D+(\d+)", stripped)
        if limits:
            descriptive, procedural = int(limits.group(1)), int(limits.group(2))
        if not stripped.startswith("|"):
            header = None
            continue
        cells = split_cells(stripped)
        if is_separator(cells):
            continue
        if header is None:
            header = cells
            continue
        if header == DICT_HEADER and len(cells) == len(DICT_HEADER):
            term, forms = parse_term(cells[0])
            rule = cells[5]
            scope = ("every" if rule.startswith("Every use:") else
                     "first" if rule.startswith("First use:") else None)
            entries.append(Entry(term, forms, quoted(cells[4]), scope,
                                 quoted(rule) if scope else [],
                                 scope is not None and "in code" in rule, number))
        elif header == FILLER_HEADER and len(cells) == 2:
            fillers.extend((word, cells[1]) for word in quoted(cells[0]))
        elif header == VERBS_HEADER and len(cells) == 1:
            verbs.update(w.strip(" .`").lower() for w in cells[0].split(",") if w.strip(" .`"))
    return Spec(entries, fillers, verbs, descriptive, procedural)


# ------------------------------------------------------------------------------- anchors

def anchors(cell: str) -> list[tuple[str, str]]:
    """The (name, path) pairs of a cell: a code-span path written in parentheses anchors the
    code-span names written before it, back to the previous such path."""
    pairs: list[tuple[str, str]] = []
    names: list[str] = []
    for match in CODE_SPAN.finditer(cell):
        content = match.group(2).strip()
        before = cell[:match.start()].rstrip()
        after = cell[match.end():].lstrip()
        if "/" in content and before.endswith("(") and after[:1] in (")", ",", ";"):
            pairs.extend((name, content) for name in names)
            names = []
        elif "/" not in content and " " not in content:
            names.append(content)
    return pairs


def declared_word(name: str) -> str:
    """The word a file must contain for `name`: its last component, without `.`, `#` or `%`."""
    word = name.lstrip(".#").rstrip("%")
    return word.split(".")[-1] if "." in word else word


# ------------------------------------------------------------------------------- checks

class Checker:
    def __init__(self, root: Path, spec: Spec):
        self.root = root
        self.spec = spec
        listed = subprocess.run(["git", "ls-files"], cwd=root, capture_output=True, text=True).stdout.split("\n")
        self.tracked = [p for p in listed if p]
        self.basenames = {os.path.basename(p) for p in self.tracked if not p.startswith("vendor/")}
        self.terms = [(e, [form_pattern(f) for f in e.forms]) for e in spec.entries if e.scope]
        self.qualifiers = {id(e): [qualifier_pattern(q) for q in e.qualifiers] for e in spec.entries}
        self.avoid = [(form_pattern(w), e.term) for e in spec.entries for w in e.avoid]
        self.fillers = [(form_pattern(w), instead) for w, instead in spec.fillers]

    def ours(self, path: str) -> bool:
        """A file of this repository whose lines can move: not pinned, and either written from
        the root or a suffix of a tracked path."""
        if path.startswith(PINNED_PREFIXES):
            return False
        if path.startswith(tuple(r + "/" for r in REPO_ROOTS)) or path in self.tracked:
            return True
        if "/" not in path:
            return path in self.basenames
        return any(p.endswith("/" + path) for p in self.tracked if not p.startswith("vendor/"))

    def line_cites(self, path: str, unit: Unit) -> list[Finding]:
        hint = "cite the declaration by name and path, without a line"
        findings: list[Finding] = []
        last_ours = False
        for number, line in unit.lines:
            for match in CODE_SPAN.finditer(line):
                content = match.group(2).strip()
                cite = LINE_CITE.match(content)
                if cite:
                    last_ours = self.ours(cite.group("path"))
                    if last_ours:
                        findings.append(Finding(path, number, "line-cite", f"`{content}`", hint))
                elif BARE_LINE.match(content) and last_ours:
                    findings.append(Finding(path, number, "line-cite", f"`{content}`", hint))
            for match in PROSE_LINE_CITE.finditer(CODE_SPAN.sub(" ", line)):
                if self.ours(match.group(1)):
                    findings.append(Finding(path, number, "line-cite", match.group(0), hint))
        return findings

    def anchor_findings(self, path: str, unit: Unit) -> list[Finding]:
        findings: list[Finding] = []
        number, cell = unit.lines[0]
        for name, cited in anchors(cell):
            if not cited.startswith(tuple(r + "/" for r in REPO_ROOTS)):
                continue
            target = self.root / cited
            if not target.is_file():
                findings.append(Finding(path, number, "anchor", f"`{name}` (`{cited}`)", "no such file"))
                continue
            word = declared_word(name)
            if not re.search(r"(?<![\w'])" + re.escape(word) + r"(?![\w'])", target.read_text(errors="replace")):
                findings.append(Finding(path, number, "anchor", f"`{name}` (`{cited}`)",
                                        f"the file does not contain {word}"))
        return findings

    def check(self, path: str, text: str) -> list[Finding]:
        findings: list[Finding] = []
        seen_first: set[str] = set()
        for unit in units(text):
            findings.extend(self.line_cites(path, unit))
            if unit.kind == "cell" and unit.table and path == SPEC:
                if (unit.table, unit.column) in (("dict", 2), ("tree", 0)):
                    findings.extend(self.anchor_findings(path, unit))
                continue
            row = None
            if unit.kind == "cell":
                row = make_sentence(prose_line(unit.row, False), unit.lines[0][0], self.spec.verbs)
            for sentence in sentences_of(unit, self.spec.verbs):
                if unit.kind in ("para", "item"):
                    limit = self.spec.procedural if sentence.procedural else self.spec.descriptive
                    if sentence.words > limit:
                        kind = "procedural" if sentence.procedural else "descriptive"
                        findings.append(Finding(path, sentence.line, "length",
                                                f"{sentence.words} words > {limit} ({kind})",
                                                excerpt(sentence.prose)))
                findings.extend(self.word_findings(path, sentence, seen_first, row))
        return sorted(findings, key=lambda f: (f.line, RULES.index(f.rule)))

    def word_findings(self, path: str, sentence: Sentence, seen_first: set[str],
                      row: Sentence | None = None) -> list[Finding]:
        """The word rules on one sentence. In a table cell the qualifier may stand anywhere in
        the cell's row: a role label and its theorem sit in neighbouring cells."""
        findings: list[Finding] = []
        context = row or sentence
        for entry, patterns in self.terms:
            hit = next((m for p in patterns for m in [p.search(sentence.plain)] if m), None)
            if hit is None:
                continue
            if entry.scope == "first":
                if entry.term in seen_first:
                    continue
                seen_first.add(entry.term)
            qualified = (entry.code_ok and (sentence.has_code or context.has_code)) or any(
                q.search(sentence.prose) or q.search(context.prose) for q in self.qualifiers[id(entry)])
            if not qualified:
                which = "first use" if entry.scope == "first" else "use"
                findings.append(Finding(path, sentence.line, "qualifier",
                                        f"\"{hit.group(0)}\" ({which} of {entry.term}) without its qualifier",
                                        excerpt(sentence.prose)))
        for pattern, term in self.avoid:
            for match in pattern.finditer(sentence.plain):
                findings.append(Finding(path, sentence.line, "avoid", f"\"{match.group(0)}\"", f"write {term}"))
        for pattern, instead in self.fillers:
            for match in pattern.finditer(sentence.plain):
                hint = "delete it" if instead in ("—", "-", "") else f"write {instead}"
                findings.append(Finding(path, sentence.line, "filler", f"\"{match.group(0)}\"", hint))
        return findings


def excerpt(text: str, width: int = 72) -> str:
    flat = " ".join(text.split())
    return flat if len(flat) <= width else flat[: width - 1] + "…"
