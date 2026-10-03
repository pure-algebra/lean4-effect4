"""doc_refs: the references the Markdown authorities make, and which of them are stale.

A reference is a Markdown link target, an inline-code path (`src/Effect4/Program/Ty.lean`,
`docs/core/decisions.md`, `scripts/generate.py`, ...), a `git:<rev>:<path>` citation, or a
`make <target>`. `stale_references(root)` returns the ones that do not resolve: a path that does
not exist (resolved against the repository root, then against the document's directory), a
citation that names no object in the repository's history, a make target the Makefile does not
define. Fenced code blocks are read for make targets only. A missing path with a unique tracked
namesake gets that file suggested.

The documents are every tracked Markdown file that is not history: not docs/research/, vendor/,
the archived registers and contracts, or the attack logs.
"""
from __future__ import annotations

import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

PATH_ROOTS = ("src", "docs", "Test", "tools", "scripts", "ts", "harness", "ocaml", "generated",
              "vendor", "workshop", ".github")
HISTORY = ("docs/research/", "vendor/", "Test/Counterexamples/Archive/", "Test/contracts/archive/")
SKIP_CHARS = set("*<>{}|…?$ \t\"'")
LINK = re.compile(r"\[[^\]]*\]\(([^)\s]+)(?:\s+\"[^\"]*\")?\)")
CODE = re.compile(r"`([^`]+)`")
GIT_CITE = re.compile(r"^git:([0-9a-fA-F]{6,40}):(.+)$")
MAKE = re.compile(r"\bmake(?:\s+-[A-Za-z]+)*\s+([a-z][a-z0-9_-]*)")
PLAIN_TARGETS = {"check", "build", "gen", "help", "clean", "corpus", "doctor", "status"}


@dataclass
class Stale:
    file: str
    line: int
    kind: str
    text: str
    hint: str = ""

    def render(self) -> str:
        hint = f"  ({self.hint})" if self.hint else ""
        return f"{self.file}:{self.line}: {self.kind} {self.text}{hint}"


def git_lines(root: Path, *args: str) -> list[str]:
    out = subprocess.run(["git", *args], cwd=root, check=True, capture_output=True, text=True).stdout
    return [line for line in out.split("\n") if line]


def doc_files(root: Path) -> list[str]:
    """Every tracked Markdown file that is not history: the research notes, the vendored sources,
    the archived registers and contracts, and the attack logs (`ATTACKS.md`) are not checked."""
    return [path for path in git_lines(root, "ls-files", "--", "*.md")
            if not path.startswith(HISTORY) and not path.endswith("/ATTACKS.md")]


def makefile_targets(root: Path) -> tuple[set[str], list[str], list[str]]:
    """The Makefile's literal targets, plus `check-<x>` / `gen-<x>` from its lists; the `%` rules;
    the committed generated paths (`GENERATED_PATHS`)."""
    text = (root / "Makefile").read_text()
    text = re.sub(r"\\\n", " ", text)
    targets: set[str] = set()
    patterns: list[str] = []
    variables: dict[str, str] = {}
    for line in text.split("\n"):
        assignment = re.match(r"^([A-Z_]+)\s*[:?]?=\s*(.*)$", line)
        if assignment:
            variables[assignment.group(1)] = assignment.group(2)
            continue
        rule = re.match(r"^([^\s:#=][^:#=]*?):(?!=)", line)
        if not rule:
            continue
        for name in rule.group(1).split():
            if "$(" in name or name.startswith("."):
                continue
            if "%" in name:
                patterns.append(name)
            else:
                targets.add(name)
    for prefix, variable in (("check-", "CHECKS"), ("gen-", "GEN_GROUPS")):
        for name in variables.get(variable, "").split():
            if "$(" not in name:
                targets.add(prefix + name)
    generated = [p for p in variables.get("GENERATED_PATHS", "").split() if "$(" not in p]
    return targets, patterns, generated


def matches_pattern(name: str, patterns: list[str]) -> bool:
    for pattern in patterns:
        head, _, tail = pattern.partition("%")
        if name.startswith(head) and name.endswith(tail) and len(name) >= len(head) + len(tail):
            return True
    return False


class Checker:
    def __init__(self, root: Path):
        self.root = root
        self.tracked = set(git_lines(root, "ls-files"))
        self.by_name: dict[str, list[str]] = {}
        for path in self.tracked:
            self.by_name.setdefault(os.path.basename(path), []).append(path)
        self.targets, self.patterns, self.generated = makefile_targets(root)
        self.citations: dict[str, list[Stale]] = {}
        self.missing: list[Stale] = []
        self.stale: list[Stale] = []

    def is_generated(self, doc: str) -> bool:
        """Listed exactly in `GENERATED_PATHS`, or carrying the `GENERATED` header mark."""
        if doc in self.generated:
            return True
        with open(self.root / doc, encoding="utf-8", errors="replace") as handle:
            head = "".join(handle.readline() for _ in range(3))
        return "GENERATED" in head

    def exists(self, relative: str) -> bool:
        return (self.root / relative).exists()

    def resolve(self, target: str, doc: str) -> bool:
        """`target` exists at the root, or relative to the document's directory; a module path
        may omit `.lean`; a path git ignores is a build artifact and resolves, except under
        docs/research/, where a cited note must be tracked (force-added)."""
        if target.startswith("docs/research/"):
            return target.rstrip("/") in self.tracked or any(
                path.startswith(target.rstrip("/") + "/") for path in self.tracked)
        if self.exists(target) or ("." not in os.path.basename(target) and self.exists(target + ".lean")):
            return True
        relative = os.path.normpath(os.path.join(os.path.dirname(doc), target))
        return self.exists(relative)

    def check_missing(self) -> None:
        """One `git check-ignore` over every missing path: an ignored one is a build artifact and
        resolves; a research note is never excused this way (it must be tracked)."""
        if not self.missing:
            return
        candidates = sorted({s.text for s in self.missing if not s.text.startswith("docs/research/")})
        ignored: set[str] = set()
        if candidates:
            out = subprocess.run(["git", "check-ignore", "--stdin"], cwd=self.root,
                                 input="\n".join(candidates) + "\n", capture_output=True, text=True).stdout
            ignored = {line for line in out.split("\n") if line}
        self.stale.extend(s for s in self.missing if s.text not in ignored)

    def hint_for(self, target: str, doc: str) -> str:
        where = "; the document is generated, repair its producer" if self.is_generated(doc) else ""
        if target.startswith("docs/research/"):
            return ("untracked research note: git add -f it" if self.exists(target) else "missing") + where
        name = os.path.basename(target.rstrip("/"))
        namesakes = self.by_name.get(name, [])
        if len(namesakes) == 1:
            return f"moved? {namesakes[0]}" + where
        if len(namesakes) > 1:
            return f"{len(namesakes)} tracked files are named {name}" + where
        return "missing" + where

    def check_citations(self) -> None:
        """One `git cat-file --batch-check` over every citation; a missing object is stale."""
        if not self.citations:
            return
        keys = "\n".join(self.citations) + "\n"
        out = subprocess.run(["git", "cat-file", "--batch-check"], cwd=self.root, input=keys,
                             capture_output=True, text=True).stdout
        for line in out.split("\n"):
            if line.endswith(" missing"):
                key = line[: -len(" missing")]
                self.stale.extend(self.citations.get(key, []))

    def check_target(self, doc: str, line_no: int, target: str, kind: str) -> None:
        target = target.strip()
        if not target or target.startswith(("http://", "https://", "mailto:", "#", "<")):
            return
        cite = GIT_CITE.match(target)
        if cite:
            key = f"{cite.group(1)}:{cite.group(2)}"
            self.citations.setdefault(key, []).append(
                Stale(doc, line_no, kind, target, "no such object in history"))
            return
        target = target.split("#", 1)[0]
        if not target or any(ch in SKIP_CHARS for ch in target):
            return
        if not self.resolve(target, doc):
            self.missing.append(Stale(doc, line_no, kind, target, self.hint_for(target, doc)))

    def check_code_span(self, doc: str, line_no: int, token: str) -> None:
        token = token.strip().rstrip(".,;:")
        token = re.sub(r":[0-9][0-9,\-–]*$", "", token)
        if not token or any(ch in SKIP_CHARS for ch in token) or GIT_CITE.match(token):
            if GIT_CITE.match(token):
                self.check_target(doc, line_no, token, "citation")
            return
        if "/" not in token:
            return
        head = token.split("/", 1)[0]
        if head not in PATH_ROOTS and not token.startswith(("./", "../")):
            return
        if token.endswith("/"):
            if not self.resolve(token, doc):
                self.missing.append(Stale(doc, line_no, "path", token, "no such directory"))
            return
        self.check_target(doc, line_no, token, "path")

    def check_make(self, doc: str, line_no: int, line: str) -> None:
        for match in MAKE.finditer(line):
            name = match.group(1)
            if line[match.end():match.end() + 1] == "<":
                continue  # a placeholder: `make gen-<group>`
            if "-" not in name and name not in PLAIN_TARGETS:
                continue
            if name in self.targets or matches_pattern(name, self.patterns):
                continue
            self.stale.append(Stale(doc, line_no, "make target", f"make {name}", "not in the Makefile"))

    def check_doc(self, doc: str) -> None:
        fenced = False
        for line_no, line in enumerate((self.root / doc).read_text().split("\n"), start=1):
            stripped = line.lstrip()
            if stripped.startswith("```") or stripped.startswith("~~~"):
                fenced = not fenced
                continue
            self.check_make(doc, line_no, line)
            if fenced:
                continue
            for match in CODE.finditer(line):
                self.check_code_span(doc, line_no, match.group(1))
            for match in LINK.finditer(CODE.sub(" ", line)):
                self.check_target(doc, line_no, match.group(1), "link")


def stale_references(root: Path) -> list[Stale]:
    checker = Checker(root)
    for doc in doc_files(root):
        checker.check_doc(doc)
    checker.check_citations()
    checker.check_missing()
    return sorted(checker.stale, key=lambda s: (s.file, s.line, s.text))
