#!/usr/bin/env python3
"""The citation gate: one walk of the source trees, two questions about every line.

1. EXISTENCE. Every explicit repository-relative citation path (not line ranges) resolves.
   Deterministic inventory and baseline; new missing targets refuse; removing a target
   invalidates a stamp even if it is outside the scanned source trees. Synthetic fixtures
   resolve against their own tree. Revision-qualified `git:<rev>:<path>` citations resolve
   against their immutable git tree. Untracked research notes must be marked as such in
   authority documents; they are not live source dependencies.

2. NO LINE CITATION INTO A MUTABLE AUTHORED DOCUMENT. A line citation into a pinned host
   source is stable: those files are third-party bytes identified by digest, never edited
   here. A line citation into one of this repository's own rulings is not: those documents
   are edited continuously, so a name plus a line number silently retargets whenever a
   section above it grows, and the citing sentence keeps asserting a claim the target no
   longer makes. That has happened here — a proof-graph reallocation moved five obligation
   rows and citations elsewhere were left pointing at unrelated prose with no file edited.
   Cite a section heading, an obligation id, a proof-graph node or a short quoted phrase.

   What a pass means: in the scanned trees, no citation names one of the protected documents
   together with a line number. What it does not mean: nothing about whether a replacement
   anchor exists, whether the target still says what the citing sentence claims, or whether
   any other citation is correct. It is a lexical scan, not a resolver. Three limits named
   rather than glossed: a bare continuation citation such as `:123` carries no document name
   and is invisible; the targets are matched exactly after stripping one leading `./`, so a
   different file with the same basename is a different target; and `vendor/`,
   `node_modules/`, `_copy/` and `research/` are pruned wherever they appear, because none of
   those trees is authored here.

Until 2026-09-18 these were two programs (`check-internal-citations.sh` did the second) and
`make check-citations` ran both, so every text file of the nine trees was read twice. They are
one pass now; the shell gate is retired and its seventeen-case reaction test drives this
script through `--internal-only`.

`--root` reports on a supplied tree. `--internal-only` runs question 2 alone, which is what a
synthetic tree can be asked: the existence baseline is about this repository.
"""
from __future__ import annotations

import argparse
from functools import cache
import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys

TREES = {"src", "Test", "tools", "ocaml", "ts", "docs", "scripts", "harness", "generated"}
PRUNE = {".git", ".lake", "_build", "node_modules", "_copy", "vendor", "research"}
ROOTS = "src/(?:Effect4|OCaml5|Tools)|Test|tools|ocaml|ts|docs|scripts|harness|generated|vendor|Effect4|Effect4Test|test|workshop|skills"
TOKEN = re.compile(rf"(?<![\w/.:=-])(?:\./)?(?:{ROOTS})/[\w./-]+\.(?:lean|ml|sh|md|ts|py|tsv|json)(?![\w.])")
GIT_TOKEN = re.compile(r"git:([0-9a-f]{7,40}):([\w./-]+\.(?:lean|ml|sh|md|ts|py|tsv|json))(?![\w.])")
BASELINE = "generated/citation-baseline.txt"
ALLOW = "scripts/source-citations-allowed.txt"
# Frozen host receipts retain the bytes recorded before the namespace move.
# Their paths resolve against the immutable pre-move tree and the reviewed pre-cleanup
# tree below. This existence check does not refresh their recorded host verdicts.
HISTORICAL = ("ocaml/avatar/out/", "ocaml/wasm/out/", "ocaml/probes/fuzz/corpus/",
              "ocaml/server/generated/", "Test/fixtures/traces/fiber-m3/")
HISTORICAL_FILES = {"ocaml/avatar/tools/witnesses-after.txt", "ocaml/avatar/tools/failfast-demo-native.txt"}
HISTORICAL_REVS = ("c407ab7", "d00cade")
# The mutable authored rulings, in both spellings a citation can use. Assembled rather than
# spelled where the target no longer exists, so this file carries no citation of its own to a
# path the existence half would then have to find.
RETIRED_ROUTER = "AGENT-" + "ROUTING.md"
PROTECTED = {
    "docs/research/SCHEMA-CUTOVER.md", "SCHEMA-CUTOVER.md",
    "PLAN.md", "AGENTS.md",
    "docs/ARCHITECTURE.md", "ARCHITECTURE.md",
    "docs/DESIGN-ISSUES.md", "DESIGN-ISSUES.md",
    "docs/DESIGN-MAP.md", "DESIGN-MAP.md",
    "docs/" + RETIRED_ROUTER, RETIRED_ROUTER,
}
LINE_TOKEN = re.compile(r"[A-Za-z0-9._/-]+\.[A-Za-z0-9]+:[0-9]+(?:-[0-9]+)?")


def inventory(root: Path) -> list[Path]:
    # Canonical source inventory: tracked files and unignored additions. Local installs,
    # archived harness caches and research notes are not part of a fresh checkout.
    if (root / ".git").exists():
        result = subprocess.run(["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
                                cwd=root, check=True, capture_output=True)
        return sorted({root / name for raw in result.stdout.split(b"\0") if raw
                       for name in [raw.decode("utf-8")]
                       if (name.split('/')[0] in TREES or name in
                           {"AGENTS.md", "README.md", "lakefile.toml",
                            ".claude/skills/runtime-coverage/SKILL.md"})
                       and not any(part in PRUNE for part in Path(name).parts)
                       and (root / name).is_file()})
    paths = []
    for tree in sorted(TREES):
        for parent, dirs, files in os.walk(root / tree):
            dirs[:] = sorted(d for d in dirs if d not in PRUNE)
            paths.extend(Path(parent) / f for f in sorted(files))
    paths.extend(root / p for p in ("AGENTS.md", "README.md", "lakefile.toml",
                                   ".claude/skills/runtime-coverage/SKILL.md") if (root / p).is_file())
    return sorted(paths)


def inspect(root: Path, internal_only: bool = False):
    digest = hashlib.sha256()
    missing: dict[str, list[str]] = {}
    tokens = 0
    notes = []
    histories = {}
    line_tokens = 0
    violations: list[str] = []
    files = 0
    @cache
    def children(directory):
        return {entry.name for entry in directory.iterdir()}
    @cache
    def exact_file(path_text):
        # Cache strings: WindowsPath equality folds case, which would merge a miss
        # for the wrong spelling with a hit for the canonical spelling.
        path = Path(path_text)
        if not path.is_relative_to(root) or not path.is_file():
            return False
        # Enforce Linux spelling on Windows too; exists() alone is case-insensitive there.
        while path != root:
            if path.name not in children(path.parent):
                return False
            path = path.parent
        return True
    def historical_exists(revision, path):
        if revision not in histories:
            result = subprocess.run(["git", "ls-tree", "-r", "--name-only", revision],
                                    cwd=root, text=True, capture_output=True)
            histories[revision] = set(result.stdout.splitlines()) if result.returncode == 0 else set()
        return path in histories[revision]
    for file in inventory(root):
        rel = file.relative_to(root).as_posix()
        data = file.read_bytes()
        digest.update(rel.encode() + b"\0" + data + b"\0")
        if b"\0" in data or not data:
            continue
        text = data.decode("utf-8", errors="replace")
        files += 1
        # Question 2 reads every text file, the detector fixtures included: a violation in a
        # fixture is a violation, and the fixture trees are where the reaction test plants one.
        for n, line in enumerate(text.splitlines(), 1):
            for match in LINE_TOKEN.finditer(line):
                token = match.group()
                line_tokens += 1
                document = token.split(":", 1)[0].removeprefix("./")
                if document in PROTECTED:
                    violations.append(f"{rel} line {n} cites `{token}`; cite a section heading, "
                                      "obligation ID, proof-graph node, or quoted phrase instead")
        if internal_only or rel in (BASELINE, ALLOW) or rel.startswith("Test/fixtures/internal-citations/tree/"):
            continue
        # A detector fixture is an independent repository, not a citation into this one.
        fixture = re.search(r"Test/fixtures/[^/]+/tree/", rel)
        resolution_root = root / fixture.group() if fixture else root
        for n, line in enumerate(text.splitlines(), 1):
            for match in GIT_TOKEN.finditer(line):
                revision, path = match.groups()
                tokens += 1
                exists = historical_exists(revision, path)
                digest.update(match.group().encode() + bytes([exists]))
                if not exists:
                    missing.setdefault(match.group(), []).append(f"{rel}:{n}")
            for match in TOKEN.finditer(line):
                path = match.group().removeprefix("./")
                if path.startswith("docs/research/"):
                    if rel in {"AGENTS.md", "README.md", "docs/ARCHITECTURE.md",
                               "docs/DESIGN-BASIS.md", "docs/DESIGN-ISSUES.md", "docs/DESIGN-MAP.md",
                               "docs/RUNTIME-COVERAGE.md"}:
                        if "(untracked working note)" not in line:
                            notes.append(f"{rel}:{n}: {path} needs (untracked working note)")
                    continue
                tokens += 1
                # Package-local paths resolve from the citing
                # document's directory first; full src/ and Test/ paths stay root-relative.
                candidates = [resolution_root / path]
                if path.startswith(("tools/", "test/", "generated/")):
                    candidates += [parent / path for parent in file.parents if parent.is_relative_to(root)]
                exists = any(exact_file(str(candidate)) for candidate in candidates)
                if not exists and (rel.startswith(HISTORICAL) or rel in HISTORICAL_FILES):
                    exists = any(historical_exists(revision, path) for revision in HISTORICAL_REVS)
                digest.update(path.encode() + bytes([exists]))
                if not exists:
                    missing.setdefault(path, []).append(f"{rel}:{n}")
    return digest, missing, tokens, notes, line_tokens, violations, files


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--update-baseline", action="store_true")
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--list-missing", action="store_true")
    parser.add_argument("--internal-only", action="store_true",
                        help="run the protected-document scan alone (for a synthetic tree)")
    parser.add_argument("extra", nargs="*", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.extra:
        print(f"FAIL unexpected argument: {args.extra[0]}", file=sys.stderr)
        return 1
    root = args.root.resolve()
    if not root.is_dir():
        print(f"FAIL root is not a directory: {root}", file=sys.stderr)
        return 1
    here = Path(__file__).resolve().parent.parent
    present = [tree for tree in sorted(TREES) if (root / tree).is_dir()]
    if not present:
        print(f"FAIL none of the scanned trees ({' '.join(sorted(TREES))}) exist under {root}",
              file=sys.stderr)
        return 1
    digest, missing, tokens, notes, line_tokens, violations, files = inspect(root, args.internal_only)
    # The extraction-pattern tooth: a scan that finds no `path:line` token at all has stopped
    # matching. It is asked of this repository and of any tree the detector suite hands to
    # `--internal-only`; a foreign tree scanned in full mode may legitimately hold none, and the
    # result there already says it closes nothing here.
    if (args.internal_only or root == here) and not line_tokens:
        print("FAIL extracted no citation tokens at all; the extraction pattern no longer matches",
              file=sys.stderr)
        return 1
    if violations:
        print(f"FAIL {len(violations)} line-numbered citation(s) into a mutable authored document",
              file=sys.stderr)
        for violation in violations:
            print("FAIL " + violation, file=sys.stderr)
        return 1
    internal_pass = (
        f"PASS no line-numbered citation into the {len({p.rsplit(chr(47), 1)[-1] for p in PROTECTED})} protected authored documents\n"
        f"PASS {line_tokens} citation tokens examined in {files} files "
        f"across {len(present)} scanned tree(s)")
    if args.internal_only:
        print(internal_pass)
        if root != here:
            print("INFO scanned root is not this repository: " + str(root))
            print("INFO the result is about the supplied tree only and closes nothing here")
        else:
            print("NOTE lexical scan only; host-source, vendor/, and .lean line citations "
                  "are accepted unchecked")
        return 0
    allowed_file = root / ALLOW
    allowed_bytes = allowed_file.read_bytes() if allowed_file.exists() else b""
    digest.update(allowed_bytes)
    allowed = {line.split("\t")[0] for line in allowed_bytes.decode().splitlines()
               if line and not line.startswith("#")}
    missing = {p: refs for p, refs in missing.items() if p not in allowed}
    baseline_file = root / BASELINE
    if args.update_baseline:
        baseline_file.parent.mkdir(parents=True, exist_ok=True)
        baseline_file.write_text("# GENERATED by python3 scripts/check-source-citations.py --update-baseline\n"
                                 "# format=citation-baseline-v1; inputs=the scanned source inventory\n"
                                 + "\n".join(sorted(missing)) + "\n", encoding="utf-8", newline="\n")
        print(f"Baseline: {len(missing)} missing targets")
        return 0
    baseline = set()
    if baseline_file.exists():
        baseline = {s for s in baseline_file.read_text().splitlines() if s and not s.startswith("#")}
    if args.list_missing:
        for path, refs in sorted(missing.items()):
            print(path + "\t" + ", ".join(refs))
        return 0
    failures = notes + [f"missing {p}: {', '.join(missing[p])}" for p in sorted(missing.keys() - baseline)]
    if not tokens:
        failures.append("extracted no repository citation tokens")
    if failures:
        print("\n".join("FAIL source-citations: " + f for f in failures), file=sys.stderr)
        return 1
    summary = f"{tokens} citation tokens examined; {len(missing)} baselined missing targets"
    print(f"PASS source-citations: {summary}")
    print(internal_pass)
    if root != here:
        print("INFO scanned root is not this repository: " + str(root))
        print("INFO the result is about the supplied tree only and closes nothing here")
    else:
        print("NOTE lexical scan only; host-source, vendor/, and .lean line citations "
              "are accepted unchecked")
    return 0


if __name__ == "__main__":
    sys.exit(main())
