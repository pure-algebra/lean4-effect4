#!/usr/bin/env python3
"""Check existence of explicit repository-relative citation paths (not line ranges).

Properties: deterministic inventory and baseline; new missing targets refuse; removing
a target invalidates a stamp even if it is outside the scanned source trees. Synthetic
fixtures resolve against their own tree. Revision-qualified `git:<rev>:<path>` citations
resolve against their immutable git tree. Untracked research notes must be
marked as such in authority documents; they are not live source dependencies.
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


def inspect(root: Path):
    digest = hashlib.sha256()
    missing: dict[str, list[str]] = {}
    tokens = 0
    notes = []
    histories = {}
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
        if b"\0" in data or rel in (BASELINE, ALLOW) or rel.startswith("Test/fixtures/internal-citations/tree/"):
            continue
        text = data.decode("utf-8", errors="replace")
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
                               "docs/DESIGN-BASIS.md", "docs/RUNTIME-COVERAGE.md"}:
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
    return digest, missing, tokens, notes


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--update-baseline", action="store_true")
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--list-missing", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    digest, missing, tokens, notes = inspect(root)
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
    digest.update("\n".join(sorted(baseline)).encode())
    key = digest.hexdigest()
    summary = f"{tokens} citation tokens examined; {len(missing)} baselined missing targets"
    if root == Path(__file__).resolve().parent.parent:
        stamp_dir = root / ".lake/stamps/source-citations"
        stamp = stamp_dir / key
        if stamp.exists() and not args.force and os.environ.get("EFFECT4_FORCE") != "1":
            print(f"PASS source-citations: {summary}; skipped (EFFECT4_FORCE=1 re-runs)")
            return 0
        stamp_dir.mkdir(parents=True, exist_ok=True)
        for old in stamp_dir.iterdir():
            if old.is_file():
                old.unlink()
        stamp.write_text(summary + "\n")
    print(f"PASS source-citations: {summary}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
