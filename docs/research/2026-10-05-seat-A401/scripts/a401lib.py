"""Seat A401 (2026-10-05): shared helpers of the rc.112 against 4.0.1 audit.

The inputs are four comment-stripped trees that `strip.mjs` writes (the source and the compiled
JavaScript of each build), their fact tables, and the two vendored source trees. Every path below
is relative to a tree root (`Queue.ts`, `internal/effect.ts`).

Vocabulary of this library:
  code line   a line of a comment-stripped file that is not blank, with its white space collapsed
              and its relative import paths rewritten to tree paths (so a moved file compares)
  hunk        a maximal run of code lines that the two builds do not share, from a line diff
"""
import json
import os
import posixpath
import re
import subprocess
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
PIN_SRC = os.path.join(REPO, "vendor", "effect-4.0.0-rc.112", "src")
REL_SRC = os.path.join(REPO, "vendor", "effect-4.0.1", "src")
SCRATCH = os.environ.get("A401_SCRATCH", "")


def scratch(*parts):
    if not SCRATCH:
        raise SystemExit("set A401_SCRATCH to the folder that holds stripped/ and the fact tables")
    return os.path.join(SCRATCH, *parts)


def facts(name):
    with open(scratch(name + ".facts.json")) as handle:
        return json.load(handle)


def tree_files(root):
    out = []
    for folder, _, names in os.walk(root):
        for name in names:
            out.append(os.path.relpath(os.path.join(folder, name), root))
    return sorted(out)


# The release moved every `unstable/<area>` folder to the top level, and renamed one of them.
MOVED_AREAS = {"httpapi": "http-api"}


def counterpart(pin_rel, release_files):
    """The release's path for a file of the pin, or None when the release has no such file."""
    if pin_rel in release_files:
        return pin_rel
    if pin_rel.startswith("unstable/"):
        rest = pin_rel[len("unstable/"):]
        area, _, tail = rest.partition("/")
        moved = MOVED_AREAS.get(area, area) + "/" + tail
        if moved in release_files:
            return moved
    return None


IMPORT_SPEC = re.compile(r"""(\bfrom\s*|\bimport\s*\(\s*|\bimport\s*|\brequire\s*\(\s*)(["'])(\.{1,2}/[^"']*)\2""")


def normalise_imports(line, rel, path_map):
    """Rewrite each relative import path to a tree path, mapped through `path_map` when given."""
    base = posixpath.dirname(rel)

    def rewrite(match):
        target = posixpath.normpath(posixpath.join(base, match.group(3)))
        if path_map is not None:
            probe = target[:-3] + ".ts" if target.endswith(".js") else target
            mapped = path_map.get(probe)
            if mapped is not None:
                target = mapped[:-3] + ".js" if target.endswith(".js") else mapped
        return f'{match.group(1)}"@tree/{target}"'

    return IMPORT_SPEC.sub(rewrite, line)


def code_lines(stripped_path, rel, path_map=None):
    """[(line number, code line)] for the non-blank lines of a comment-stripped file."""
    out = []
    with open(stripped_path, encoding="utf8") as handle:
        for number, raw in enumerate(handle.read().split("\n"), start=1):
            text = " ".join(raw.split())
            if text:
                out.append((number, normalise_imports(text, rel, path_map)))
    return out


HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def diff_hunks(a_lines, b_lines):
    """Hunks of a histogram line diff, as (a_start, a_len, b_start, b_len) over 0-based indices.

    `a_start` is the index of the first removed line, or the index before which the added lines
    are inserted when `a_len` is 0. `b_start` likewise.
    """
    with tempfile.TemporaryDirectory() as folder:
        a_path = os.path.join(folder, "a")
        b_path = os.path.join(folder, "b")
        with open(a_path, "w", encoding="utf8") as handle:
            handle.write("".join(line + "\n" for line in a_lines))
        with open(b_path, "w", encoding="utf8") as handle:
            handle.write("".join(line + "\n" for line in b_lines))
        run = subprocess.run(
            ["git", "diff", "--no-index", "--histogram", "-U0", "--no-color", "--no-ext-diff", a_path, b_path],
            capture_output=True, text=True, encoding="utf8")
    hunks = []
    for line in run.stdout.split("\n"):
        match = HUNK.match(line)
        if not match:
            continue
        a_start, a_len = int(match.group(1)), int(match.group(2) or "1")
        b_start, b_len = int(match.group(3)), int(match.group(4) or "1")
        # In unified format a zero-length side names the line before the insertion point.
        a_index = a_start - 1 if a_len > 0 else a_start
        b_index = b_start - 1 if b_len > 0 else b_start
        hunks.append((a_index, a_len, b_index, b_len))
    return hunks


def index_map(hunks, a_count):
    """For each index of the first sequence: the index it equals in the second, or None."""
    mapping = [None] * a_count
    a_pos, b_pos = 0, 0
    for a_index, a_len, b_index, b_len in hunks:
        while a_pos < a_index:
            mapping[a_pos] = b_pos
            a_pos += 1
            b_pos += 1
        a_pos = a_index + a_len
        b_pos = b_index + b_len
    while a_pos < a_count:
        mapping[a_pos] = b_pos
        a_pos += 1
        b_pos += 1
    return mapping


def squeeze(lines):
    """The lines joined with every white-space character removed: layout does not show."""
    return "".join("".join(line.split()) for line in lines)


class Pair:
    """One file of the pin with its counterpart in the release, aligned by code lines."""

    def __init__(self, pin_rel, rel_rel, path_map, kind="src"):
        self.pin_rel, self.rel_rel = pin_rel, rel_rel
        ext = (lambda p: p) if kind == "src" else (lambda p: p[:-3] + ".js")
        self.pin_code = code_lines(scratch("stripped", f"pin-{kind}", ext(pin_rel)), pin_rel, path_map)
        self.rel_code = code_lines(scratch("stripped", f"rel-{kind}", ext(rel_rel)), rel_rel, None)
        self.hunks = diff_hunks([t for _, t in self.pin_code], [t for _, t in self.rel_code])
        self.map = index_map(self.hunks, len(self.pin_code))

    @property
    def removed(self):
        return sum(h[1] for h in self.hunks)

    @property
    def added(self):
        return sum(h[3] for h in self.hunks)


B64 = {c: i for i, c in enumerate("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/")}


def source_lines_of(map_path):
    """For each generated line (1-based): the set of source lines (1-based) that its segments name.

    A version 3 source map with one source. Every segment of a generated line counts, so a
    generated line that holds a token of a source line is tied to that source line.
    """
    with open(map_path, encoding="utf8") as handle:
        data = json.load(handle)
    out = {}
    src_line = 0
    for gen_index, group in enumerate(data["mappings"].split(";")):
        lines = set()
        for segment in group.split(","):
            if not segment:
                continue
            fields, value, shift = [], 0, 0
            for char in segment:
                digit = B64[char]
                value |= (digit & 31) << shift
                if digit & 32:
                    shift += 5
                else:
                    fields.append(-(value >> 1) if value & 1 else value >> 1)
                    value, shift = 0, 0
            if len(fields) >= 4:
                src_line += fields[2]
                lines.add(src_line + 1)
        if lines:
            out[gen_index + 1] = lines
    return out
