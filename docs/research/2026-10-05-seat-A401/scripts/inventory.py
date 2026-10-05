#!/usr/bin/env python3
"""Seat A401: the inventory of the citations of the pinned Effect source.

Run: python3 inventory.py > ../out/citations.tsv        (a summary goes to stderr)

It reads every tracked file outside `docs/research/` and `vendor/`. The brief's domain is
`src/`, `Test/`, `tools/`, `docs/core/`, `docs/RUNTIME-COVERAGE.md`, `docs/UPSTREAM-BACKLOG.md` and
`generated/effect-runtime-census.tsv`; every other tracked file is the extended domain.

A citation has one of four forms:

  full        `vendor/effect-4.0.0-rc.112/src/Queue.ts:455`     (the line part is optional)
  bare        `internal/effect.ts:6039-6068`, `Scheduler.ts:207-233`
  cont        `:5291`, a line part alone, which continues a file named before it
  census-row  a `mechanism` row of `generated/effect-runtime-census.tsv`: a file and a line range
              in two columns (the token is the row id)

One row is one line range: `X.ts:3800-3804,4019-4030` gives two rows. The file of a `bare` token
is resolved against the pin's tree (an exact path, or the one file whose path ends with the token).

The file of a `cont` token is not written beside it, so the script tries candidates in this order
and takes the first one that passes a check:

  1. block     the last file named before the token in the same block (a comment, a docstring, a
               paragraph or a table row), when it is a pin file, carries a line, or touches the token
  2. tag       the file of a census row that the block names in a `census: <row id>` tag
  3. default   the default of the citing file (`defaults.tsv`: declared in its header, or read there)
  4. carry     the last file that an earlier block cited with a line
  5. dominant  the file that the citing file cites most often with a line
  6. global    `internal/effect.ts`, the default that `src/Effect4/Machine/Fibers.lean` declares
  7. plain     a file that the same block names without a line

The checks, strongest first:

  census   the block carries a `census: <row id>` tag, and the lines lie in or near that row's span
  exact    the code span just before the token names an identifier that the cited lines hold
  named    a code span of the block names an identifier that the cited lines hold (two lines of margin)

A file with a line part that is neither a pin file nor one tracked file (`K2Copy.lean:994`) is
`outside`: a `cont` token after it in the same block continues that file, not the pin.

`check` is the result for the file the row reports. A `cont` row that no candidate passes takes
the first candidate whose file holds the lines, and its check is `unconfirmed`. `skipped:` lists
the earlier candidates that held the lines and failed the check; `also:` lists the later ones
that pass too. `overrides.tsv` settles the rows that the seat read by hand.
"""
import os
import re
import subprocess
import sys

import a401lib as lib

BRIEF_PREFIXES = ("src/", "Test/", "tools/", "docs/core/")
BRIEF_FILES = ("docs/RUNTIME-COVERAGE.md", "docs/UPSTREAM-BACKLOG.md", "generated/effect-runtime-census.tsv")
ARCHIVE_PREFIXES = ("Test/Counterexamples/Archive/", "Test/contracts/archive/")
FULL_MARK = "effect-4.0.0-rc.112/src/"
GLOBAL_DEFAULT = "internal/effect.ts"

EXT = r"(?:ts|tsx|lean|json|md|mjs|cjs|js|py|sh|ml|mli|tsv|toml|txt|out|yml|yaml)"
FILE_TOKEN = re.compile(r"(?<![\w@./:-])((?:[\w@.-]+/)*[\w@.-]*[\w]\." + EXT + r")(?![\w/-])")
LINES_HEAD = re.compile(r":(\d+)(?:\s?[-–]\s?(\d+))?")
LINES_MORE_TIGHT = re.compile(r",(\d+)(?:[-–](\d+))?")
LINES_MORE_LOOSE = re.compile(r",\s?(\d+)(?:\s?[-–]\s?(\d+))?")
CONT_TOKEN = re.compile(r"`(?:[A-Za-z_$][\w$.]* )?:(\d+)(?:[-–](\d+))?((?:,\s?\d+(?:[-–]\d+)?)*)`")
IDENT = re.compile(r"[A-Za-z_$][\w$]{3,}")
CODE_SPAN = re.compile(r"`([^`\n]+)`")
CENSUS_TAG = re.compile(r"census:\s*((?:[a-z-]+\.[A-Za-z0-9-]+)(?:\s*,\s*[a-z-]+\.[A-Za-z0-9-]+)*)")


def tracked():
    out = subprocess.run(["git", "ls-files", "-z"], cwd=lib.REPO, capture_output=True, check=True).stdout
    return [p for p in out.decode("utf8").split("\0") if p]


def is_text(path):
    return not path.endswith((".png", ".jpg", ".jpeg", ".gif", ".pdf", ".ico", ".woff", ".woff2", ".zip",
                              ".gz", ".tgz", ".wasm", ".bin", ".lockb"))


def blocks_of(path, lines):
    """A block number for every line: the unit inside which a `cont` token continues a file."""
    out, block = [], 0
    if path.endswith(".lean"):
        depth, in_line_run = 0, False
        for line in lines:
            stripped = line.strip()
            opens = len(re.findall(r"/-", line))
            closes = len(re.findall(r"-/", line))
            if depth == 0:
                if opens > 0:
                    block += 1
                    in_line_run = False
                elif stripped.startswith("--"):
                    if not in_line_run:
                        block += 1
                    in_line_run = True
                else:
                    block += 1
                    in_line_run = False
            out.append(block)
            depth = max(0, depth + opens - closes)
    elif path.endswith(".md"):
        previous_blank = True
        for line in lines:
            stripped = line.strip()
            starts_item = bool(re.match(r"^\s*(?:[-*+]|\d+\.)\s", line)) or stripped.startswith("|") \
                or stripped.startswith("#")
            if not stripped:
                previous_blank = True
                block += 1
            elif previous_blank or starts_item:
                block += 1
                previous_blank = False
            out.append(block)
    else:
        in_comment = False
        for line in lines:
            stripped = line.strip()
            is_comment = stripped.startswith(("//", "*", "/*", "#", "(*"))
            if not (is_comment and in_comment):
                block += 1
            in_comment = is_comment
            out.append(block)
    return out


class Sources:
    """The pin's tree and the tracked tree, with the text of each file read once."""

    def __init__(self, repo_files):
        self.pin = set(lib.tree_files(lib.PIN_SRC))
        self.repo = set(repo_files)
        self.text = {}

    def resolve(self, token):
        """(kind, file, how): kind is `pin`, `repo` or `none`."""
        if FULL_MARK in token:
            rel = token.split(FULL_MARK, 1)[1]
            return ("pin", rel, "full") if rel in self.pin else ("none", token, "full-missing")
        if token.endswith(".ts"):
            if token in self.repo:
                return ("repo", token, "repo-file")
            if token in self.pin:
                return ("pin", token, "exact")
            if token.startswith("src/") and token[4:] in self.pin:
                return ("pin", token[4:], "exact")
            tails = sorted(rel for rel in self.pin if rel.endswith("/" + token))
            if len(tails) == 1:
                return ("pin", tails[0], "suffix")
            if len(tails) > 1:
                return ("none", token, "ambiguous:" + ",".join(tails))
        if token in self.repo:
            return ("repo", token, "repo-file")
        tails = sorted(p for p in self.repo if p.endswith("/" + token))
        if len(tails) == 1:
            return ("repo", tails[0], "repo-suffix")
        if len(tails) > 1:
            return ("repo-many", "|".join(tails), "repo-ambiguous")
        return ("none", token, "not-in-pin" if token.endswith(".ts") else "other-kind")

    def lines(self, kind, rel):
        key = (kind, rel)
        if key not in self.text:
            root = lib.PIN_SRC if kind == "pin" else lib.REPO
            try:
                with open(os.path.join(root, rel), encoding="utf8") as handle:
                    self.text[key] = handle.read().split("\n")
            except (OSError, UnicodeDecodeError):
                self.text[key] = []
        return self.text[key]


def parse_lines(text, start, loose):
    head = LINES_HEAD.match(text, start)
    if not head:
        return []
    ranges = [(int(head.group(1)), int(head.group(2) or head.group(1)))]
    position = head.end()
    more = LINES_MORE_LOOSE if loose else LINES_MORE_TIGHT
    while True:
        nxt = more.match(text, position)
        if not nxt:
            break
        ranges.append((int(nxt.group(1)), int(nxt.group(2) or nxt.group(1))))
        position = nxt.end()
    return ranges


def census_spans():
    """row id -> (file, start, end) from the committed census table."""
    out = {}
    with open(os.path.join(lib.REPO, "generated", "effect-runtime-census.tsv"), encoding="utf8") as handle:
        for line in handle:
            cells = line.rstrip("\n").split("\t")
            if cells[0] == "mechanism":
                start, end = cells[4].split("-")
                out[cells[2]] = (cells[3], int(start), int(end))
    return out


def load_defaults():
    out = {}
    with open(os.path.join(lib.HERE, "defaults.tsv"), encoding="utf8") as handle:
        for line in handle:
            if line.startswith("#") or not line.strip():
                continue
            path, default, _ = line.rstrip("\n").split("\t", 2)
            out[path] = default
    return out


def load_overrides():
    """(citing file, citing line, start, end) -> the file the seat read there (`-` for no pin file)."""
    out = {}
    path = os.path.join(lib.HERE, "overrides.tsv")
    if not os.path.exists(path):
        return out
    with open(path, encoding="utf8") as handle:
        for line in handle:
            if line.startswith("#") or not line.strip():
                continue
            citing, number, start, end, target, _ = line.rstrip("\n").split("\t", 5)
            out[(citing, int(number), int(start), int(end))] = target
    return out


def main():
    files = [p for p in tracked() if not p.startswith(("docs/research/", "vendor/")) and is_text(p)]
    sources = Sources(files)
    spans = census_spans()
    defaults = load_defaults()
    overrides = load_overrides()
    used_overrides = set()
    rows, others = [], {}

    for path in files:
        try:
            with open(os.path.join(lib.REPO, path), encoding="utf8") as handle:
                lines = handle.read().split("\n")
        except (UnicodeDecodeError, OSError):
            continue
        if not any(".ts" in line or "`:" in line for line in lines):
            continue
        if path == "generated/effect-runtime-census.tsv":
            # The census table names a row's file and its lines in two columns.
            for number, line in enumerate(lines, start=1):
                cells = line.split("\t")
                if cells[0] == "mechanism":
                    start, end = cells[4].split("-")
                    rows.append(dict(path=path, line=number, form="census-row", token=cells[2], file=cells[3],
                                     start=int(start), end=int(end), how="table", check="census"))
        block_of = blocks_of(path, lines)
        block_text, block_tags = {}, {}
        for number, line in enumerate(lines, start=1):
            block_text.setdefault(block_of[number - 1], []).append(line)
        for block, text in block_text.items():
            joined = "\n".join(text)
            tags = [tag.strip() for group in CENSUS_TAG.findall(joined) for tag in group.split(",")]
            block_tags[block] = [tag for tag in tags if tag in spans]

        def names_of(block):
            found = CODE_SPAN.findall("\n".join(block_text[block]))
            return {name for span in found for name in IDENT.findall(span)
                    if not re.search(r"\.(ts|lean|md|json)(:[\d,–-]+)?$", span.strip())}

        def check(kind, rel, start, end, block, near=frozenset()):
            """`census`, `exact`, `named`, `unnamed`, `out-of-range` or `outside` for one candidate."""
            if kind == "outside":
                return "outside"
            if kind == "pin":
                for tag in block_tags[block]:
                    tag_file, tag_start, tag_end = spans[tag]
                    if tag_file == rel and start >= tag_start - 15 and end <= tag_end + 15:
                        return "census"
            source = sources.lines(kind, rel)
            if start > len(source) or start < 1:
                return "out-of-range"
            if near and near & set(IDENT.findall("\n".join(source[start - 1:end]))):
                return "exact"
            window = "\n".join(source[max(0, start - 3):min(len(source), end + 2)])
            return "named" if names_of(block) & set(IDENT.findall(window)) else "unnamed"

        def near_names(line_number, position):
            """The identifiers of the code span that ends just before `position` on the line."""
            text = lines[line_number - 1][:position]
            found = CODE_SPAN.findall(text)
            while found and re.fullmatch(r"(?:[\w$.]* )?:[\d,–\s-]+", found[-1].strip()):
                found.pop()
            if not found:
                return frozenset()
            if re.search(r"\.(ts|lean|md|json)(:[\d,–-]+)?$", found[-1].strip()):
                return frozenset()
            return frozenset(IDENT.findall(found[-1]))

        # Pass 1: the tokens of the file, in order.
        tokens = []
        for number, line in enumerate(lines, start=1):
            events = [(m.start(), "file", m) for m in FILE_TOKEN.finditer(line)]
            events += [(m.start(), "cont", m) for m in CONT_TOKEN.finditer(line)]
            for position, kind, match in sorted(events, key=lambda e: e[0]):
                if kind == "file":
                    token = match.group(1)
                    file_kind, rel, how = sources.resolve(token)
                    loose = line.count("`", 0, match.start()) % 2 == 1
                    ranges = parse_lines(line, match.end(), loose)
                    tokens.append(dict(kind="file", line=number, position=position, end=match.end(), token=token,
                                       file_kind=file_kind, rel=rel, how=how, ranges=ranges))
                else:
                    ranges = [(int(match.group(1)), int(match.group(2) or match.group(1)))]
                    for extra in re.finditer(r"(\d+)(?:[-–](\d+))?", match.group(3) or ""):
                        ranges.append((int(extra.group(1)), int(extra.group(2) or extra.group(1))))
                    tokens.append(dict(kind="cont", line=number, position=position, end=match.end(),
                                       token=match.group(0).strip("`"), ranges=ranges))

        lined = [t for t in tokens if t["kind"] == "file" and t["ranges"] and t["file_kind"] in ("pin", "repo")]
        tally = {}
        for t in lined:
            tally[(t["file_kind"], t["rel"])] = tally.get((t["file_kind"], t["rel"]), 0) + 1
        dominant = max(tally, key=tally.get) if tally else None

        # Pass 2: one row per range.
        block_id, block_last, block_plain, carry = None, None, [], None
        for index, t in enumerate(tokens):
            this_block = block_of[t["line"] - 1]
            if this_block != block_id:
                block_id, block_last, block_plain = this_block, None, []
            if t["kind"] == "file":
                is_full = t["how"] in ("full", "full-missing")
                usable = t["file_kind"] in ("pin", "repo")
                if t["file_kind"] in ("none", "repo-many") and t["ranges"] and not is_full:
                    block_last = ("outside", t["token"])
                    carry = block_last
                elif usable and (t["file_kind"] == "pin" or t["ranges"]):
                    block_last = (t["file_kind"], t["rel"])
                    if t["ranges"] or t["file_kind"] == "pin":
                        carry = (t["file_kind"], t["rel"]) if t["ranges"] else carry
                elif usable:
                    nxt = tokens[index + 1] if index + 1 < len(tokens) else None
                    touching = nxt is not None and nxt["kind"] == "cont" and nxt["line"] == t["line"] \
                        and nxt["position"] - t["end"] <= 4
                    if touching:
                        block_last = (t["file_kind"], t["rel"])
                    else:
                        block_plain.append((t["file_kind"], t["rel"]))
                elif t["file_kind"] == "repo-many":
                    for rel in t["rel"].split("|"):
                        block_plain.append(("repo", rel))
                if t["file_kind"] != "pin":
                    if t["ranges"] and t["token"].endswith(".ts") and t["file_kind"] == "none":
                        others.setdefault((t["token"], t["how"]), []).append(f"{path}:{t['line']}")
                    if not is_full:
                        continue
                if not t["ranges"] and not is_full:
                    continue            # a bare file name with no line is not a citation
                form = "full" if is_full else "bare"
                near = near_names(t["line"], t["position"])
                for start, end in (t["ranges"] or [(0, 0)]):
                    verdict = "n/a"
                    if t["file_kind"] == "pin" and start > 0:
                        verdict = check("pin", t["rel"], start, end, block_id, near)
                    rows.append(dict(path=path, line=t["line"], form=form, token=t["token"],
                                     file=t["rel"] if t["file_kind"] == "pin" else "-",
                                     start=start, end=end, how=t["how"], check=verdict))
            else:
                candidates = []
                if block_last is not None:
                    candidates.append(("block", block_last))
                for tag in block_tags[block_id]:
                    candidates.append(("tag", ("pin", spans[tag][0])))
                if path in defaults:
                    candidates.append(("default", ("pin", defaults[path])))
                if carry is not None:
                    candidates.append(("carry", carry))
                if dominant is not None:
                    candidates.append(("dominant", dominant))
                candidates.append(("global", ("pin", GLOBAL_DEFAULT)))
                candidates += [("plain", c) for c in block_plain]
                seen, ordered = set(), []
                for why, target in candidates:
                    if target not in seen:
                        seen.add(target)
                        ordered.append((why, target))
                for start, end in t["ranges"]:
                    key = (path, t["line"], start, end)
                    if key in overrides:
                        used_overrides.add(key)
                        target = overrides[key]
                        rows.append(dict(path=path, line=t["line"], form="cont", token=t["token"],
                                         file=target if target in sources.pin else "-", start=start, end=end,
                                         how="read" if target in sources.pin else f"read:{target}", check="read"))
                        continue
                    near = near_names(t["line"], t["position"])
                    verdicts = [(why, target, check(target[0], target[1], start, end, block_id, near))
                                for why, target in ordered]
                    first = verdicts[0]
                    chosen = next((v for v in verdicts if v[2] == "census"), None) \
                        or (first if first[2] == "outside" else None) \
                        or next((v for v in verdicts if v[2] == "exact"), None) \
                        or next((v for v in verdicts if v[2] == "named"), None)
                    if chosen is None:
                        chosen = next((v for v in verdicts if v[2] != "out-of-range"), verdicts[0])
                        chosen = (chosen[0], chosen[1], "unconfirmed" if chosen[2] == "unnamed" else chosen[2])
                    why, (file_kind, rel), verdict = chosen
                    passing = [f"{w}={tg[1]}" for w, tg, v in verdicts
                               if v in ("census", "exact", "named") and tg != (file_kind, rel)]
                    skipped = []
                    for w, tg, v in verdicts:
                        if tg == (file_kind, rel):
                            break
                        if v == "unnamed":
                            skipped.append(f"{w}={tg[1]}")
                    note = verdict + (";also:" + ",".join(passing) if passing else "") \
                        + (";skipped:" + ",".join(skipped) if skipped else "")
                    rows.append(dict(path=path, line=t["line"], form="cont", token=t["token"],
                                     file=rel if file_kind == "pin" else "-", start=start, end=end,
                                     how=why if file_kind == "pin" else f"{why}:{rel}", check=note))

    print("\t".join(["domain", "archive", "citing_file", "citing_line", "form", "token", "pin_file",
                     "start", "end", "resolution", "check"]))
    for row in rows:
        domain = "brief" if row["path"].startswith(BRIEF_PREFIXES) or row["path"] in BRIEF_FILES else "extended"
        archive = "archive" if row["path"].startswith(ARCHIVE_PREFIXES) else "live"
        print("\t".join(str(x) for x in [domain, archive, row["path"], row["line"], row["form"], row["token"],
                                         row["file"], row["start"], row["end"], row["how"], row["check"]]))

    for key in sorted(set(overrides) - used_overrides):
        print(f"  UNUSED OVERRIDE\t{key}", file=sys.stderr)
    resolved = [r for r in rows if r["file"] != "-"]
    print(f"rows {len(rows)}; resolved to a pin file {len(resolved)}; "
          f"`.ts` tokens with lines that resolve to no file: {len(others)}", file=sys.stderr)
    for (token, how), where in sorted(others.items()):
        print(f"  other\t{token}\t{how}\t{len(where)}\t{where[0]}", file=sys.stderr)


if __name__ == "__main__":
    main()
