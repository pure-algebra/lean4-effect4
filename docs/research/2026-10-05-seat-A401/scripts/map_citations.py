#!/usr/bin/env python3
"""Seat A401: map every cited line range of the pin to the release, and list the changes it meets.

Run (after strip.mjs, units.mjs, compare_trees.py and inventory.py):
    A401_SCRATCH=<scratch> A401_PIN_DIST=<pin build>/dist A401_REL_DIST=<release build>/dist \\
        python3 map_citations.py

It writes, under ../out/:

  ranges.tsv             one row per distinct cited range (pin file, start, end)
  citations-mapped.tsv   citations.tsv with the status and the release's range of each row
  hunks.tsv              one row per hunk of a cited file, with its class and the ranges it meets
  hunks/<file>.diff      the text of each hunk of a cited file (code lines, comments stripped)
  by-file.tsv            the counts per cited file
  js-unexplained.tsv     per cited file: the hunks of the compiled JavaScript whose source lines, by
                         the source maps, lie in no source hunk (an emit difference, if any)

The status of a range:

  same          every code line of the range stands in the release, in one run, with no code line
                added inside it; `shift` is the release's first line minus the pin's
  same-comment  the range holds no code line, and its text stands in the release at the mapped place
  moved         a line diff calls the range changed, and the range's code lines stand once, as one
                run, at another place of the release's file (three lines or sixty characters at least)
  changed       a code line of the range is replaced or dropped, or a code line is added inside it
  removed       no code line of the range stands in the release
  comment-changed  the range holds no code line, and its text differs at the mapped place
  file-absent   the release has no counterpart of the cited file
  out-of-range  the range starts after the last line of the cited file
  file-only     the citation names the file with no line

The class of a hunk (a run of code lines that the two builds do not share):

  layout        the removed and the added lines are equal once white space is dropped
  erased        every declaration that the hunk touches compiles to the same JavaScript in both
                builds, or is a type declaration; or no difference of the compiled JavaScript comes
                from the hunk's lines, by the builds' source maps. The change is types or casts
  import        the hunk touches import statements only
  code          anything else: the compiled JavaScript of a touched declaration differs
"""
import json
import os
import sys

import a401lib as lib

OUT = os.path.join(lib.HERE, "..", "out")
PIN_DIST = os.environ.get("A401_PIN_DIST", "")
REL_DIST = os.environ.get("A401_REL_DIST", "")


def load_units(name):
    with open(lib.scratch(name + ".units.json")) as handle:
        return json.load(handle)


def base(key):
    return key.split("#")[0]


class FileMap:
    """The alignment of one cited file with its counterpart, and the classes of its hunks."""

    def __init__(self, pin_rel, rel_rel, path_map, units):
        self.pin_rel, self.rel_rel = pin_rel, rel_rel
        self.pair = lib.Pair(pin_rel, rel_rel, path_map, "src")
        with open(os.path.join(lib.PIN_SRC, pin_rel), encoding="utf8") as handle:
            self.pin_raw = handle.read().split("\n")
        with open(os.path.join(lib.REL_SRC, rel_rel), encoding="utf8") as handle:
            self.rel_raw = handle.read().split("\n")
        js = lambda p: p[:-3] + ".js"
        self.pin_units = units["pin-src"].get(pin_rel, [])
        self.rel_units = units["rel-src"].get(rel_rel, [])
        pin_js = {u["key"]: u for u in units["pin-dist"].get(js(pin_rel), [])}
        rel_js = {u["key"]: u for u in units["rel-dist"].get(js(rel_rel), [])}
        rel_by_key = {u["key"]: u for u in self.rel_units}
        pin_by_key = {u["key"]: u for u in self.pin_units}

        def js_of(table, key):
            if key in table:
                return table[key]
            same_base = [u for k, u in table.items() if base(k) == base(key)]
            return same_base[0] if len(same_base) == 1 else None

        def status(unit, other_by_key, mine_js, other_js):
            """How a unit compares with the unit of the same key in the other build."""
            other = other_by_key.get(unit["key"])
            if other is None:
                same_base = [u for k, u in other_by_key.items() if base(k) == base(unit["key"])]
                other = same_base[0] if len(same_base) == 1 else None
            if other is None:
                return "absent"
            if other["ast"] == unit["ast"]:
                return "same"
            kind = unit["kind"].replace("export ", "")
            if kind in ("interface", "type", "namespace", "import", "export-all", "export-list"):
                return "type-decl" if kind in ("interface", "type", "namespace") else "import"
            a, b = js_of(mine_js, unit["key"]), js_of(other_js, unit["key"])
            if a is None and b is None:
                return "erased"         # an overload signature or a declaration with no JavaScript
            if a is not None and b is not None and a["ast"] == b["ast"]:
                return "erased"
            return "code"

        self.pin_status = {u["key"]: status(u, rel_by_key, pin_js, rel_js) for u in self.pin_units}
        self.rel_status = {u["key"]: status(u, pin_by_key, rel_js, pin_js) for u in self.rel_units}
        # The source lines that a difference of the compiled JavaScript comes from, by source map.
        self.js_pin_lines, self.js_rel_lines, self.js_hunks = set(), set(), 0
        dist = lib.Pair(pin_rel, rel_rel, path_map, "dist")
        js_hunk_lines = []
        if dist.hunks:
            pin_map = lib.source_lines_of(os.path.join(PIN_DIST, js(pin_rel) + ".map"))
            rel_map = lib.source_lines_of(os.path.join(REL_DIST, js(rel_rel) + ".map"))
            self.js_hunks = len(dist.hunks)
            for a_index, a_len, b_index, b_len in dist.hunks:
                from_pin, from_rel = set(), set()
                for number, _ in dist.pin_code[a_index:a_index + a_len]:
                    from_pin |= pin_map.get(number, set())
                for number, _ in dist.rel_code[b_index:b_index + b_len]:
                    from_rel |= rel_map.get(number, set())
                self.js_pin_lines |= from_pin
                self.js_rel_lines |= from_rel
                js_hunk_lines.append((from_pin, from_rel, dist.pin_code[a_index:a_index + a_len],
                                      dist.rel_code[b_index:b_index + b_len]))
        self.hunks = [self.classify(i, h) for i, h in enumerate(self.pair.hunks)]
        # A difference of the JavaScript that no source hunk explains would be an emit difference.
        covered_pin, covered_rel = set(), set()
        for h in self.hunks:
            covered_pin |= set(range(h["pin_first"], h["pin_last"] + 1))
            covered_rel |= set(range(h["rel_first"], h["rel_last"] + 1))
        self.js_unexplained = [(a, b) for from_pin, from_rel, a, b in js_hunk_lines
                               if not (from_pin & covered_pin) and not (from_rel & covered_rel)]

    def units_at(self, units, first, last):
        """The innermost units that overlap the lines; a class is dropped when a member overlaps."""
        hit = [u for u in units if u["start"] <= last and u["end"] >= first]
        members = {base(u["key"]).split(".")[0].replace("get ", "").replace("set ", "")
                   for u in hit if "member" in u["kind"]}
        return [u for u in hit if not (u["kind"].endswith("class") and u["key"] in members)]

    def classify(self, index, hunk):
        a_index, a_len, b_index, b_len = hunk
        pin_code, rel_code = self.pair.pin_code, self.pair.rel_code
        removed = pin_code[a_index:a_index + a_len]
        added = rel_code[b_index:b_index + b_len]
        pin_units = self.units_at(self.pin_units, removed[0][0], removed[-1][0]) if removed else []
        rel_units = self.units_at(self.rel_units, added[0][0], added[-1][0]) if added else []
        statuses = [self.pin_status[u["key"]] for u in pin_units] + [self.rel_status[u["key"]] for u in rel_units]
        # The hunk's own lines, widened to the whole statement lines around it on neither side:
        # a source line belongs to the hunk when the diff says so, and to nothing else.
        pin_first = removed[0][0] if removed else 1
        pin_last = removed[-1][0] if removed else 0
        rel_first = added[0][0] if added else 1
        rel_last = added[-1][0] if added else 0
        js_here = any(pin_first <= n <= pin_last for n in self.js_pin_lines) \
            or any(rel_first <= n <= rel_last for n in self.js_rel_lines)
        if lib.squeeze(t for _, t in removed) == lib.squeeze(t for _, t in added):
            klass = "layout"
        elif statuses and all(s == "import" for s in statuses):
            klass = "import"
        elif statuses and all(s in ("same", "erased", "type-decl", "import") for s in statuses):
            klass = "erased"
        elif not js_here:
            klass = "erased"
        else:
            klass = "code"
        return dict(id=index + 1, a_index=a_index, a_len=a_len, b_index=b_index, b_len=b_len,
                    removed=removed, added=added, klass=klass, pin_first=pin_first, pin_last=pin_last,
                    rel_first=rel_first, rel_last=rel_last,
                    pin_units=[u["key"] + "=" + self.pin_status[u["key"]] for u in pin_units],
                    rel_units=[u["key"] + "=" + self.rel_status[u["key"]] for u in rel_units],
                    ranges=0)

    def map_range(self, start, end):
        pin_code, rel_code, mapping = self.pair.pin_code, self.pair.rel_code, self.pair.map
        if start > len(self.pin_raw):
            return dict(status="out-of-range", new_start="", new_end="", shift="", hunks=[])
        inside = [i for i, (number, _) in enumerate(pin_code) if start <= number <= end]
        if not inside:
            # No code line: place the range by the code line after it, or the one before it.
            after = next((i for i, (number, _) in enumerate(pin_code) if number > end), None)
            before = next((i for i in range(len(pin_code) - 1, -1, -1) if pin_code[i][0] < start), None)
            new_start = None
            if after is not None and mapping[after] is not None:
                new_start = rel_code[mapping[after]][0] - (pin_code[after][0] - start)
            elif before is not None and mapping[before] is not None:
                new_start = rel_code[mapping[before]][0] + (start - pin_code[before][0])
            if new_start is None or new_start < 1:
                return dict(status="comment-changed", new_start="", new_end="", shift="", hunks=[])
            new_end = new_start + (end - start)
            same = self.pin_raw[start - 1:end] == self.rel_raw[new_start - 1:new_end]
            return dict(status="same-comment" if same else "comment-changed", new_start=new_start,
                        new_end=new_end, shift=new_start - start, hunks=[])
        first, last = inside[0], inside[-1]
        touched = [h for h in self.hunks
                   if (h["a_len"] > 0 and h["a_index"] <= last and h["a_index"] + h["a_len"] - 1 >= first)
                   or (h["a_len"] == 0 and first < h["a_index"] <= last)]
        mapped = [mapping[i] for i in inside]
        if not touched:
            new_start, new_end = rel_code[mapped[0]][0], rel_code[mapped[-1]][0]
            # Keep the leading and trailing lines of the range that hold no code.
            new_start -= pin_code[first][0] - start
            new_end += end - pin_code[last][0]
            return dict(status="same", new_start=new_start, new_end=new_end, shift=new_start - start, hunks=[])
        alive = [m for m in mapped if m is not None]
        # A block that a line diff calls changed may stand elsewhere in the release, unchanged.
        block = [pin_code[i][1] for i in inside]
        texts = [t for _, t in rel_code]
        places = [j for j in range(len(texts) - len(block) + 1) if texts[j:j + len(block)] == block]
        if len(places) == 1 and (len(block) >= 3 or sum(len(t) for t in block) >= 60):
            new_start = rel_code[places[0]][0] - (pin_code[first][0] - start)
            new_end = rel_code[places[0] + len(block) - 1][0] + (end - pin_code[last][0])
            return dict(status="moved", new_start=new_start, new_end=new_end, shift=new_start - start, hunks=[])
        if not alive and all(h["b_len"] == 0 for h in touched):
            status = "removed"
        else:
            status = "changed"
        lows = [rel_code[m][0] for m in alive]
        for h in touched:
            if h["b_len"] > 0:
                lows += [rel_code[h["b_index"]][0], rel_code[h["b_index"] + h["b_len"] - 1][0]]
        new_start = min(lows) if lows else ""
        new_end = max(lows) if lows else ""
        return dict(status=status, new_start=new_start, new_end=new_end, shift="", hunks=touched)


def main():
    pin_src, rel_src = lib.facts("pin-src"), lib.facts("rel-src")
    release_files = set(rel_src)
    path_map = {p: lib.counterpart(p, release_files) for p in pin_src}
    path_map = {p: r for p, r in path_map.items() if r is not None}
    units = {name: load_units(name) for name in ("pin-src", "rel-src", "pin-dist", "rel-dist")}
    file_status = {}
    with open(os.path.join(OUT, "files.tsv"), encoding="utf8") as handle:
        for line in list(handle)[1:]:
            cells = line.rstrip("\n").split("\t")
            if cells[1] != "-":
                file_status[cells[1]] = cells[0]

    with open(os.path.join(OUT, "citations.tsv"), encoding="utf8") as handle:
        header, *rows = [line.rstrip("\n").split("\t") for line in handle]
    maps, results = {}, {}

    def file_map(pin_rel):
        if pin_rel not in maps:
            maps[pin_rel] = FileMap(pin_rel, path_map[pin_rel], path_map, units)
        return maps[pin_rel]

    for row in rows:
        pin_rel, start, end = row[6], int(row[7]), int(row[8])
        if pin_rel == "-":
            continue
        key = (pin_rel, start, end)
        if key in results:
            results[key]["count"] += 1
            continue
        if start == 0:
            result = dict(status="file-only", new_start="", new_end="", shift="", hunks=[], units=[])
        elif pin_rel not in path_map:
            result = dict(status="file-absent", new_start="", new_end="", shift="", hunks=[], units=[])
        else:
            fm = file_map(pin_rel)
            result = fm.map_range(start, end)
            result["units"] = [u["key"] + "=" + fm.pin_status[u["key"]]
                               for u in fm.units_at(fm.pin_units, start, end)]
            for h in result["hunks"]:
                h["ranges"] += 1
        result["count"] = 1
        results[key] = result

    def release_of(pin_rel):
        return path_map.get(pin_rel, "-")

    def hunk_cell(result):
        return ",".join(f"{h['id']}:{h['klass']}" for h in result["hunks"])

    def verdict(result):
        """The strongest class among the hunks that a changed range meets."""
        classes = {h["klass"] for h in result["hunks"]}
        for klass in ("code", "erased", "import", "layout"):
            if klass in classes:
                return klass
        return ""

    with open(os.path.join(OUT, "ranges.tsv"), "w", encoding="utf8") as out:
        out.write("\t".join(["pin_file", "start", "end", "citations", "status", "strongest_hunk_class",
                             "release_file", "new_start", "new_end", "shift", "file_status", "hunks", "units"]) + "\n")
        for (pin_rel, start, end), r in sorted(results.items()):
            out.write("\t".join(str(x) for x in [
                pin_rel, start, end, r["count"], r["status"], verdict(r), release_of(pin_rel), r["new_start"],
                r["new_end"], r["shift"], file_status.get(pin_rel, ""), hunk_cell(r), ";".join(r["units"])]) + "\n")

    with open(os.path.join(OUT, "citations-mapped.tsv"), "w", encoding="utf8") as out:
        out.write("\t".join(header + ["status", "strongest_hunk_class", "release_file", "new_start", "new_end"]) + "\n")
        for row in rows:
            if row[6] == "-":
                out.write("\t".join(row + ["not-a-pin-citation", "", "", "", ""]) + "\n")
                continue
            r = results[(row[6], int(row[7]), int(row[8]))]
            out.write("\t".join(row + [r["status"], verdict(r), release_of(row[6]), str(r["new_start"]),
                                       str(r["new_end"])]) + "\n")

    os.makedirs(os.path.join(OUT, "hunks"), exist_ok=True)
    with open(os.path.join(OUT, "hunks.tsv"), "w", encoding="utf8") as out:
        out.write("\t".join(["pin_file", "hunk", "class", "pin_lines", "release_lines", "removed", "added",
                             "cited_ranges", "pin_units", "release_units"]) + "\n")
        for pin_rel in sorted(maps):
            fm = maps[pin_rel]
            name = pin_rel.replace("/", "__") + ".diff"
            with open(os.path.join(OUT, "hunks", name), "w", encoding="utf8") as diff:
                diff.write(f"# {pin_rel} (rc.112) against {fm.rel_rel} (4.0.1): code lines, comments stripped\n")
                for h in fm.hunks:
                    pin_lines = f"{h['removed'][0][0]}-{h['removed'][-1][0]}" if h["removed"] else \
                        f"before {fm.pair.pin_code[h['a_index']][0] if h['a_index'] < len(fm.pair.pin_code) else 'end'}"
                    rel_lines = f"{h['added'][0][0]}-{h['added'][-1][0]}" if h["added"] else \
                        f"before {fm.pair.rel_code[h['b_index']][0] if h['b_index'] < len(fm.pair.rel_code) else 'end'}"
                    out.write("\t".join(str(x) for x in [
                        pin_rel, h["id"], h["klass"], pin_lines, rel_lines, h["a_len"], h["b_len"], h["ranges"],
                        ";".join(h["pin_units"]), ";".join(h["rel_units"])]) + "\n")
                    diff.write(f"\n@@ hunk {h['id']} [{h['klass']}] pin {pin_lines} release {rel_lines} "
                               f"cited ranges {h['ranges']}\n")
                    diff.write(f"   pin units: {'; '.join(h['pin_units'])}\n")
                    diff.write(f"   release units: {'; '.join(h['rel_units'])}\n")
                    for number, text in h["removed"]:
                        diff.write(f"-{number:6d} {text}\n")
                    for number, text in h["added"]:
                        diff.write(f"+{number:6d} {text}\n")

    by_file = {}
    for row in rows:
        if row[6] == "-":
            continue
        r = results[(row[6], int(row[7]), int(row[8]))]
        entry = by_file.setdefault(row[6], {"brief": 0, "extended": 0, "archive": 0, "status": {}, "klass": {}})
        entry["archive" if row[1] == "archive" else row[0]] += 1
        entry["status"][r["status"]] = entry["status"].get(r["status"], 0) + 1
        if r["status"] in ("changed", "removed"):
            entry["klass"][verdict(r)] = entry["klass"].get(verdict(r), 0) + 1
    statuses = ["same", "same-comment", "moved", "changed", "removed", "comment-changed", "file-absent", "out-of-range", "file-only"]
    classes = ["code", "erased", "import", "layout"]
    with open(os.path.join(OUT, "by-file.tsv"), "w", encoding="utf8") as out:
        out.write("\t".join(["pin_file", "release_file", "file_status", "citations", "brief_live", "brief_archive",
                             "extended"] + statuses + ["changed:" + c for c in classes]) + "\n")
        for pin_rel, entry in sorted(by_file.items(), key=lambda kv: -sum(kv[1]["status"].values())):
            total = sum(entry["status"].values())
            out.write("\t".join(str(x) for x in [
                pin_rel, release_of(pin_rel), file_status.get(pin_rel, "absent"), total, entry["brief"],
                entry["archive"], entry["extended"]] + [entry["status"].get(s, 0) for s in statuses]
                + [entry["klass"].get(c, 0) for c in classes]) + "\n")
    with open(os.path.join(OUT, "js-unexplained.tsv"), "w", encoding="utf8") as out:
        out.write("pin_file\tjs_hunks\tjs_hunks_that_no_source_hunk_explains\tfirst_such_hunk\n")
        for pin_rel in sorted(maps):
            fm = maps[pin_rel]
            first = ""
            if fm.js_unexplained:
                a, b = fm.js_unexplained[0]
                first = " | ".join(["-" + t for _, t in a[:2]] + ["+" + t for _, t in b[:2]])[:200]
            out.write(f"{pin_rel}\t{fm.js_hunks}\t{len(fm.js_unexplained)}\t{first}\n")
    totals = {}
    for r in results.values():
        totals[r["status"]] = totals.get(r["status"], 0) + r["count"]
    print(f"distinct ranges {len(results)}; cited files {len(by_file)}; citations by status {dict(sorted(totals.items()))}",
          file=sys.stderr)


if __name__ == "__main__":
    main()
