#!/usr/bin/env python3
"""A finite scan of the batteries for lines the battery-line rule forbids (decisions row 301).

    python3 battery_lines.py [ROOT]

A battery line is a reader, a control or a finite evaluation (AGENTS.md, Trust). The scan reads
the text of every `Test/**/*.lean` file and reports four shapes. It is a reading of source, not a
proof: a shape it reports can be a legitimate reader, and a restatement in another shape is missed.

- `#print axioms` lines (forbidden outright);
- an `example` or `theorem` whose whole proof is one name, `:= name` or `:= by exact name`, with no
  argument: a restatement of that name's statement, unless the statement is instantiated;
- the same with `:= by simpa using name` or `:= name.symm`;
- `#check name` lines, which pin a statement's existence and read nothing.

It prints a count per shape and per directory, and the lines of the codegen batteries.
"""
import collections
import pathlib
import re
import sys

ROOT = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".").resolve()
NAME = r"[A-Za-z_][A-Za-z0-9_'.!?]*"
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(example|theorem)\b")
BARE = re.compile(rf":=\s*(?:by\s+exact\s+)?({NAME})\s*$")
# Proofs by the kernel or by instance search evaluate; they restate no named theorem.
KERNEL = {"rfl", "inferInstance", "trivial", "Iff.rfl", "HEq.rfl", "id", "decide", "Subsingleton.elim"}
SIMPA = re.compile(rf":=\s*(?:by\s+simpa(?:\s+only\s+\[[^\]]*\])?\s+using\s+({NAME})|({NAME})\.symm)\s*$")


def declarations(lines):
    """Each `example` or `theorem` with its text up to the next blank line or declaration."""
    i = 0
    while i < len(lines):
        if DECL.match(lines[i].lstrip()):
            start = i
            body = [lines[i].rstrip()]
            i += 1
            while i < len(lines) and lines[i].strip() and not DECL.match(lines[i].lstrip()) \
                    and not lines[i].startswith(("#", "/--", "/-!", "--", "namespace", "end ", "section", "open")):
                body.append(lines[i].rstrip())
                i += 1
            yield start + 1, " ".join(part.strip() for part in body)
        else:
            i += 1


def main() -> int:
    counts = collections.Counter()
    per_dir = collections.defaultdict(collections.Counter)
    codegen = []
    everything = []
    files = sorted((ROOT / "Test").rglob("*.lean"))
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        area = "/".join(rel.split("/")[:2])
        lines = path.read_text(errors="replace").splitlines()
        for n, line in enumerate(lines, 1):
            s = line.strip()
            if s.startswith("#print axioms"):
                counts["print-axioms"] += 1
                per_dir[area]["print-axioms"] += 1
                print(f"  print-axioms {rel}:{n}: {s[:120]}")
            if re.match(rf"#check\s+{NAME}\s*$", s):
                counts["check-name"] += 1
                per_dir[area]["check-name"] += 1
        for n, text in declarations(lines):
            bare, simpa = BARE.search(text), SIMPA.search(text)
            named = (bare and bare.group(1)) or (simpa and (simpa.group(1) or simpa.group(2)))
            kind = None if not named or named in KERNEL else ("bare-proof" if bare else "simpa-proof")
            if kind:
                counts[kind] += 1
                per_dir[area][kind] += 1
                entry = f"{rel}:{n}: {kind} by {named}: {text[:150]}"
                everything.append(entry)
                if rel.startswith("Test/Codegen/"):
                    codegen.append(entry)
    print(f"files {len(files)}")
    print("by shape", dict(counts))
    for area, c in sorted(per_dir.items()):
        print(f"  {area}\t{dict(c)}")
    print("codegen batteries")
    for line in codegen:
        print(" ", line)
    print("every bare or simpa proof by name")
    for line in everything:
        print(" ", line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
