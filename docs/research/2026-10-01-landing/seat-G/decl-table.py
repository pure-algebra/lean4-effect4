#!/usr/bin/env python3
"""Seat G: a table of the declarations in an axioms log (`'X' depends on axioms: [...]` or
`'X' does not depend on any axioms`), each with the file:line that declares it in this worktree.
Usage: decl-table.py AXIOMS.log"""
import os, re, subprocess, sys
root = os.path.dirname(os.path.abspath(__file__))
while not os.path.exists(os.path.join(root, "lakefile.toml")):
    root = os.path.dirname(root)
pat = re.compile(r"^'(?P<name>[^']+)' (?:depends on axioms: \[(?P<ax>[^\]]*)\]|does not depend on any axioms)")
def site(full):
    parts = full.split(".")
    short = parts[-1]
    # a declaration written with a dotted name (`FoldLift.fireFold_lift`) or a plain one
    cands = [".".join(parts[-2:]), short] if len(parts) > 1 else [short]
    for c in cands:
        out = subprocess.run(["git", "grep", "-n", "-E",
                              rf"^(private |protected |@\[[^]]*\] )*(theorem|def|structure|abbrev) {re.escape(c)}( |$)",
                              "--", "src", "Test"], cwd=root, capture_output=True, text=True).stdout
        lines = [l for l in out.splitlines() if l]
        if len(lines) == 1:
            f, n, _ = lines[0].split(":", 2)
            return f"{f}:{n}"
        if len(lines) > 1:
            # disambiguate by the namespace's last component appearing in the file path or text
            hint = parts[-2] if len(parts) > 1 else ""
            pick = [l for l in lines if hint and hint in l.split(":", 2)[0]]
            if len(pick) == 1:
                f, n, _ = pick[0].split(":", 2)
                return f"{f}:{n}"
            return " / ".join(":".join(l.split(":", 2)[:2]) for l in lines)
    return "?"
print("| Declaration | Declared at | Axioms |")
print("| --- | --- | --- |")
for line in open(sys.argv[1], encoding="utf-8"):
    m = pat.match(line.strip())
    if m:
        ax = m.group("ax")
        ax = f"[{ax}]" if ax is not None else "none"
        print(f"| `{m.group('name')}` | `{site(m.group('name'))}` | `{ax}` |")
