#!/usr/bin/env python3
"""Seat G: compare the statement half (up to the first `:=`) of each `#print` of a theorem in two
logs of probes/Statements.lean; print SAME/DIFF per theorem and the size of each proof half."""
import re, sys
def prints(path):
    text = open(path, encoding="utf-8").read()
    out = {}
    for m in re.finditer(r"^(?:@\[[^\n]*\]\s*)?theorem ([\w.']+) :", text, re.M):
        start = m.start()
        end = text.find(" :=", start)
        nxt = re.search(r"^(?:@\[|theorem |'|Effect4\.|##)", text[end:], re.M)
        proof_end = end + (nxt.start() if nxt else len(text) - end)
        out[m.group(1)] = (text[start:end], text[end:proof_end])
    return out
b, a = prints(sys.argv[1]), prints(sys.argv[2])
bad = 0
for k in b:
    same = k in a and b[k][0] == a[k][0]
    bad += not same
    print(f"{'SAME' if same else 'DIFF'} statement of {k}; proof half {len(b[k][1].splitlines())} lines before, "
          f"{len(a.get(k, ('', ''))[1].splitlines())} after")
sys.exit(1 if bad else 0)
