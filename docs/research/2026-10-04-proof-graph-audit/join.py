"""Join the reach probe's unconsumed theorems against battery and tool mentions.

Usage: python3 docs/research/2026-10-04-proof-graph-audit/join.py <reach.tsv>
Reads the `.ilean` reference index of Test and the tool roots, then a textual scan of
Test/, tools/, scripts/ and three core documents. Prints the tiers the audit quotes.
"""
import collections, glob, json, re, sys

rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1]) if not l.startswith("#")]
print("tiers:", dict(collections.Counter(r[0] for r in rows)))
files = glob.glob(".lake/build/lib/lean/Test/**/*.ilean", recursive=True)
for root in ["ProofGraph", "Tools", "Conform", "Drivers", "Effect4Gen"]:
    files += glob.glob(f".lake/build/lib/lean/{root}/**/*.ilean", recursive=True)
mentioned = set()
for f in files:
    for key in json.load(open(f))["references"]:
        try:
            mentioned.add(json.loads(key)["c"]["n"])
        except (KeyError, ValueError):
            pass
c = [r for r in rows if r[0] == "C"]
c_ref = [r for r in c if r[1] in mentioned]
rest = [r for r in c if r[1] not in mentioned]
text = ""
for f in (glob.glob("Test/**/*.lean", recursive=True) + glob.glob("tools/**/*.lean", recursive=True)
          + glob.glob("scripts/**/*.py", recursive=True)
          + ["docs/core/semantics.md", "docs/core/system-map.md", "docs/RUNTIME-COVERAGE.md"]):
    text += open(f).read() + "\n"
words = set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.!?]*", text))
named = [r for r in rest if r[1] in words or r[1].split(".")[-1] in words]
print(f"ilean files {len(files)}; C {len(c)}: referenced {len(c_ref)}, named in text {len(named)}, "
      f"no mention {len(rest) - len(named)}")
