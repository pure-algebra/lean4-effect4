"""Finite source-closure check of the pinned C1 commit; no Lean gate claim."""
import re
import subprocess

REV = "96e3fd10935c55e709710b0922964f0192671606"
paths = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", REV, "src", "tools"], text=True).splitlines()
modules = {p.removeprefix("src/").removeprefix("tools/").removesuffix(".lean").replace("/", "."): p for p in paths if p.endswith(".lean")}
cache = {}

def read(module):
    if module not in cache:
        cache[module] = subprocess.check_output(["git", "show", REV + ":" + modules[module]], text=True)
    return cache[module]

def closure(start):
    seen, stack = set(), [start]
    while stack:
        module = stack.pop()
        if module in seen or module not in modules:
            continue
        seen.add(module)
        for line in read(module).splitlines():
            match = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+([^/-]+)", line)
            if match:
                stack.extend(match[1].split())
    return seen

for entry in ["Effect4.Author", "Effect4.Emit", "Effect4.Library", "Effect4.Run"]:
    reach = closure(entry)
    bad = sorted(m for m in reach if m == "Effect4.Laws" or m.startswith("Effect4.Laws."))
    assert not bad, (entry, bad)
    print(f"{entry}: {len(reach)} local modules; no Laws import")
before = subprocess.check_output(["git", "show", REV + "^:src/Effect4/Run.lean"], text=True)
after = read("Effect4.Run.Basic")
anchor = "namespace Effect4"
assert before[before.index(anchor):] == after[after.index(anchor):]
print("Run declaration body: byte-identical after the import and documentation header")
