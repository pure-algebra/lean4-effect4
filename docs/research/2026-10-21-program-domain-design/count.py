"""Count the lines the note's section 6 reports: code lines of each declaration, docstrings and
blank lines excluded, in the probes (what the slice adds) and in the tree (what it moves or
deletes).

    python3 -I docs/research/2026-10-21-program-domain-design/count.py

A declaration starts at a line opening with def, theorem, structure, inductive, instance or abbrev,
and ends before the next blank line, docstring, comment, namespace or end line.
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
KEYWORD = re.compile(r"^(def|theorem|structure|inductive|instance|abbrev) (\S+)")
STOP = ("/--", "/-!", "--", "#", "end ", "namespace", "open ", "set_option")


def declarations(path, start=None, stop=None):
    """(kind, name, code lines) for each declaration between the two markers."""
    lines = path.read_text().splitlines()
    i = next(k for k, l in enumerate(lines) if l.startswith(start)) if start else 0
    j = next(k for k, l in enumerate(lines) if k > i and l.startswith(stop)) if stop else len(lines)
    found, current = [], None
    for line in lines[i:j]:
        match = KEYWORD.match(line)
        if match:
            if current:
                found.append(current)
            current = [match.group(1), match.group(2), 1]
        elif current is not None:
            if line.strip() == "" or line.startswith(STOP):
                found.append(current)
                current = None
            else:
                current[2] += 1
    if current:
        found.append(current)
    return found


def report(title, found, names=None):
    chosen = [d for d in found if names is None or d[1] in names]
    print(f"\n{title}")
    for kind, name, n in chosen:
        print(f"  {n:4d}  {kind} {name}")
    totals = {}
    for kind, _, n in chosen:
        key = "theorem" if kind == "theorem" else "definition"
        totals[key] = totals.get(key, 0) + n
    print("  total:", ", ".join(f"{k} {v}" for k, v in sorted(totals.items())))


def marked(path, name):
    lines = path.read_text().splitlines()
    return lines.index(f"-- END {name}") - lines.index(f"-- BEGIN {name}") - 1


probe_object = HERE / "probe-object.lean"
report("the object's operations and laws (probe-object.lean)",
       declarations(probe_object, "deriving instance DecidableEq for Object",
                    "/-! ## The to-do, as data"))
print(f"\n  carriers section: {marked(probe_object, 'carriers')} lines; "
      f"generated section: {marked(probe_object, 'generated')} lines")
generated = probe_object.read_text().splitlines()
begin, end = generated.index("-- BEGIN generated"), generated.index("-- END generated")
block, sizes = None, {}
for line in generated[begin + 1:end]:
    match = re.match(r"^namespace T_95_root_95__46_Effect4_46_Program_46_(\w+)C$", line)
    if match:
        block = match.group(1)
        sizes[block] = 0
    if block:
        sizes[block] += 1
    if line.startswith("end T_"):
        block = None
print("  generated blocks:", ", ".join(f"{k} {v}" for k, v in sizes.items()))

service = declarations(HERE / "probe-service.lean", "/-- **The names a target accepts",
                       "/-! ## The to-do")
# the probe's local copy of the carrier `Object` is no new code
report("the service view (probe-service.lean)", service,
       {d[1] for d in service if d[1] != "Object"})
report("the row names (probe-names.lean)", declarations(HERE / "probe-names.lean"))
report("the certificate's uniqueness (probe-certificate.lean)",
       declarations(HERE / "probe-certificate.lean"))
report("the saved session over the object (probe-record.lean)",
       declarations(HERE / "probe-record.lean"), {"Record", "save", "restore", "restore_save"})

print("\nthe tree, at HEAD")
report("  the service view in the printer (src/Effect4/Codegen/Print.lean)",
       declarations(ROOT / "src/Effect4/Codegen/Print.lean", "structure Service where",
                    "/-- A method's type in the service's shape"))
report("  the hand JSON of the certificate (tools/Compiler/Check.lean)",
       declarations(ROOT / "tools/Compiler/Check.lean"), {"certificate"})
report("  the tool round trip of inspect (tools/Compiler/Inspect.lean)",
       declarations(ROOT / "tools/Compiler/Inspect.lean"), {"opened", "ask", "reading"})
report("  the saved session (src/Effect4/Run/LiveRecord.lean)",
       declarations(ROOT / "src/Effect4/Run/LiveRecord.lean"), {"LiveRecord", "save", "restore"})
report("  the built program (src/Effect4/Api/Built.lean)",
       declarations(ROOT / "src/Effect4/Api/Built.lean"), {"Built", "ofProgram"})

# The construction sites of `Built` (section 8, points 1 and 8): an anonymous constructor with the
# certificate third, a record with the certificate's field punned or set, and an update of the names.
import subprocess
PATTERNS = [
    r"Built := ⟨",                     # an anonymous constructor of a named value
    r"Live\.open ⟨",                   # an anonymous constructor opened at once
    r"app, program, admitted",         # a punned record
    r"with rowNames :=",               # an update of the names
    r"rowNames := before\.rowNames",   # a law's statement
]
sites = []
for pattern in PATTERNS:
    out = subprocess.run(["git", "grep", "-nE", pattern, "--", "src/*.lean", "tools/*.lean",
                          "Test/*.lean"], cwd=ROOT, capture_output=True, text=True).stdout
    sites += [line.split(":")[0] + ":" + line.split(":")[1] for line in out.splitlines()]
run_contract = subprocess.run(["git", "grep", "-n", "admitted := ", "--", "Test/Run/RunContract.lean"],
                              cwd=ROOT, capture_output=True, text=True).stdout
sites += [line.split(":")[0] + ":" + line.split(":")[1] for line in run_contract.splitlines()]
print("\nconstruction sites of Built:")
for site in sorted(set(sites)):
    print("  " + site)
print(f"  total: {len(set(sites))}")
named = [s for s in sites if not s.startswith("src/")]
print(f"  in Test/: {len(set(named))}")
sys.exit(0)
