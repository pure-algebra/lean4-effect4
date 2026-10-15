#!/usr/bin/env python3
"""Probe D: a census of the LCNF route's artifacts and syntax traversals (tested, finite: one run).

    python3 docs/research/2026-10-14-lowering-collation/probes/census.py .

It reads committed files only and changes nothing. Each count holds of the tree at the commit it
runs on.
"""
import re
import sys
from pathlib import Path

root = Path(sys.argv[1] if len(sys.argv) > 1 else ".")

# 1. The closures of the four LCNF artifacts, from their committed manifests.
def closure(name):
    rows = (root / "ocaml/gen" / f"closure-{name}.tsv").read_text().splitlines()[1:]
    return {r.split("\t")[0] for r in rows if r.strip()}

arts = ["fibers_gen", "machine_gen", "api_gen", "api_engine"]
sets = {a: closure(a) for a in arts}
print("1. closures (declarations per artifact)")
for a in arts:
    print(f"   {a}: {len(sets[a])}")
for small in ["machine_gen", "fibers_gen"]:
    inside = sets[small] & sets["api_gen"]
    print(f"   {small} inside api_gen: {len(inside)} of {len(sets[small])}")
print(f"   api_gen and api_engine share: {len(sets['api_gen'] & sets['api_engine'])}"
      f"; only api_gen: {len(sets['api_gen'] - sets['api_engine'])}"
      f"; only api_engine: {len(sets['api_engine'] - sets['api_gen'])}")
lines = {a: len((root / ("ocaml/engine" if a == "api_engine" else "ocaml/gen") / f"{a}.ml")
                .read_text().splitlines()) for a in arts}
print("   generated lines:", lines, "total", sum(lines.values()))

# 2. Hand traversals of the OCaml expression syntax: functions whose arms match `Ml.Expr`
#    constructors that the LCNF route never emits (an arm per constructor is a traversal).
expr_ctors = re.findall(r"^  \| (\w+)", (root / "src/OCaml5/Ml/Syntax.lean").read_text().split(
    "inductive Expr : Type where", 1)[1].split("inductive Arm", 1)[0], re.M)
print(f"\n2. Ml.Expr has {len(expr_ctors)} constructors")
emitters = ["src/OCaml5/Lcnf/Translate.lean", "src/OCaml5/Lcnf/Builtins.lean",
            "src/OCaml5/Lcnf/Externs.lean", "src/OCaml5/Lcnf/Native.lean",
            "src/OCaml5/Lcnf/Clock.lean", "src/OCaml5/Lcnf/ClockFlow.lean",
            "src/OCaml5/Tools/LcnfGen.lean"]
text = "\n".join((root / f).read_text() for f in emitters)
built = [c for c in expr_ctors if re.search(r"(Ml\.Expr\.|Expr\.|[^\w])\." + c + r"\b", text)
         or re.search(r"Ml\.Expr\." + c + r"\b", text)]
print(f"   constructors the route's sources build (by name): {len(built)}")
print("   ", " ".join(built))
trav = {}
for f in ["src/OCaml5/Ml/Render.lean", "src/OCaml5/Ml/Check.lean", "src/OCaml5/Lcnf/Builtins.lean",
          "tools/Conform/Effect4/LcnfMl.lean", "src/OCaml5/Lcnf/Translate.lean"]:
    src = (root / f).read_text()
    # a traversal: a definition whose body has an arm for `.letRecIn` or `.matchE` or `.tuple`
    defs = re.split(r"\n(?=(?:private |partial |protected )*(?:def|theorem) )", src)
    n = 0
    for d in defs:
        arms = set(re.findall(r"\|\s*\.(\w+)", d)) & set(expr_ctors)
        if len(arms) >= 6:
            n += 1
    trav[f] = n
print("   hand traversals (definitions with six or more Ml.Expr arms):", trav)

# 3. The OCaml estate by kind.
def count(paths):
    return sum(len(p.read_text().splitlines()) for p in paths)
ocaml = root / "ocaml"
gen_ml = [ocaml / "gen" / f"{a}.ml" for a in ["fibers_gen", "machine_gen", "api_gen"]] + [ocaml / "engine/api_engine.ml"]
effgen = [ocaml / "eff" / f for f in ["eff_types.ml", "eff_wire.ml", "eff_subterm.ml", "eff_json.ml", "eff_native.ml", "eff_layout.ml"]]
engine_hand = [p for p in (ocaml / "engine").glob("*.ml*") if p.name != "api_engine.ml"] + [ocaml / "engine/tools/api_engine_prelude.ml"]
cas_hand = [p for p in (ocaml / "engine/cas").glob("*.ml*")]
eff_hand = [ocaml / "eff/eff_frame.ml", ocaml / "eff/eff_json_text.ml"]
clock = list((ocaml / "clock").glob("*.ml*"))
tests = list((ocaml / "engine/test").rglob("*.ml")) + list((ocaml / "engine/cas/test").rglob("*.ml")) + list((ocaml / "eff/test").glob("*.ml"))
print("\n3. the OCaml estate, lines by kind")
for name, ps in [("made from LCNF", gen_ml), ("made by the EffGen templates", effgen),
                 ("hand engine (with the prelude)", engine_hand), ("hand CAS", cas_hand),
                 ("hand eff kernel", eff_hand), ("hand clock", clock), ("tests", tests)]:
    print(f"   {name}: {count(ps)} lines in {len(ps)} files")

# 4. The engine's extern table by row kind, and rows keyed on compiler-made names.
rows = [l.split() for l in (ocaml / "engine/externs.txt").read_text().splitlines()
        if l.strip() and not l.lstrip().startswith("#")]
kinds = {}
for r in rows:
    kinds[r[0]] = kinds.get(r[0], 0) + 1
made = [r[1] for r in rows if "_at_" in r[1] or "spec_" in r[1]]
print("\n4. externs.txt rows by kind:", kinds, "; keyed on a compiler-made name:", len(made))

# 5. The engine's hand modules that the engine reaches. A module reaches another when its `.ml`,
#    comments removed, names it. The roots are the drive loop and its two instances; the CAS
#    library is a second root. A module no root reaches is used by tests only.
def strip_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("(*", i):
            depth += 1; i += 2; continue
        if depth and s.startswith("*)", i):
            depth -= 1; i += 2; continue
        if not depth:
            out.append(s[i])
        i += 1
    return "".join(out)

eng = ocaml / "engine"
mods = {p.stem: strip_comments(p.read_text()) for p in list(eng.glob("*.ml")) + list((eng / "cas").glob("*.ml"))}
def names(m):
    body = mods[m]
    return {o for o in mods if o != m and re.search(r"\b" + o.capitalize() + r"\b", body)}
def reach(roots):
    seen, todo = set(), list(roots)
    while todo:
        m = todo.pop()
        if m in seen or m not in mods:
            continue
        seen.add(m)
        todo.extend(names(m))
    return seen
live = reach(["e4_engine", "api_engine_inst", "api_engine_ref", "corpora"])
cas = reach([m for m in mods if (eng / "cas" / (m + ".ml")).exists()])
hand = {m for m in mods if m != "api_engine"}
unused = sorted(hand - live - cas)
print("\n5. engine modules the drive loop reaches:", len(live & hand), "; the CAS adds:", len(cas - live))
print("   modules no root reaches (tests only):", len(unused))
print("  ", " ".join(unused))

# 6. The other OCaml syntax sorts: constructors, and those the route's sources build by name. A
#    name match over-counts (a `.char` can be an expression or a pattern), so a count is an upper
#    bound on what the route builds.
syn = (root / "src/OCaml5/Ml/Syntax.lean").read_text()
gen_files = emitters + ["src/OCaml5/Lcnf/Types.lean"]
gen_text = "\n".join((root / f).read_text() for f in gen_files)
for sort in ["Pat", "Ty", "Decl"]:
    body = syn.split(f"inductive {sort} where", 1)[1]
    body = re.split(r"\ninductive |\nstructure |\nderiving|\nnamespace ", body, maxsplit=1)[0]
    cs = re.findall(r"^  \| (\w+)", body, re.M)
    used = [c for c in cs if re.search(r"\." + c + r"\b", gen_text)]
    print(f"\n6. Ml.{sort}: {len(cs)} constructors; built by name, at most: {len(used)}")
