#!/usr/bin/env python3
"""Seat P's line counter: the lines of a declaration (its header to the line before the next
top-level item, trailing blank lines and its own docstring excluded), in a file of the worktree or
at a git revision ("rev:path"). Usage: measure.py <table> ; tables: prod, named, all.
Every count in note.md's tables comes from this script's output (logs/measure.log)."""
import re, subprocess, sys

ROOT = "/Users/pooks/Dev/lean4-effect4-probe-P"
P = "docs/research/2026-10-01-type-language-probe/P/probes/"
TOP = re.compile(r"^(?:@\[|/--|/-!|#|end\b|namespace\b|section\b|mutual\b|open\b|set_option\b|"
                 r"variable\b|(?:private |protected |noncomputable |partial )*"
                 r"(?:theorem|lemma|def|abbrev|inductive|structure|instance|class|example|notation)\b)")

def read(src):
    if ":" in src and not src.startswith("/"):
        rev, path = src.split(":", 1)
        return subprocess.run(["git", "-C", ROOT, "show", f"{rev}:{path}"], capture_output=True,
                              text=True, check=True).stdout.splitlines()
    return open(f"{ROOT}/{src}").read().splitlines()

def block(src, name):
    lines = read(src)
    head = re.compile(r"^(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev|inductive|"
                      r"structure)\s+" + re.escape(name) + r"(?:\s|$|\.|:|\()")
    for i, l in enumerate(lines):
        if head.match(l):
            j = i + 1
            while j < len(lines) and not TOP.match(lines[j]):
                j += 1
            while j > i + 1 and lines[j - 1].strip() == "":
                j -= 1
            return i + 1, j - i
    return None, 0

def row(label, a, an, b, bn):
    la, na = block(a, an)
    lb, nb = block(b, bn)
    fa = f"{a.split(':')[-1].split('/')[-1]}:{la}" if la else "—"
    fb = f"{b.split(':')[-1].split('/')[-1]}:{lb}" if lb else "—"
    print(f"| {label} | {fa} | {na} | {fb} | {nb} | {nb - na:+d} |")

PROD = [  # (label, production file, name, copy file, name)
  ("`Ty` (constructors)", "src/Effect4/Program/Ty.lean", "Ty", P + "P2Ty.lean", "Ty"),
  ("`Ty.key`", "src/Effect4/Program/Ty.lean", "key", P + "P2Ty.lean", "key"),
  ("`Ty.renderRaw`", "src/Effect4/Program/Ty.lean", "renderRaw", P + "P2Ty.lean", "renderRaw"),
  ("`Ty.members`", "src/Effect4/Program/Ty.lean", "members", P + "P2Ty.lean", "members"),
  ("`Ty.closed`", "src/Effect4/Program/Ty.lean", "closed", P + "P2Ty.lean", "closed"),
  ("`Ty.isMember`", "src/Effect4/Program/Ty.lean", "isMember", P + "P2Ty.lean", "isMember"),
  ("`Ty.sub`", "src/Effect4/Program/Ty.lean", "sub", P + "P2Ty.lean", "sub"),
  ("`Ty.instantiate`", "src/Effect4/Program/Ty.lean", "instantiate", P + "P2Ty.lean", "instantiate"),
  ("`Ty.normalize`", "src/Effect4/Program/Ty.lean", "normalize", P + "P2Ty.lean", "normalize"),
  ("`Ty.Normal`", "src/Effect4/Program/Ty.lean", "Normal", P + "P2Ty.lean", "Normal"),
  ("`normal_normalize`", "src/Effect4/Program/Ty.lean", "normal_normalize", P + "P2Ty.lean", "normal_normalize"),
  ("`sub_union_right`", "src/Effect4/Program/Ty.lean", "sub_union_right", P + "P2Ty.lean", "sub_union_right"),
  ("`sub_lit_string`", "src/Effect4/Program/Ty.lean", "sub_lit_string", P + "P2Ty.lean", "sub_lit_string"),
  ("`sub_unknown`", "src/Effect4/Program/Ty.lean", "sub_unknown", P + "P2Ty.lean", "sub_unknown"),
  ("`TyView.args` (gen.)", "src/Effect4/Laws/Program/TyView.lean", "args", P + "P3View.lean", "args"),
  ("`TyView.sameHead` (gen.)", "src/Effect4/Laws/Program/TyView.lean", "sameHead", P + "P3View.lean", "sameHead"),
  ("`TyView.litRule` → the table (gen.)", "src/Effect4/Laws/Program/TyView.lean", "litRule", P + "P2Ty.lean", "leafEdges"),
  ("`sameHead_trans` (gen.)", "src/Effect4/Laws/Program/TyView.lean", "sameHead_trans", P + "P3View.lean", "sameHead_trans"),
  ("`eq_of_sameHead` (gen.)", "src/Effect4/Laws/Program/TyView.lean", "eq_of_sameHead", P + "P3View.lean", "eq_of_sameHead"),
  ("`sub_eq_false_of_not_sameHead` (gen.)", "src/Effect4/Laws/Program/TyView.lean", "sub_eq_false_of_not_sameHead", P + "P3View.lean", "sub_eq_false_of_not_sameHead"),
  ("`sub_eq_argsBelow_of_sameHead` (gen.)", "src/Effect4/Laws/Program/TyView.lean", "sub_eq_argsBelow_of_sameHead", P + "P3View.lean", "sub_eq_argsBelow_of_sameHead"),
  ("`sub_eq_args` (gen.)", "src/Effect4/Laws/Program/TyView.lean", "sub_eq_args", P + "P3View.lean", "sub_eq_args"),
  ("`argsBelow_antisymm` (gen.)", "src/Effect4/Laws/Program/TyView.lean", "argsBelow_antisymm", P + "P3View.lean", "argsBelow_antisymm"),
  ("`sub_trans_core`", "src/Effect4/Laws/Program/TypeAlgebra.lean", "sub_trans_core", P + "P4Algebra.lean", "sub_trans_core"),
  ("`sub_antisymm_normal`", "src/Effect4/Laws/Program/TypeAlgebra.lean", "sub_antisymm_normal", P + "P4Algebra.lean", "sub_antisymm_normal"),
  ("`sub_normalize_of_sub`", "src/Effect4/Laws/Program/TypeAlgebra.lean", "sub_normalize_of_sub", P + "P4Algebra.lean", "sub_normalize_of_sub"),
  ("`normal_args`", "src/Effect4/Laws/Program/TypeAlgebra.lean", "normal_args", P + "P4Algebra.lean", "normal_args"),
  ("`normal_members`", "src/Effect4/Laws/Program/TypeAlgebra.lean", "normal_members", P + "P4Algebra.lean", "normal_members"),
  ("`sub_member_right_iff`", "src/Effect4/Laws/Program/TypeAlgebra.lean", "sub_member_right_iff", P + "P4Algebra.lean", "sub_member_right_iff"),
  ("`hasTy_normalize`", "src/Effect4/Laws/Program/TypeAlgebra.lean", "hasTy_normalize", P + "P4Check.lean", "hasTy_normalize"),
  ("`Val.hasTy`", "src/Effect4/Program/Typed.lean", "Val.hasTy", P + "P4Check.lean", "hasTy"),
  ("`cata_admits_sub` / copy's `hasTy_sub`", "src/Effect4/Laws/Program/Admits.lean", "cata_admits_sub", P + "P4Check.lean", "hasTy_sub"),
  ("`Fits`", "src/Effect4/Laws/Program/Typed/Membership.lean", "Fits", P + "P5Fits.lean", "Fits"),
  ("`fits_hasTy`", "src/Effect4/Laws/Program/Typed/Membership.lean", "fits_hasTy", P + "P5Fits.lean", "fits_hasTy"),
  ("`fits_live`", "src/Effect4/Laws/Program/Typed/Membership.lean", "fits_live", P + "P5Fits.lean", "fits_live"),
  ("`fits_map`", "src/Effect4/Laws/Program/Typed/Membership.lean", "fits_map", P + "P5Fits.lean", "fits_map"),
  ("`fits_sub`", "src/Effect4/Laws/Program/Typed/Membership.lean", "fits_sub", P + "P5Fits.lean", "fits_sub"),
  ("`isTagged`", "src/Effect4/Program/Ty.lean", "isTagged", P + "P7Tagged.lean", "isTagged"),
  ("`payloadOf`", "src/Effect4/Program/Ty.lean", "payloadOf", P + "P7Tagged.lean", "payloadOf"),
  ("`decodeRaw` → `decodeRawC`", "src/Effect4/Schema/Codec.lean", "decodeRaw", P + "P8Codec.lean", "decodeRawC"),
  ("`ofSchema` → `ofSchemaC`", "src/Effect4/Schema/Bridge.lean", "ofSchema", P + "P8Schema.lean", "ofSchemaC"),
  ("`ofSchema_schema` → `ofSchemaC_schema`", "src/Effect4/Schema/Bridge.lean", "ofSchema_schema", P + "P8Schema.lean", "ofSchemaC_schema"),
]

POS = "1b069d15:" + P   # the positional record clause (questions 2 and 3)
POS6 = "8fa1247f:" + P
POS7 = "056ca30b:" + P
NAMED = [  # (label, positional file, name, named file, name)
  ("check: the record read", POS + "P4Check.lean", "fieldsHasTy", P + "P4Check.lean", "namedHasTy"),
  ("check: its monotonicity", POS + "P4Check.lean", "fieldsHasTy_mono", P + "P4Check.lean", "namedHasTy_mono"),
  ("check: `hasTy_record`", POS + "P4Check.lean", "hasTy_record", P + "P4Check.lean", "hasTy_record"),
  ("check: `hasTy_normalize_record`", POS + "P4Check.lean", "hasTy_normalize_record", P + "P4Check.lean", "hasTy_normalize_record"),
  ("check: `record_sub_not_complete`", POS + "P4Check.lean", "record_sub_not_complete", P + "P4Check.lean", "record_sub_not_complete"),
  ("Fits: the record predicate", POS + "P5Fits.lean", "FieldsFit", P + "P5Fits.lean", "NamedFit"),
  ("Fits: the optional slot", POS + "P5Fits.lean", "slotFits", P + "P5Fits.lean", "NamedFit"),
  ("Fits: `fits_record_inv`", POS + "P5Fits.lean", "fits_record_inv", P + "P5Fits.lean", "fits_record_inv"),
  ("Fits: read implies check", POS + "P5Fits.lean", "fieldsFit_hasTy", P + "P5Fits.lean", "namedFit_hasTy"),
  ("Fits: liveness", POS + "P5Fits.lean", "fieldsFit_live", P + "P5Fits.lean", "namedFit_live"),
  ("Fits: growth / monotonicity", POS + "P5Fits.lean", "fieldsFit_map", P + "P5Fits.lean", "namedFit_mono"),
  ("Fits: `fits_normalize_record`", POS + "P5Fits.lean", "fits_normalize_record", P + "P5Fits.lean", "fits_normalize_record"),
  ("projection: the function", POS + "P5Fits.lean", "project", P + "P5Fits.lean", "project"),
  ("projection: field lookup", POS + "P5Fits.lean", "slotOf", P + "P5Fits.lean", "lookupName"),
  ("projection: lookup law", POS + "P5Fits.lean", "fieldsFit_slotOf", P + "P5Fits.lean", "namedFit_lookup"),
  ("projection: required present", POS + "P5Fits.lean", "slotOf_none", P + "P5Fits.lean", "namedFit_required"),
  ("projection: assembled value fits", POS + "P5Fits.lean", "fieldsFit_of_forall", P + "P5Fits.lean", "namedFit_of_forall"),
  ("projection: absent optional skipped", POS + "P5Fits.lean", "fieldsFit_of_forall", P + "P5Fits.lean", "namedFit_skip"),
  ("projection: `fits_project`", POS + "P5Fits.lean", "fits_project", P + "P5Fits.lean", "fits_project"),
  ("inhabitance: sound step", POS6 + "P6Inhabited.lean", "fieldsFit_inhabited", P + "P6Inhabited.lean", "namedFit_inhabited"),
  ("inhabitance: fresh-world step", POS6 + "P6Inhabited.lean", "fieldsFit_fresh", P + "P6Inhabited.lean", "namedFit_fresh"),
  ("tag: the tag in the value", POS7 + "P7Tagged.lean", "fits_tagged_head", P + "P7Tagged.lean", "fits_tagged_name"),
  ("tag: the discriminant-first slot", POS7 + "P7Tagged.lean", "tag_head", P + "P7Tagged.lean", "tag_head"),
  ("tag: disjointness", POS7 + "P7Tagged.lean", "tagged_disjoint", P + "P7Tagged.lean", "tagged_disjoint"),
]

FAMILIES = [  # (label, production file, name prefix, copy file, names)
  ("`hasTy_normalize` with its named cases", "src/Effect4/Laws/Program/TypeAlgebra.lean", "hasTy_normalize",
   P + "P4Check.lean", ["hasTy_normalize", "hasTy_normalize_prod", "hasTy_normalize_record",
                        "hasTy_normalize_tuple", "hasTy_normalize_app"]),
  ("the leaf rule and its laws (gen.)", "src/Effect4/Laws/Program/TyView.lean", "litRule",
   P + "P3View.lean", ["LeafHead.mem_all", "LeafPath", "leafReach_sound", "leafLe_refl", "leafLe_trans",
                       "leafLe_antisymm", "leafLe_of_edge", "leafEdge_ne", "leafLe_iff_path",
                       "leafEdges_acyclic", "leafHead_facts", "leafRule_eq_true", "leafRule_of_heads",
                       "leafRule_of_edge", "leafRule_args", "leafRule_trans", "leafRule_asymm",
                       "leafRule_ne_unknown", "leafRule_sameHead", "leafRule_normalize"]),
]

def prefixed(src, prefix):
    lines = read(src)
    head = re.compile(r"^(?:private |protected |noncomputable )*(?:theorem|lemma|def)\s+(" +
                      re.escape(prefix) + r"[A-Za-z0-9_'.?]*)")
    names = []
    for l in lines:
        m = head.match(l)
        if m and m.group(1) not in names:
            names.append(m.group(1))
    return names

def family(label, a, prefix, b, bnames):
    an = prefixed(a, prefix)
    na = sum(block(a, n)[1] for n in an)
    nb = sum(block(b, n)[1] for n in bnames)
    print(f"| {label} | {len(an)} decl. in {a.split('/')[-1]} | {na} | {len(bnames)} decl. in {b.split('/')[-1]} | {nb} | {nb - na:+d} |")

def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which in ("prod", "all"):
        print("| production declaration | today (bff50631) | lines | on the copy | lines | change |")
        print("| --- | --- | --- | --- | --- | --- |")
        for r in PROD: row(*r)
        for f in FAMILIES: family(*f)
        print()
    if which in ("named", "all"):
        print("| what | positional (commit) | lines | named (head) | lines | change |")
        print("| --- | --- | --- | --- | --- | --- |")
        for r in NAMED: row(*r)

main()
