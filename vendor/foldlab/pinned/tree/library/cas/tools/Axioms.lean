import Cas.Values.Json
import Gate
import Walk

/-!
# The axiom gate — `lake exe axioms`

The surface ledger reports an axiom census over THEOREMS. That is the
interesting population and it is not the whole one: a `def` by
well-founded recursion, an `instance` proved by `decide`, a structure
whose field type was elaborated through choice — each can carry an
axiom, and none of them is a theorem. This tool collects
`Lean.collectAxioms` for every declaration the surface ledger covers
and states the estate's axiom hygiene as a GATE rather than as a
column.

## The clean set

`propext`, `Classical.choice`, `Quot.sound` — `Walk.cleanAxioms`, which
the surface ledger reads too. A dependency outside it is a refusal
naming the declaration: `sorryAx` is an admitted hole, `ofReduceBool`
is a kernel-level trust of native evaluation, and anything else is
something nobody has ruled on. The refusal fires on emit as well as on
`--check`, so a hole cannot be regenerated into the tree quietly.

## The walk is mirrored, its rules are not

`Walk.collect` builds the surface ledger's rows and carries axioms only
for theorems, so this tool folds `env.constants` itself. Every RULE it
folds by is `Walk`'s own — `Walk.isGenerated`, `Walk.moduleOf`,
`Walk.kindOf` — so the two populations cannot drift apart without one
of those predicates moving. The order is `Walk.collect`'s total order:
module, then declaration name.

## Only the rows that carry something

A declaration that depends on no axiom has no row. Nearly all of them
do not, and a file with a row per declaration would be a second copy of
the surface ledger rather than a report about axioms. The count of them
is in the header, so the population is stated even though it is not
listed.
-/

open Lean

namespace Ax

/-- One declaration that depends on at least one axiom. -/
structure Row where
  module : String
  name : String
  kind : String
  axioms : List String

/-- Every declaration the surface ledger covers, with its axiom
dependencies, in `Walk.collect`'s total order. Declarations with no
dependency are kept here and dropped at the document — the counters
need them. -/
def collect (env : Environment) : CoreM (Array Row) := do
  let mut byModule : Std.HashMap Name (Array Row) := {}
  for (n, ci) in env.constants.toList do
    if n.isInternalDetail || n.isAnonymous || Walk.isGenerated n then continue
    unless n.getRoot == `Cas do continue
    let some m := Walk.moduleOf env n | continue
    unless m.getRoot == `Cas do continue
    let some kind ← Meta.MetaM.run' (Walk.kindOf env n ci) | continue
    let axs ← Lean.collectAxioms n
    let row : Row := { module := m.toString, name := n.toString, kind,
                       axioms := axs.toList.map Name.toString |>.mergeSort (· < ·) }
    byModule := byModule.insert m ((byModule.getD m #[]).push row)
  let sorted := byModule.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  return (sorted.map fun (_, rows) => rows.qsort (fun a b => a.name < b.name)).flatten

/-! ## The verdict -/

def cleanNames : List String := Walk.cleanAxioms.map Name.toString

/-- The axioms of a row that the clean set does not carry. -/
def unclean (r : Row) : List String :=
  r.axioms.filter fun a => !cleanNames.contains a

/-- The refusal, one line per offending declaration. The empty list is
the gate passing. -/
def violations (rows : Array Row) : List String :=
  rows.toList.filterMap fun r =>
    match unclean r with
    | [] => none
    | axs => some s!"{r.name} ({r.module}) depends on \
{String.intercalate ", " axs} — outside the clean set \
({String.intercalate ", " cleanNames})"

/-! ## The document -/

def rowJson (r : Row) : Cas.Json.Value :=
  .obj [("module", .str r.module), ("name", .str r.name),
        ("kind", .str r.kind),
        ("axioms", .arr (r.axioms.map Cas.Json.Value.str))]

/-- Every axiom any declaration depends on, in name order, with the
number of declarations that reach it. -/
def census (rows : Array Row) : List Cas.Json.Value :=
  let names := (rows.toList.flatMap (·.axioms)).eraseDups.mergeSort (· < ·)
  names.map fun a =>
    .obj [("axiom", .str a),
          ("declarations", .nat (rows.filter (·.axioms.contains a) |>.size))]

/-- The gate's emitted header. The document declared no version before
this one, so its `schemaVersion` opens at 1. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "axioms"
  module := "library/cas/tools/Axioms.lean"

def document (rows : Array Row) : String :=
  let carrying := rows.filter (fun r => !r.axioms.isEmpty)
  let beyond := rows.toList.filterMap fun r =>
    if (unclean r).isEmpty then none else some r.name
  Cas.Json.render (emitted.obj [
    ("library", .str "Cas"),
    ("cleanSet", .arr (cleanNames.map Cas.Json.Value.str)),
    ("counters", .obj [
      ("declarations", .nat rows.size),
      ("axiomFree", .nat (rows.size - carrying.size)),
      ("withAxioms", .nat carrying.size),
      ("beyondCleanSet", .nat beyond.length)]),
    ("census", .arr (census rows)),
    ("beyondCleanSet", .arr (beyond.map Cas.Json.Value.str)),
    ("declarations", .arr (carrying.toList.map rowJson))]) ++ "\n"

end Ax

/-! ## The tool -/

def outPath : System.FilePath := "meta" / "out" / "axioms.META.json"

def regen : String := "lake exe axioms"

/-- Emit or check the fixture, THEN refuse an unclean dependency. The
two failures are separate: stale bytes mean the report was not
regenerated, and a violation means the library depends on something
nobody ruled on. Both are red; only the second is a fact about the
mathematics. -/
unsafe def gate (args : List String) : IO Unit := do
  let pending ← IO.mkRef ([] : List String)
  let fixtures : IO (List Gate.Fixture) := do
    enableInitializersExecution
    let rows ← Walk.run Ax.collect
    pending.set (Ax.violations rows)
    let carrying := rows.filter (fun r => !r.axioms.isEmpty)
    return [⟨outPath, Ax.document rows,
             s!"{carrying.size} of {rows.size} declarations carry an axiom"⟩]
  Gate.main regen fixtures args
  let vs ← pending.get
  unless vs.isEmpty do
    IO.eprintln s!"\nAXIOM GATE: UNCLEAN — {vs.length} declaration(s).\n"
    for v in vs do IO.eprintln s!"  - {v}"
    IO.eprintln "\nThe clean set is propext, Classical.choice, Quot.sound. \
A `sorryAx` is an admitted hole and `ofReduceBool` trusts native \
evaluation in the kernel; either is a ruling, not a regeneration. \
Close the hole, or widen the set in tools/Walk.lean with the ruling \
that widened it."
    throw (IO.userError
      s!"{vs.length} declaration(s) outside the clean set")

unsafe def main := gate
