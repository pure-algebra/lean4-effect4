import Gate
import Obl
import Law

/-!
# The debt projection — `lake exe debts`

One document naming everything this library currently owes, collected
from the two places that already record it and from nowhere else:

- the docstrings, through `Obl` — every obligation row whose state is
  `owed`, `parked` or `pin-pending`. `discharged`, `un-parked`,
  `obligation` and `sub-obligation` are history or framing and are not
  debts;
- the ruling registry, through `Law` — every UNBOUND row, which is the
  law index's own word for a ruling no declaration enforces yet. The
  law gate counts those and deliberately does not fail on them; this
  is where they are collected rather than merely counted.

The projection MINTS nothing. Both halves are read from the authority
that already computes them — `Obl.scanAll` and `Law.unboundOf` — so a
debt appears here because a docstring or the registry says it, and
disappears when that source does. `--check` is the byte gate: a debt
that quietly evaporates is a red diff.

## The named join

A debt written in the structured form (`owed(judge-stable)`) carries
its id, and a row that says `discharges(judge-stable)` elsewhere in the
tree settles it. Where both exist the debt row names the modules that
discharge it (`settledBy`) — it stays in the document, because the
marker is still written and striking it is the work the row is asking
for. An unnamed debt cannot be joined at all, which is the argument
for naming one.

## What v0 does NOT read

**Receipts and `docs/SPECS.md`.** Both are real debt registers and
neither is in the Lean environment: the receipts are JSON under
`.reference/provenance/`, and SPECS is prose. Reading them is a file
walk outside this tool's import closure, which is a second tool's job
(`EnvLedger` is the precedent for a config-reading emitter). The
document says what the compiled library says, and does not pretend to
be the estate's whole debt.
-/

open Lean

namespace Debt

/-! ## The two sources -/

/-- The modules that discharge `id`, by name. A `discharges(id)` row is
an `Obl` row with state `discharged` carrying that id — the same scan,
read for its other direction. -/
def settledBy (rows : List Obl.Row) (id : String) : List String :=
  ((rows.filter fun r =>
    r.state == "discharged" && r.id == some id).map (·.module)).eraseDups

/-- One docstring debt. `id` and `settledBy` appear only when the
marker names its debt; every other field is on every row. -/
def docstringJson (rows : List Obl.Row) (r : Obl.Row) : Cas.Json.Value :=
  let settled := match r.id with
    | none => []
    | some i => settledBy rows i
  .obj (
    [("source", Cas.Json.Value.str "docstring"),
     ("state", .str r.state),
     ("module", .str r.module)] ++
    -- Where to open it. A ruling row carries neither, which is why the
    -- shape spells both optional: a registry entry has no source.
    Obl.anchorJson r ++
    (match r.declaration with
     | some d => [("declaration", Cas.Json.Value.str d)]
     | none => []) ++
    (match r.id with
     | some i => [("id", Cas.Json.Value.str i)]
     | none => []) ++
    (if settled.isEmpty then []
     else [("settledBy", Cas.Json.Value.arr (settled.map Cas.Json.Value.str))]) ++
    [("keyword", .str r.keyword), ("excerpt", .str r.excerpt)])

/-- One unbound ruling, in the registry's own words. -/
def rulingJson (r : Law.Ruling) : Cas.Json.Value :=
  .obj [("source", .str "ruling"), ("state", .str "unbound"),
        ("id", .str r.id), ("statement", .str r.statement)]

/-- The registry rows the law index reports as UNBOUND, as rows rather
than as ids: `Law.unboundOf` is the authority for which ids those are,
and the registry is the authority for what each one says. -/
def unboundRulings (claims : List Law.Claim) : List Law.Ruling :=
  let ids := Law.unboundOf Law.registry claims
  Law.registry.filter fun r => ids.contains r.id

/-! ## The document -/

def stateCount (rows : List Obl.Row) (s : String) : Nat :=
  (rows.filter (·.state == s)).length

/-- The debts, in reading order: the docstring rows in the obligation
ledger's own order (module blocks, then declarations, both in `Walk`'s
total order), then the unbound rulings in registry order. Counters
per source, so a document that grew can be read at its head. -/
def document (e : Gate.Emitted) (rows : List Obl.Row)
    (rulings : List Law.Ruling) : String :=
  let debts := rows.filter Obl.isDebt
  let named := debts.filter (·.id.isSome)
  let settled := named.filter fun r =>
    match r.id with
    | none => false
    | some i => !(settledBy rows i).isEmpty
  Cas.Json.render (e.obj [
    ("library", .str "Cas"),
    ("convention", .str
      "owed(<id>): <text> names a debt in a docstring and \
discharges(<id>): <text> settles it; an UNBOUND registry row is a \
ruling no declaration enforces yet"),
    ("counters", .obj [
      ("debts", .nat (debts.length + rulings.length)),
      ("docstrings", .nat debts.length),
      ("owed", .nat (stateCount debts "owed")),
      ("parked", .nat (stateCount debts "parked")),
      ("pinPending", .nat (stateCount debts "pin-pending")),
      ("named", .nat named.length),
      ("settled", .nat settled.length),
      ("unboundRulings", .nat rulings.length)]),
    ("debts", .arr (debts.map (docstringJson rows) ++ rulings.map rulingJson))])
    ++ "\n"

end Debt

/-! ## The tool -/

def outPath : System.FilePath := "meta" / "out" / "debts.META.json"

def regen : String := "lake exe debts"

/-- The projection's emitted header. The document declared no version
before this one, so its `schemaVersion` opens at 1. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "debts"
  module := "library/cas/tools/Debts.lean"

/-- One import of the library, both projections. `Obl.entries` and
`Law.claimsOf` each fold the same environment; the walk is the cost,
and it is paid once. -/
unsafe def fixtures : IO (List Gate.Fixture) := do
  enableInitializersExecution
  let (rows, claims) ← Walk.run fun env => do
    let rows := Obl.scanAll (← Obl.entries env)
    let claims := Law.claimsOf (← Walk.collect env)
    return (rows, claims)
  let rulings := Debt.unboundRulings claims
  let debts := rows.filter Obl.isDebt
  return [⟨outPath, Debt.document emitted rows rulings,
           s!"{debts.length} docstring debts, {rulings.length} unbound rulings"⟩]

unsafe def main := Gate.main regen fixtures
