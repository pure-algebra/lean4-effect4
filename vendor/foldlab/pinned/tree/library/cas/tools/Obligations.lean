import Gate
import Obl

/-!
# The obligation ledger — `lake exe obligations`

Dozens of named obligations are load-bearing prose in this library's
docstrings, and nothing reads them. `SCHEMA-MATERIALIZATION.md`'s
defect register has already started drifting from the tree — the line
it still carries about `Cas/Backend/Ts.lean` importing
`Cas.Schema.Foreign` names an import that was removed in `34145109`,
and the file now imports nothing at all. That is the failure mode a
prose ledger has and a generated one does not.

This tool extracts what is already written. It mints no convention,
asks for no new registry, and rules on nothing: it reads the
docstrings the estate has been writing for months, matches a CLOSED
keyword set against them, and emits the result as data under a byte
gate. `--check` is that gate in `check:cas`: a docstring that quietly
loses its `owed`, an obligation that reverts from `discharged`, a
health counter that goes stale — each is a red diff.

The scan itself — the keyword set, the boundary rules, the excerpt
shape, the named `owed(id)` form and the document — is `Obl`, which the
debt projection reads too. This root is the ledger's fixture, its
controls and its verdict, nothing more.

## What it does NOT deliver

**Since-when.** Age is not derivable from the environment: declaration
ranges cover under half the library and carry no date at all. Age
needs a `git log -S` join, which is a shell step outside this tool.
The ledger says what and where and in what state, and does not pretend
to say when.

## Discharged rows STAY

The ledger is history, not hygiene: a discharged obligation keeps its
row, so the audit trail is the artifact rather than a memory of one.
This is provisional pending the operator's ruling.
-/

open Lean

/-! ## The tool -/

def outPath : System.FilePath := "meta" / "out" / "obligations.META.json"

def regen : String := "lake exe obligations"

/-- The ledger's emitted header. The document declared no version
before this one, so its `schemaVersion` opens at 1. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "obligations"
  module := "library/cas/tools/Obligations.lean"

unsafe def fixtures : IO (List Gate.Fixture) := do
  enableInitializersExecution
  let (rows, empties) ← Walk.run fun env => do
    let rows := Obl.scanAll (← Obl.entries env)
    return (rows, Obl.emptyDenotationCount env)
  let some emptyDenotations := empties
    | throw (IO.userError
        "Cas.Schema.El declares no equations — the ledger cannot count \
the value plane's Empty denotations")
  let health : Obl.Health :=
    { formless := Obl.formlessCount, emptyDenotations }
  return [⟨outPath, Obl.document emitted health rows,
           s!"{rows.length} obligations"⟩]

/-! ## The controls

A gate that cannot fail proves nothing. Each control runs the scan
over a SYNTHETIC corpus and states what must hold; the planted defects
are the three the design names — a docstring that loses its keyword, a
state that reverts, a counter that goes stale — plus the boundary and
double-count rules the closed keyword set stands on, and the rules the
named form adds: an id is carried, a bare marker still reports, a
second named marker is its own row, and `discharges` counts only when
it names something. -/

namespace Obl

/-- The synthetic corpus's module, and the source anchor derived from
it by the same rule the real walk uses — so the controls exercise the
path derivation rather than a hand-typed string. -/
private def probeModule : Name := `Cas.Probe

private def ent (decl doc : String) : Entry :=
  { module := probeModule.toString, file := Walk.sourceOf probeModule,
    declaration := some decl, line := some 7, doc }

/-- Module blocks first, then declarations — the order `entries` reads
the real environment in. -/
private def baseCorpus : List Entry := [
  { module := probeModule.toString, file := Walk.sourceOf probeModule,
    declaration := none, line := some 3,
    doc := "CORPUS PIN PENDING — the citation is not G0-pinned." },
  ent "a" "The pin is owed.",
  ent "b" "A NAMED OBLIGATION, discharged 2026-08-29."]

private def baseHealth : Health := { formless := 1, emptyDenotations := 4 }

private def baseDoc : String :=
  document _root_.emitted baseHealth (scanAll baseCorpus)

structure Control where
  name : String
  /-- What the control asserts. -/
  claim : String
  holds : Bool

/-- The states a corpus reports, in row order. -/
private def statesOf (es : List Entry) : List String :=
  (scanAll es).map (·.state)

/-- The ids a corpus reports, in row order. -/
private def idsOf (es : List Entry) : List (Option String) :=
  (scanAll es).map (·.id)

def controls : List Control :=
  let base := scanAll baseCorpus
  [ { name := "baseline"
    , claim := "the base corpus reports owed, obligation, discharged, \
pin-pending"
    , holds := statesOf baseCorpus ==
        ["pin-pending", "owed", "obligation", "discharged"] },
    { name := "keyword lost"
    , claim := "striking `owed` from a docstring drops its row and \
moves the document"
    , holds :=
        let mutated := baseCorpus.map fun e =>
          if e.declaration == some "a" then { e with doc := "The pin is due." }
          else e
        (scanAll mutated).length + 1 == base.length &&
          document _root_.emitted baseHealth (scanAll mutated) != baseDoc },
    { name := "state reverted"
    , claim := "a `discharged` row that reverts to `owed` moves the \
document"
    , holds :=
        let mutated := baseCorpus.map fun e =>
          if e.declaration == some "b" then
            { e with doc := "A NAMED OBLIGATION, owed again." }
          else e
        document _root_.emitted baseHealth (scanAll mutated) != baseDoc &&
          (scanAll mutated).any (fun r =>
            r.declaration == some "b" && r.state == "owed") },
    { name := "counter stale"
    , claim := "a health counter that drifts moves the document even \
though no row changed"
    , holds :=
        document _root_.emitted { baseHealth with formless := 0 } base != baseDoc &&
          document _root_.emitted { baseHealth with emptyDenotations := 3 } base != baseDoc },
    { name := "word boundary"
    , claim := "`borrowed`, `allowed` and `showed` are not `owed`"
    , holds := statesOf [ent "c" "The idiom is borrowed; nothing is \
allowed and nothing showed."] == [] },
    { name := "un-parked not double-counted"
    , claim := "`un-parked` reports once, as `un-parked`"
    , holds := statesOf [ent "d" "This leg is un-parked."] == ["un-parked"] },
    { name := "sub-obligation not double-counted"
    , claim := "`sub-obligation` reports once, as `sub-obligation`"
    , holds := statesOf [ent "e" "SUB-OBLIGATION 1 stands."] ==
        ["sub-obligation"] },
    { name := "case-insensitive, verbatim keyword"
    , claim := "`OBLIGATION` is found and quoted in its own casing"
    , holds :=
        match scanAll [ent "f" "A NAMED OBLIGATION."] with
        | [r] => r.state == "obligation" && r.keyword == "OBLIGATION"
        | _ => false },
    { name := "module docstring counted"
    , claim := "a module block's `PIN PENDING` reaches the counter"
    , holds := stateCount base "pin-pending" == 1 &&
        base.any (fun r => r.declaration.isNone && r.state == "pin-pending") },
    { name := "excerpt is one line"
    , claim := "a hard-wrapped docstring excerpts without its wrapping"
    , holds :=
        match scanAll [ent "g" "the row is\n  owed until the\n  pin lands"] with
        | [r] => r.excerpt == "the row is owed until the pin lands"
        | _ => false },
    { name := "the named form carries its id"
    , claim := "`owed(judge-stable)` reports state owed under that id, \
and moves the document a bare `owed` would not"
    , holds :=
        let named := ent "h" "owed(judge-stable): the definition."
        statesOf [named] == ["owed"] && idsOf [named] == [some "judge-stable"] &&
          document _root_.emitted baseHealth (scanAll [named]) !=
            document _root_.emitted baseHealth (scanAll [ent "h" "owed: the definition."]) },
    { name := "a bare marker still reports, with no id"
    , claim := "the convention is additive — every row that had no id \
still has none"
    , holds := (idsOf baseCorpus).length == base.length &&
        (idsOf baseCorpus).all (·.isNone) },
    { name := "two named debts, two rows"
    , claim := "a docstring owing two NAMED things reports both, where \
two bare `owed`s still report one"
    , holds :=
        idsOf [ent "i" "owed(alpha): one. And owed(beta): two."] ==
            [some "alpha", some "beta"] &&
          statesOf [ent "j" "owed here. And owed there."] == ["owed"] },
    { name := "`discharges` counts only when it names"
    , claim := "the prose verb is invisible and the marker is not"
    , holds :=
        statesOf [ent "k" "the grammar discharges that premise"] == [] &&
          statesOf [ent "l" "discharges(judge-stable): defined here"] ==
            ["discharged"] },
    { name := "an id is short-kebab or it is not an id"
    , claim := "a parenthetical that is not an id leaves the row bare \
rather than inventing one"
    , holds :=
        idsOf [ent "m" "owed(Judge Stable): prose."] == [none] &&
          idsOf [ent "n" "owed (judge-stable): a space is not the form."]
            == [none] },
    { name := "the id moves the document"
    , claim := "renaming a debt is a visible diff"
    , holds :=
        document _root_.emitted baseHealth (scanAll [ent "o" "owed(alpha): one."]) !=
          document _root_.emitted baseHealth (scanAll [ent "o" "owed(beta): one."]) } ]

end Obl

def selfTest : IO Unit := do
  let mut failed := 0
  for c in Obl.controls do
    let verdict := if c.holds then "fires" else "SILENT"
    IO.println s!"{verdict} {c.name} — {c.claim}"
    unless c.holds do failed := failed + 1
  IO.println s!"{Obl.controls.length - failed} of {Obl.controls.length} \
controls fire"
  unless failed == 0 do
    throw (IO.userError s!"{failed} control(s) did not fire — the gate \
cannot prove it would go red")

def usage : String :=
  s!"usage: {regen} [--check] [--json] | {regen} --self-test"

unsafe def main (args : List String) : IO Unit :=
  if args.contains "--self-test" then
    if args.length == 1 then selfTest else throw (IO.userError usage)
  else Gate.main regen fixtures args
