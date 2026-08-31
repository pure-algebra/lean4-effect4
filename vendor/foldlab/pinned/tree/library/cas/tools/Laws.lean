import Gate
import Law

/-!
# The law index — `lake exe laws`

The gate over `Law`: emit or byte-check `meta/out/laws.META.json`, then
report drift between the ruling registry and the tree. The registry
itself, the `LAW <id>: <clause>` convention, the join and the document
are `Law`, which `lake exe debts` reads too; this root is the fixture,
the planted-defect controls and the verdict.

Two failures, kept separate. Stale bytes mean the fixture was not
regenerated; a violation means the registry and the tree disagree. Both
are red, and only the second is a lie about the state of the evidence.
-/

open Lean

/-! ## The tool -/

def outPath : System.FilePath := "meta" / "out" / "laws.META.json"

def regen : String := "lake exe laws"

/-- The index's emitted header. The document declared no version before
this one, so its `schemaVersion` opens at 1. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "laws"
  module := "library/cas/tools/Laws.lean"

/-- The walk, once: every `LAW` claim in the library, in the total
order every projection sorts by. -/
unsafe def claims : IO (List Law.Claim) := do
  enableInitializersExecution
  Walk.run fun env => do
    return Law.claimsOf (← Walk.collect env)

/-! ## The controls

A gate that cannot fail proves nothing. One planted defect per rule,
each refuted on its own rule, over a SYNTHETIC registry and claim set
so the controls attack the rules without touching the tree. The
synthetic ids are real namespace ids on purpose: a self-test on
invented ids would parse to nothing and every control would "pass" by
checking nothing. -/

namespace Law

private def synthReg : List Ruling := [
  { id := "SM-1", statement := "the first ruling", status := .bound },
  { id := "SM-2", statement := "the second ruling", status := .owed },
  { id := "SM-3", statement := "the retired ruling", status := .superseded }]

private def claim (id decl : String) : Claim :=
  { id, clause := "as stated", module := "Cas.Probe", declaration := decl }

private def synthClaims : List Claim := [claim "SM-1" "Cas.Probe.first"]

private def baseDoc : String := document _root_.emitted synthReg synthClaims

structure Control where
  name : String
  /-- What the control asserts. -/
  claim : String
  holds : Bool

private def mentions (hay needle : String) : Bool :=
  (hay.splitOn needle).length > 1

/-- The control's own test: SOME violation names this rule. Each
control names a phrase only its own rule writes, so a control cannot
pass on another rule's refusal. -/
private def fires (reg : List Ruling) (cs : List Claim) (needle : String) : Bool :=
  (violations reg cs).any (fun v => mentions v needle)

def controls : List Control :=
  [ { name := "baseline"
    , claim := "an honest registry passes, and its one owed row is \
counted as unbound rather than failed"
    , holds := violations synthReg synthClaims == [] &&
        unboundOf synthReg synthClaims == ["SM-2"] },
    { name := "unregistered binding"
    , claim := "a declaration claiming an id the registry does not \
carry fails, and lands in the fixture's unregistered array"
    , holds :=
        let cs := synthClaims ++ [claim "SM-99" "Cas.Probe.typo"]
        fires synthReg cs "absent from the registry" &&
          (unregisteredOf synthReg cs).map (·.id) == ["SM-99"] },
    { name := "status lie — owed but claimed"
    , holds :=
        fires synthReg (synthClaims ++ [claim "SM-2" "Cas.Probe.second"])
          "recorded owed"
    , claim := "a row recorded owed that a declaration now claims fails" },
    { name := "status lie — bound but unclaimed"
    , claim := "a docstring that loses its LAW line while the registry \
still says bound fails — the comment-deletion attack"
    , holds := fires synthReg [] "recorded bound" },
    { name := "status lie — superseded but claimed"
    , claim := "a retired row a declaration still claims fails"
    , holds :=
        fires synthReg (synthClaims ++ [claim "SM-3" "Cas.Probe.third"])
          "recorded superseded" },
    { name := "duplicate registry row"
    , claim := "one id on two rows fails"
    , holds := fires (synthReg ++ [synthReg[1]!]) synthClaims
        "duplicate row" },
    { name := "malformed registry id"
    , claim := "a row outside the SM- namespace fails"
    , holds := fires
        (synthReg ++ [{ id := "R7", statement := "a foreign id"
                      , status := .owed }]) synthClaims
        "not an id of the SM- namespace" },
    { name := "empty statement"
    , claim := "a row that states nothing fails"
    , holds := fires
        (synthReg ++ [{ id := "SM-4", statement := "", status := .owed }])
        synthClaims "states nothing" },
    { name := "the claim must be at the head"
    , claim := "a LAW line below prose is discussion, not a binding"
    , holds :=
        headClaims "The float ceiling bites here.\nLAW SM-15: no float." == [] &&
          headClaims "LAW SM-15: no float.\nThe float ceiling bites here."
            == [("SM-15", "no float.")] },
    { name := "the line grammar is exact"
    , claim := "a near-miss is not a claim, and a clause keeps its own \
colons"
    , holds :=
        parseLawLine "LAWS SM-15: no float" == none &&
          parseLawLine "LAW SM-15 no float" == none &&
          parseLawLine "law SM-15: no float" == none &&
          parseLawLine "LAW SM-15: " == none &&
          parseLawLine "LAW SM-19: the doors: held in agreement" ==
            some ("SM-19", "the doors: held in agreement") },
    { name := "one docstring, several rulings"
    , claim := "a run of LAW lines at the head is several claims, and \
the run ends at the first line that is not one"
    , holds :=
        headClaims "LAW SM-6: one\nLAW SM-7: two\nprose\nLAW SM-8: three"
          == [("SM-6", "one"), ("SM-7", "two")] },
    { name := "the debt moves the document"
    , claim := "adding an unbound row moves the bytes even though \
nothing failed"
    , holds :=
        let grown := synthReg ++
          [{ id := "SM-4", statement := "a new ruling", status := .owed }]
        violations grown synthClaims == [] &&
          document _root_.emitted grown synthClaims != baseDoc },
    { name := "the clause is carried verbatim"
    , claim := "rewording a declaration's own clause moves the bytes"
    , holds :=
        document _root_.emitted synthReg [{ (claim "SM-1" "Cas.Probe.first") with
          clause := "as restated" }] != baseDoc } ]

end Law

def selfTest : IO Unit := do
  let mut failed := 0
  for c in Law.controls do
    let verdict := if c.holds then "fires" else "SILENT"
    IO.println s!"{verdict} {c.name} — {c.claim}"
    unless c.holds do failed := failed + 1
  IO.println s!"{Law.controls.length - failed} of {Law.controls.length} \
controls fire"
  unless failed == 0 do
    throw (IO.userError s!"{failed} control(s) did not fire — the gate \
cannot prove it would go red")

def usage : String :=
  s!"usage: {regen} [--check] [--json] | {regen} --self-test"

/-- Emit or check the fixture, THEN report drift. The byte gate and the
index gate are separate failures: stale bytes mean the fixture was not
regenerated, and a violation means the registry and the tree disagree.
Both are red; only the second is a lie about the state of the
evidence. -/
unsafe def gate (args : List String) : IO Unit := do
  let pending ← IO.mkRef ([] : List String)
  let fixtures' : IO (List Gate.Fixture) := do
    let cs ← claims
    pending.set (Law.violations Law.registry cs)
    let bound := Law.statusCount Law.registry .bound
    return [⟨outPath, Law.document emitted Law.registry cs,
             s!"{bound} of {Law.registry.length} rulings bound, \
{(Law.unboundOf Law.registry cs).length} unbound"⟩]
  Gate.main regen fixtures' args
  let vs ← pending.get
  unless vs.isEmpty do
    IO.eprintln s!"\nLAW INDEX: DRIFT — {vs.length} violation(s).\n"
    for v in vs do IO.eprintln s!"  - {v}"
    IO.eprintln "\nThe registry and the tree disagree. Fix the tree, or \
amend Law.registry in the same commit that moved the ruling. Do not \
delete the row to make this pass."
    throw (IO.userError
      s!"{vs.length} law-index violation(s) — run `{regen}` after fixing")

unsafe def main (args : List String) : IO Unit :=
  if args.contains "--self-test" then
    if args.length == 1 then selfTest else throw (IO.userError usage)
  else gate args
