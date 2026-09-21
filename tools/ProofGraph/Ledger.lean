import ProofGraph.Proof
import Batteries.Util.ProofWanted

/-!
A checked join between a derived obligation set and authored evidence. Declarations, not
rendered rows, carry propositions. The caller derives goals; this module checks exact set
coverage, dependencies, theorem types, placeholder types, and the open-obligation ceiling.
-/
namespace ProofGraph
open Lean Meta

/-- A declared proof obligation. Its inhabitant records a statement; it does not prove it. -/
structure Obligation (statement : Prop) : Prop where

def Obligation.statement {p : Prop} (_ : Obligation p) : Prop := p

structure Goal where
  id : Name
  levels : List Name := []
  proposition : Expr
  dependencies : Array Name := #[]

inductive Evidence where
  | proved (theoremName : Name)
  | wanted (placeholder : Name)

structure Entry where
  goal : Name
  evidence : Evidence

structure Report where
  proved : Nat := 0
  wanted : Nat := 0
  edges : Array (Name × Name) := #[]

/-- A placeholder records a closed proposition and has no inhabitant of that proposition. -/
def addWanted (name : Name) (levels : List Name) (proposition : Expr) : MetaM Unit := do
  if proposition.hasFVar || proposition.hasMVar then throwError "proof graph: open goal {name}"
  unless ← isProp proposition do throwError "proof graph: not a proposition: {name}"
  addDecl <| .defnDecl {
    name, levelParams := levels
    type := mkApp (mkConst ``ProofWanted [.zero]) proposition
    value := mkApp (mkConst ``ProofWanted.mk [.zero]) proposition
    hints := .abbrev, safety := .safe }

private def validateWanted (g : Goal) (name : Name) : MetaM Unit := do
  let .defnInfo info ← getConstInfo name
    | throwError "proof graph: {name} is not a placeholder definition"
  unless info.levelParams == g.levels do
    throwError "proof graph: placeholder universes changed for {g.id}"
  let expected := mkApp (mkConst ``ProofWanted [.zero]) g.proposition
  unless ← isDefEq info.type expected do
    throwError "proof graph: placeholder proposition changed for {g.id}"
  let extra := (← collectAxioms name).filter fun a => ![``propext, ``Quot.sound].contains a
  unless extra.isEmpty do throwError "proof graph: placeholder {name} reaches {extra}"

/-- Validate before counting. Equal counts cannot hide a replaced, missing, or stale goal. -/
def check (goals : Array Goal) (entries : Array Entry) (ceiling : Nat) : MetaM Report := do
  let ids := goals.map (·.id)
  unless ids.toList.eraseDups.length == ids.size do throwError "proof graph: duplicate goal id"
  let entryIds := entries.map (·.goal)
  unless entryIds.toList.eraseDups.length == entryIds.size do throwError "proof graph: duplicate evidence"
  for entry in entries do
    unless ids.contains entry.goal do throwError "proof graph: stale entry {entry.goal}"
  let mut report : Report := {}
  for g in goals do
    if g.proposition.hasFVar || g.proposition.hasMVar then throwError "proof graph: open goal {g.id}"
    unless ← isProp g.proposition do throwError "proof graph: not a proposition: {g.id}"
    for dep in g.dependencies do
      unless ids.contains dep do throwError "proof graph: unknown dependency {dep} of {g.id}"
      report := { report with edges := report.edges.push (g.id, dep) }
    let some entry := entries.find? (·.goal == g.id)
      | throwError "proof graph: missing evidence or placeholder for {g.id}"
    match entry.evidence with
    | .proved name =>
      let reference : ProofRef := ⟨name, g.levels, g.proposition⟩
      if let .error why ← reference.validate then throwError "proof graph: {why}"
      report := { report with proved := report.proved + 1 }
    | .wanted name =>
      validateWanted g name
      report := { report with wanted := report.wanted + 1 }
  -- Kahn's algorithm: every dependency must leave the remaining set before its consumer.
  let mut remaining := ids
  for _ in [:goals.size] do
    remaining := remaining.filter fun id =>
      report.edges.any (fun (src, dst) => src == id && remaining.contains dst)
  unless remaining.isEmpty do throwError "proof graph: dependency cycle through {remaining}"
  if report.wanted > ceiling then
    throwError "proof graph: {report.wanted} open obligations exceed ceiling {ceiling}"
  return report

end ProofGraph
