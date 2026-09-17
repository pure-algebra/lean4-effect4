import Effect4.Laws.Auto.Inversion

/-!
# Laws.Auto.Census — which theorems of a module does a tactic prove from their statements?

`#auto_census Some.Module using tac` takes every theorem the named (imported) module declares,
makes a goal of its statement, and runs `tac` on it under a heartbeat cap. It reports the
theorems `tac` closes, each with the number of source lines its present declaration takes and
the axioms the found proof reaches, longest first; then the totals.

It is a measuring instrument, for finding where `aesop` with the rules registered so far
already does the work of a long proof, and for checking a candidate rule set against a whole
module at once. It changes nothing: every attempt is rolled back.

    #auto_census Effect4.Laws.Codegen.Template using aesop
    #auto_census Effect4.Laws.Codegen.Template heartbeats 40000 using (intros; aesop)
-/

open Lean Elab Meta Command

namespace Effect4.Laws.Auto

/-- The axioms a term reaches: those of every constant it mentions. -/
def axiomsOf (e : Expr) : CoreM (Array Name) := do
  let mut out : Array Name := #[]
  for c in e.getUsedConstants do
    for a in (← collectAxioms c) do
      unless out.contains a do out := out.push a
  return out.qsort (·.toString < ·.toString)

/-- One attempt, rolled back: the axioms of the proof `tac` finds for `type`, if it finds one
within `cap` heartbeats. -/
def attempt (type : Expr) (tac : Syntax) (cap : Nat) : TermElabM (Option (Array Name)) :=
  withoutModifyingState do
    -- a search that runs out of heartbeats is a runtime exception: it is an answer ("no"),
    -- not a failure of the census
    tryCatchRuntimeEx
      (withOptions (fun o => maxHeartbeats.set o cap) <| withCurrHeartbeats do
        let goal ← mkFreshExprMVar type
        let rest ← Tactic.run goal.mvarId! (Tactic.evalTactic tac)
        unless rest.isEmpty do return none
        let proof ← instantiateMVars goal
        if proof.hasExprMVar || proof.hasSorry then return none
        return some (← axiomsOf proof))
      (fun _ => return none)

syntax (name := autoCensus)
  "#auto_census " ident (" heartbeats " num)? " using " tacticSeq : command

@[command_elab autoCensus] def elabAutoCensus : CommandElab := fun stx => do
  let modName := stx[1].getId
  let cap := if stx[2].isNone then 20000 else stx[2][1].toNat
  let tac := stx[4]
  let env ← getEnv
  let some modIdx := env.getModuleIdx? modName
    | throwError "#auto_census: {modName} is not an imported module"
  let theorems := env.constants.map₁.fold (init := #[]) fun acc name info =>
    match info with
    | .thmInfo thm =>
      if env.getModuleIdxFor? name == some modIdx && !name.isInternalDetail then
        acc.push (name, thm.type)
      else acc
    | _ => acc
  -- only what a person wrote: a theorem with a source range of its own (equation and
  -- congruence lemmas the elaborator generates have none)
  let mut written : Array (Nat × Name × Expr) := #[]
  for (name, type) in theorems do
    if let some r ← findDeclarationRanges? name then
      written := written.push (r.range.endPos.line - r.range.pos.line + 1, name, type)
  let mut found : Array (Nat × Name × Array Name) := #[]
  for (lines, name, type) in written do
    if let some axioms ← liftTermElabM (attempt type tac cap) then
      found := found.push (lines, name, axioms)
  let sorted := found.qsort fun a b => a.1 > b.1
  let mut report := m!"{modName}: {found.size} of {written.size} theorems closed from their \
    statements; {sorted.foldl (fun n r => n + r.1) 0} source lines they now take"
  for (lines, name, axioms) in sorted do
    report := report ++ m!"\n  {lines}\t{name}\t{axioms}"
  logInfo report

end Effect4.Laws.Auto
