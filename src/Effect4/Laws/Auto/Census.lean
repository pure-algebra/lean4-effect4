import Effect4.Laws.Auto.Inversion
import ProofGraph.Search

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
abbrev axiomsOf := ProofGraph.axiomsOf

/-- The source line a constant of the current module is declared at: its own, or that of the
declaration it was generated from (`foo.eq_1`, `foo.match_1`, … carry no range of their own). -/
def declaredAt : Name → CoreM (Option Nat)
  | name@(.str p _) => do
    if let some r ← findDeclarationRanges? name then return some r.range.pos.line
    declaredAt p
  | name => do
    if let some r ← findDeclarationRanges? name then return some r.range.pos.line
    return none

/-- Does `proof`, found for a theorem declared at line `first` of module `modIdx`, use that
theorem itself or anything of the module declared after it? In place, the proof would have
neither. -/
def usesWhatFollows (proof : Expr) (modIdx : ModuleIdx) (first : Nat) : CoreM Bool := do
  let env ← getEnv
  for c in proof.getUsedConstants do
    if env.getModuleIdxFor? c == some modIdx then
      if let some line ← declaredAt c then
        if line ≥ first then return true
  return false

/-- One attempt, rolled back: the axioms of the proof `tac` finds for `type`, if it finds one
within `cap` heartbeats that the theorem could carry in place. -/
def attemptProof (type : Expr) (tac : Syntax) (cap : Nat) (modIdx : ModuleIdx) (first : Nat) :
    TermElabM (Option Expr) := do
  let .ok proof ← ProofGraph.search type tac cap | return none
  if ← usesWhatFollows proof modIdx first then return none
  return some proof

/-- The measuring API retains its previous result; generators may use `attemptProof` and
publish the returned term through `ProofGraph.addTheorem`. -/
def attempt (type : Expr) (tac : Syntax) (cap : Nat) (modIdx : ModuleIdx) (first : Nat) :
    TermElabM (Option (Array Name)) := do
  let some proof ← attemptProof type tac cap modIdx first | return none
  return some (← axiomsOf proof)

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
  let mut written : Array (Nat × Nat × Name × Expr) := #[]
  for (name, type) in theorems do
    if let some r ← findDeclarationRanges? name then
      written := written.push (r.range.pos.line, r.range.endPos.line, name, type)
  let mut found : Array (Nat × Nat × Name × Array Name) := #[]
  for (first, last, name, type) in written do
    if let some axioms ← liftTermElabM (attempt type tac cap modIdx first) then
      found := found.push (first, last, name, axioms)
  let sorted := found.qsort fun a b => a.2.1 - a.1 > b.2.1 - b.1
  let mut report := m!"{modName}: {found.size} of {written.size} theorems closed from their \
    statements; {sorted.foldl (fun n r => n + (r.2.1 - r.1 + 1)) 0} source lines they now take"
  -- one row per theorem: lines, first-last line of the declaration, name, axioms of the found proof
  for (first, last, name, axioms) in sorted do
    report := report ++ m!"\n  {last - first + 1}\t{first}-{last}\t{name}\t{axioms}"
  logInfo report

end Effect4.Laws.Auto
