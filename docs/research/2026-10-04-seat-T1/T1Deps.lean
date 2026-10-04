import ProofGraph.Axioms
import Effect4.Laws.Program.Agreement.Machine
import Effect4.Laws.Program.Agreement.Loop
import Effect4.Laws.Program.MeaningSound
import Effect4.Laws.Program.LoopSound
import Effect4.Laws.Program.Progress

/-! Seat T1 scratch: does `run_eq_meaning` or `loopAgreement` reach `sound`, `soundB` or
`progress`? The stop predicate names the three theorems, so each is a leaf the walk reports
when it reaches it and does not enter. Each walk gets a fresh memo.

Controls:
* positive, stop at the three: `meaning_typed` reaches `sound`, `meaningB_typed` reaches `soundB`;
* positive for `progress`, stop at `progress` alone (with the three as stops, `progress` is only
  reachable through `sound`, a stop leaf): `meaning_typed` reaches it;
* module level: the stop predicate selects every declaration of the three soundness modules, and
  the walk lists which of them each agreement root reaches. -/

open Lean Elab Command

def t1Targets : List Name :=
  [`Effect4.Program.Denote.sound, `Effect4.Program.Denote.soundB, `Effect4.Program.progress]

def t1Modules : List Name :=
  [`Effect4.Laws.Program.MeaningSound, `Effect4.Laws.Program.LoopSound,
   `Effect4.Laws.Program.Progress]

def t1Stop (n : Name) : Bool := t1Targets.contains n

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).bind fun i => env.header.moduleNames[i.toNat]?

def t1Walk (root : Name) (stop : Name → Bool) (label : String) (targets : List Name) :
    CommandElabM Unit := do
  let env ← getEnv
  unless env.contains root do
    logInfo m!"{root}: not in the environment"
    return
  let (reached, _) := (ProofGraph.reachedAxioms env root stop).run {}
  match reached with
  | none => logInfo m!"{root}: step budget ran out"
  | some leaves =>
    let hits := targets.map fun t => s!"{t}: {leaves.contains t}"
    let other := leaves.filter (fun n => !targets.contains n)
    logInfo m!"[{label}] {root}\n  {String.intercalate "\n  " hits}\n  other leaves: {other.toList}"

def t1ModuleWalk (root : Name) : CommandElabM Unit := do
  let env ← getEnv
  let stop : Name → Bool := fun n =>
    n != root && (moduleOf env n).any (fun m => t1Modules.contains m)
  let (reached, _) := (ProofGraph.reachedAxioms env root stop).run {}
  match reached with
  | none => logInfo m!"{root}: step budget ran out"
  | some leaves =>
    let inModules := leaves.filter stop
    logInfo m!"[modules] {root} reaches {inModules.size} declaration(s) of the three modules: {inModules.toList}"

-- positive controls, stop at the three
#eval t1Walk `Effect4.Program.Denote.meaning_typed t1Stop "three" t1Targets
#eval t1Walk `Effect4.Program.Denote.meaningB_typed t1Stop "three" t1Targets
-- positive control for `progress`, stop at `progress` alone
#eval t1Walk `Effect4.Program.Denote.meaning_typed (· == `Effect4.Program.progress) "progress"
  [`Effect4.Program.progress]
-- the test
#eval t1Walk `Effect4.Program.Agreement.run_eq_meaning t1Stop "three" t1Targets
#eval t1Walk `Effect4.Program.Agreement.loopAgreement t1Stop "three" t1Targets
-- module level
#eval t1ModuleWalk `Effect4.Program.Agreement.run_eq_meaning
#eval t1ModuleWalk `Effect4.Program.Agreement.loopAgreement
#eval t1ModuleWalk `Effect4.Program.Denote.meaning_typed

/-- Every declaration of a module, walked with the three modules' declarations as stops. -/
def t1WholeModule (mod : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some idx := env.getModuleIdx? mod | logInfo m!"{mod}: not loaded"; return
  let decls := env.constants.toList.filterMap fun (n, _) =>
    if env.getModuleIdxFor? n == some idx then some n else none
  let stop : Name → Bool := fun n => (moduleOf env n).any (fun m => t1Modules.contains m)
  let (results, _) := ProofGraph.reachedAxiomsMany env decls.toArray {} stop
  let mut users : Array (Name × List Name) := #[]
  for (n, r) in decls.zip results.toList do
    if let some leaves := r then
      let hits := leaves.filter stop
      unless hits.isEmpty do users := users.push (n, hits.toList)
  logInfo m!"[whole module] {mod}: {decls.length} declaration(s); {users.size} reach the three modules: {users.toList}"

#eval t1WholeModule `Effect4.Laws.Program.Agreement.Loop
#eval t1WholeModule `Effect4.Laws.Program.Agreement.Machine
