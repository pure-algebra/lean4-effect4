import Effect4.Laws.Program.Agreement.Segment
import Effect4.Laws.Program.LoopAgreement
import Tools.Semantics

set_option autoImplicit false

namespace HostCleanupReview
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

private def u : NativeEff := .succeed (.lit .unit)
private def t : Term := .lit .unit

-- The machine profile includes loops, conditional handlers, and every external row index.
#guard LoopedRows (.catchIf t (.iterate none t t t t u) (.perform (.external 7) t))
#guard !StraightRows [] (.perform (.external 7) t)
#guard !LoopedRows (.catchIf t (.yieldNow 0) u)
#guard !LoopedRows (.catchIf t u (.yieldNow 0))
#guard !LoopedRows (.iterate none t t t t (.yieldNow 0))
#guard !LoopedRows (.defs [] .nil u)
#guard !LoopedRows (.perform .deferredAwait t)
#guard !LoopedRows (.perform (.call 0) t)
#guard LoopedRows (.perform .refMake t)

open Lean Elab Command Effect4.Laws.Auto in
run_cmd liftTermElabM do
  let env ← getEnv
  let moved := ``Effect4.Program.Agreement.run_eq_meaning
  let segment := `Effect4.Laws.Program.Agreement.Segment
  let oldHome := `Effect4.Laws.Program.Agreement.Machine
  let mod := semanticsModule env moved
  unless mod == segment do throwError "the moved theorem has an unexpected module"
  let defaults := Tools.Semantics.registry.concepts.flatMap (·.defaultModules)
  unless defaults.contains oldHome do throwError "positive old-home control failed"
  if defaults.contains mod then throwError "the placement omission no longer reproduces"
  let segmentNames := (semanticsTheorems env).filter fun n => semanticsModule env n == segment
  unless segmentNames.contains moved do throwError "the theorem is not available to the report reader"
  let selected := segmentNames.filter fun n => defaults.contains (semanticsModule env n)
  unless selected.isEmpty do throwError "the exact module filter did not omit Segment"
  let repairedDefaults := segment :: defaults
  let selectedAfter := segmentNames.filter fun n => repairedDefaults.contains (semanticsModule env n)
  unless selectedAfter == segmentNames do throwError "the local placement control did not restore the declarations"
  logInfo m!"placement: module={mod}; available={segmentNames.size}; selected={selected.size}; selected with local module entry={selectedAfter.size}"
  unless env.contains `Effect4.Program.Denote.LoopedRows do throwError "the generated predicate is missing"
  if env.contains `Effect4.Program.Agreement.LoopedRows then throwError "the old predicate name remains available"
  logInfo "predicate name: Denote.LoopedRows present; Agreement.LoopedRows absent"
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if semanticsModule env name == segment then
      match ProofGraph.exactAxioms env name with
      | none => throwError "missing constant during selected-module axiom reading: {name}"
      | some axioms =>
        unless axioms.all (fun a => [`propext, `Quot.sound].contains a) do
          throwError "selected-module axiom ceiling failed for {name}: {axioms}"
        checked := checked + 1
  logInfo m!"exactAxioms: {checked} Segment declarations fit [propext, Quot.sound]"

end HostCleanupReview
