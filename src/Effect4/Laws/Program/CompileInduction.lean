import Effect4.Program.Compile
import Lean.Elab.Tactic.Induction

/-!
# Shared compiler induction equations

Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumers: source ownership and release custody proofs by compiler induction.
Realize Lean's compiler and frame case principles once before independent consumers import them.
Lean otherwise generates colliding matcher auxiliaries when their proof modules meet.
This module adds no assumption, program representation or application claim.
-/

run_meta do
  let some _ ← Lean.Meta.getFunInduct? true false ``Effect4.Program.compileEff
    | throwError "The compiler's functional induction principle is unavailable"

run_meta do
  for declName in [``Effect4.Machine.progOf] do
    let some _ ← Lean.Meta.getFunInduct? true false declName
      | throwError "Missing functional induction principle: {declName}"
  for declName in [``Effect4.Machine.finProgram, ``Effect4.Machine.contAOf,
      ``Effect4.Machine.contEOf, ``Effect4.Machine.cancelProgram,
      ``Effect4.Program.contAOf, ``Effect4.Program.contEOf,
      ``Effect4.Program.suspendBodyAt, ``Effect4.Program.loopFinishAt,
      ``Effect4.Program.loopNextAt, ``Effect4.Program.cancelProgramOf,
      ``Effect4.Prim.armA, ``Effect4.Prim.armE,
      ``Effect4.FrameFiber.resumeValue, ``Effect4.FrameFiber.resumeCause] do
    let some _ ← Lean.Meta.getFunInduct? true true declName
      | throwError "Missing functional case principle: {declName}"
