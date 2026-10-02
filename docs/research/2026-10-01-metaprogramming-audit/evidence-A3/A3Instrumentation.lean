/- UNCOMPILED instrumentation proposal, isolated use only.
   It delegates the original tactic unchanged and emits a success message that
   ordinary tactic backtracking can discard. No global counter or trace total.
   Counts are not reliable until Controls.lean validates this on Lean v4.33.1. -/
import Lean

open Lean Elab Tactic

syntax (name := a3Arm) "a3_arm " str " / " str " => " tactic : tactic

elab_rules : tactic
  | `(tactic| a3_arm $family:str / $arm:str => $body:tactic) => do
    let declaration := (← Term.getDeclName?).getD .anonymous
    let position ← getRefPosition
    let family := family.getString
    let arm := arm.getString
    evalTactic body
    logInfo m!"A3_RETAINED|{declaration}|{family}|{arm}|{position.line}:{position.column}"
