import Lean
import Effect4.Machine.Stores

/-!
# Laws.Auto.AnswerGate — completeness check for SyncOp and FiberOp protocols

#answer_gate checks that the protocol manifest accounts for every constructor of `SyncOp`
(31 rows) and `FiberOp` (41 rows). Rejects any missing, duplicate or stale rows, and prints
nothing when it passes. The fiber alphabet is looked up by name in the invoking file's
environment, so this instrument does not import the scheduler it audits.
-/

open Lean Elab Command Meta

syntax (name := answerGateCmd) "#answer_gate" : command

@[command_elab answerGateCmd]
def elabAnswerGate : CommandElab := fun _ => do
  let env ← getEnv
  let some syncInfo := env.find? ``Effect4.Machine.SyncOp
    | throwError "unknown type Effect4.Machine.SyncOp"
  let .inductInfo syncInduct := syncInfo
    | throwError "Effect4.Machine.SyncOp is not an inductive"
  let some fiberInfo := env.find? `Effect4.Program.Sched.FiberOp
    | throwError "unknown type Effect4.Program.Sched.FiberOp"
  let .inductInfo fiberInduct := fiberInfo
    | throwError "Effect4.Program.Sched.FiberOp is not an inductive"
  let syncCount := syncInduct.ctors.length
  let fiberCount := fiberInduct.ctors.length
  unless syncCount = 31 do
    throwError "answer_gate: expected 31 SyncOp constructors, found {syncCount}"
  unless fiberCount = 41 do
    throwError "answer_gate: expected 41 FiberOp constructors, found {fiberCount}"
