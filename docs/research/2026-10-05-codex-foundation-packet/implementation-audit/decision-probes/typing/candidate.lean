-- UNCOMPILED DESIGN SKETCH. No Lean command was run for this file.
-- Placement: store-typing, R4; serves fold-typed-atomic-update and the
-- existing five Queue typing goals. Consumer: the exact wrapper update's
-- step_keeps_cell application. Domain: this signature, environment, cell
-- type, reply type, and first-order term. Excludes acceptance for every
-- MessageTy, source hygiene, whole-program admission, and host behavior.
-- This sketches a local proof adapter, not a requested new public API.
import Effect4.Laws.Modules.Queue.Steps
import Effect4.Laws.Modules.Queue.Typing
import ProofGraph.Plan

namespace QueueTypingCandidate
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Queue.Model

-- The existing consumer already accepts precisely this equality.
abbrev ExactUpdate (sig : Signature NativeOp) (capturedTypes : TyEnv)
    (cellType replyType : Ty) (body : Term) : Prop :=
  termTy sig (capturedTypes ++ [cellType]) body = some (.prod replyType cellType)

-- A successful dependent branch retains an actual equality proof.
-- A caller must retain the elaboration equation for the SAME body separately.
-- This mirrors checkTypedProgram; it does not add a typing algorithm.
def updateEvidence (sig : Signature NativeOp) (capturedTypes : TyEnv)
    (cellType replyType : Ty) (body : Term) :
    Option (PLift (ExactUpdate sig capturedTypes cellType replyType body)) :=
  if h : ExactUpdate sig capturedTypes cellType replyType body then some ⟨h⟩ else none

-- Proposed concrete certificate, independent of takeStep_typed.
-- This is a kernel-checkable tactic route, not a report that it compiled.
-- Its consumer is a native, canonical-scope instance; arbitrary scopes need
-- an exact elaboration/weakening connection or a check of the actual body.
@[semantics "store-typing" (requirement := R4)]
theorem nativeNatTake :
    typeAt nativeSignature ["id", "hint", "s"]
      [Queue.idTy, Queue.idTy, Queue.cellTy .nat]
      (Queue.takeStep .nat (var "id") (var "hint") (var "s")) =
      some (.prod (takeReplyTy .nat) (Queue.cellTy .nat)) := by
  decide

-- Proposed refusing control: the request identity is typed as a number.
-- The existing QueueSteps battery already checks this refusal finitely.
@[semantics "store-typing" (requirement := R4)]
theorem numberIsNotRequestIdentity :
    typeAt nativeSignature ["id", "hint", "s"]
      [.nat, Queue.idTy, Queue.cellTy .nat]
      (Queue.takeStep .nat (var "id") (var "hint") (var "s")) = none := by
  decide

-- Required after implementation: actual result, ceiling, and no dependency
-- on any of the five planned goals. These commands are NOT run here.
#print axioms nativeNatTake
#plan_status nativeNatTake
#print axioms numberIsNotRequestIdentity
end QueueTypingCandidate
