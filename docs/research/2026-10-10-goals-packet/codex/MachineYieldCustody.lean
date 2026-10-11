import Effect4.Laws.Program.ReleaseCustody.Evaluation
import ProofGraph.AxiomAudit

/-! Reader for the forced-yield clause of Execution.command_custody.
The old independent stack sum duplicates scope-add credit beneath the saved constant.
The new projection follows the actual saved continuation and retains one credit.
These equations inspect the assertion; they establish no whole-command preservation. -/
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.Control

example (q : List Nat) (scope : Nat) (a : Val) (fin : FinName)
    (one : credit q fin = 1) :
    currentCredits q (.yieldNowWith 0) +
      ([.onSuccessConst (.yieldNowWith 0) (.sync (.op (.scopeAdd scope fin))),
        .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)].map
        (futureCredits q)).sum = 2 := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, futureCredits,
    currentCredits, opCredits, one]
  omega

example (q : List Nat) (scope : Nat) (a : Val) (fin : FinName)
    (one : credit q fin = 1) :
    currentCredits q (.yieldNowWith 0) +
      stackCredits q (.yieldNowWith 0)
        [.onSuccessConst (.yieldNowWith 0) (.sync (.op (.scopeAdd scope fin))),
         .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin)] = 1 := by
  simp only [currentCredits, stackCredits, opCredits, responseCredits, stackCap,
    ite_true, one]

/-- The actual charged fiber frame consumes the corrected equation. -/
example (q : List Nat) (f : Fiber) (scope : Nat) (a : Val) (fin : FinName)
    (lower : List NCode)
    (current : f.frame.current = .sync (.op (.scopeAdd scope fin)))
    (stack : f.frame.stack = .onSuccess (.sync (.op (.scopeAdd scope fin)))
      (.afterScopeAdd a fin) :: lower) :
    fiberCredits q { countOp f with
      frame := { f.frame with
        current := .yieldNowWith 0
        stack := .onSuccessConst (.yieldNowWith 0) (.sync (.op (.scopeAdd scope fin))) :: f.frame.stack }
      yieldOverride := none } = fiberCredits q f :=
  scope_add_yield_frame_credits q f scope a fin lower current stack

/-- The direct interruption edit consumes the checked callback-sensitive stack bound. -/
example (q : List Nat) (f : Fiber) (cause : CauseV) :
    fiberCredits q { f with frame := { f.frame with current := .failure cause } } ≤ fiberCredits q f :=
  Evaluation.failure_fiber_le q f cause

/-- Actual yield injection consumes the arbitrary selected machine row and pending command suffix. -/
example (root : NativeEff) (table : RowTable) (m : NativeMachine) (id : FiberId)
    (f : Fiber) (pending : List Command) (q : List Nat)
    (unique : (m.fibers.map RunFiber.id).Nodup)
    (funded : Funded q m (.loop id false :: pending)) (found : m.fiber? id = some f)
    (interrupt : f.frame.deferredInterrupt = false)
    (verdict : yieldVerdict (countOp f) = true) (prevent : f.preventYield = false) :
    Funded q (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop id false) pending).1
      (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.loop id false) pending).2 :=
  Evaluation.forced_yield_loop_funded root table m id f pending q unique funded found interrupt verdict prevent

#axiom_audit Effect4.Laws.Program.ReleaseCustody.Names Effect4.Laws.Program.ReleaseCustody.Control
  Effect4.Laws.Program.ReleaseCustody.Evaluation
