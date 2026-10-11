import Effect4.Laws.Program.NativeHeapExecution
import Effect4.Laws.Program.TracedMoves

/-!
Readers and controls for the reference lookup frame rule, R4 and R11.
The control separates event-labelled frame motion from actual store execution.
The native reader uses the real evaluator at an existing-cell write.
-/
set_option autoImplicit false
namespace Test.Machine.ReferenceFootprint
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Moves

def before : Stores := {Stores.empty with refs := [.nat 10, .nat 20]}
def written : Stores := {before with refs := [.nat 11, .nat 20]}

/-- The shared row law reads a different existing cell. -/
example : refPeek written.refs ⟨1⟩ = refPeek before.refs ⟨1⟩ :=
  syncOpStep_refPeek_other (op := .refSet ⟨0⟩ (.nat 11)) (before := before)
    (after := written) (answer := .cell ⟨0⟩) rfl ⟨1⟩ (by decide)

/-- The same law reads an absent cell, without an allocation assumption. -/
example : refPeek written.refs ⟨7⟩ = refPeek before.refs ⟨7⟩ :=
  syncOpStep_refPeek_other (op := .refSet ⟨0⟩ (.nat 11)) (before := before)
    (after := written) (answer := .cell ⟨0⟩) rfl ⟨7⟩ (by decide)

/- Allocation's actual answer names its new cell. Omitting it loses this change. -/
#guard (SyncOp.refMake .unit).refKernel.isNone
#guard (SyncOp.refMake .unit).refFootprint (.cell ⟨0⟩) = some ⟨0⟩
#guard refPeek [.unit] ⟨0⟩ ≠ refPeek [] ⟨0⟩

/-- Allocation retains a different existing cell through the same frame rule. -/
example : refPeek (before.refs ++ [.unit]) ⟨1⟩ = refPeek before.refs ⟨1⟩ :=
  syncOpStep_refPeek_other (op := .refMake .unit) (before := before)
    (after := {before with refs := before.refs ++ [.unit]})
    (answer := .cell ⟨2⟩) rfl ⟨1⟩ (by decide)

/-- A read retains its selected cell too. -/
example : before.refs = before.refs :=
  syncOpStep_refGet_refs (cell := ⟨0⟩) (before := before) (after := before)
    (answer := .nat 10) rfl

def program : NativeEff := .succeed (.lit .unit)
def machine : NativeMachine := {Api.load program 0 with state := before}
def fiber : NFiber := RunFiber.make ⟨0⟩ (.sync (.op (.refSet ⟨0⟩ (.nat 11)))) true (0, false) emptyCtx

/-- The actual primitive evaluator uses the shared source-operation footprint. -/
example : refPeek (evaluatePrim (interpAt program [] []) machine fiber false).machine.state.refs ⟨1⟩ =
    some (.nat 20) := by
  rw [StoreExecution.primitive_refPeek_other program [] [] machine fiber false ⟨1⟩]
  · rfl
  · intro op value source executed
    rcases source with same | impossible
    · change Prim.sync (EffThunk.op (.refSet ⟨0⟩ (.nat 11))) = .sync (.op op) at same
      cases same
      change some (⟨0⟩ : RefKey) ≠ some ⟨1⟩
      decide
    · cases impossible

/-- Event-labelled frame motion alone admits unrelated heaps. -/
theorem event_labels_ignore_heap (m : NativeMachine) (frame : NFrame) (heap : RefHeap) :
    TracedMoves m frame {m with state := {m.state with refs := heap}} frame :=
  (AdministrativeTrace.of_eq rfl).idle frame

/-- This raw relation control changes the selected reference while retaining the frame word. -/
example : TracedMoves machine fiber.frame {machine with state := written} fiber.frame :=
  event_labels_ignore_heap machine fiber.frame written.refs
#guard refPeek written.refs ⟨0⟩ ≠ refPeek before.refs ⟨0⟩

end Test.Machine.ReferenceFootprint
