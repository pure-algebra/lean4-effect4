import Effect4.Laws.Program.AnswerSlots.AllocationAttachment
import Effect4.Laws.Machine.StatePreservation

/-!
Concept: store-typing R4 and reactive-scheduling R9.
Consumer: the shared pending allocation command producer for Atomic and Queue.
Pending frame flow retains the same exact heap through native administration.
The actual matching parked suffix supplies each admitted reply's answer class.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program

/-- The pending command flow keeps both the real saved frame and the exact allocation contents. -/
def PendingFrame (spec : Spec) (fragment : SourceScope.Fragment spec.root) (world : World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  FrameAt spec fragment world frame ∧ HeapPrefix spec world.state

/-- Metadata edits retain the actual pending current code and saved suffix. -/
theorem FrameAt.fields (spec : Spec) (fragment : SourceScope.Fragment spec.root) (world : World)
    (before after : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (held : FrameAt spec fragment world before) (current : after.current = before.current)
    (stack : after.stack = before.stack) : FrameAt spec fragment world after := by
  obtain ⟨input, output, code, saved⟩ := held
  exact ⟨input, output, current ▸ code, stack ▸ saved⟩

/-- A cleared pending fiber retains its actual current input with an empty saved suffix. -/
theorem FrameAt.cleared (spec : Spec) (fragment : SourceScope.Fragment spec.root) (world : World)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (held : FrameAt spec fragment world frame) : FrameAt spec fragment world {frame with stack := []} := by
  obtain ⟨input, output, code, saved⟩ := held
  exact ⟨input, input, code, .nil input⟩

/-- Actual pending interruption records metadata or installs a failure at its existing answer class. -/
theorem FrameAt.interruption (spec : Spec) (fragment : SourceScope.Fragment spec.root) (world : World)
    (fiber : SourceScope.SourceFiber) (cause : CauseV) (held : FrameAt spec fragment world fiber.frame) :
    FrameAt spec fragment world (interruptWithCause cause fiber).1.frame := by
  obtain ⟨input, output, code, saved⟩ := held
  have phase := code_phase spec world input fiber.frame.current code
  unfold interruptWithCause
  dsimp only
  repeat' split
  all_goals refine ⟨input, output, ?_, saved⟩
  all_goals aesop (add norm simp [frameCore]) (add safe apply [CodeAt.failure])

/-- Exact reference contents and deferred allocation counts retype an administrative pending frame. -/
theorem FrameAt.store_fields (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (owner : FiberId) (before after : Stores) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (held : PendingFrame spec fragment ⟨owner, before, false⟩ frame)
    (refs : after.refs = before.refs)
    (deferred : after.deferreds.cells.length = before.deferreds.cells.length) :
    PendingFrame spec fragment ⟨owner, after, false⟩ frame := by
  obtain ⟨⟨input, output, code, saved⟩, heap⟩ := held
  have counts : before.refs.length = after.refs.length := congrArg List.length refs.symm
  have future : Future ⟨owner, before, false⟩ ⟨owner, after, false⟩ :=
    ⟨rfl, Nat.le_of_eq counts, Nat.le_of_eq deferred.symm, fun pending => pending⟩
  have contents : after.refs = Initialization.values spec.initialization after.refs.length := by
    rw [refs]
    exact heap.1
  refine ⟨⟨input, output,
    code_rebase spec _ input frame.current code _ future counts deferred.symm rfl contents,
    path_future spec fragment _ _ future input output frame.stack saved⟩, ?_⟩
  exact ⟨contents, by rw [refs, deferred]; exact heap.2⟩

/-- Deferred waking preserves the number of allocated deferred cells. -/
theorem deferred_wake_length (store : DeferredStore) (cell : DeferredKey) :
    (store.wakeBatch cell).cells.length = store.cells.length := by
  unfold DeferredStore.wakeBatch
  split
  · rfl
  · split <;> exact DeferredStore.setCell_cells_length _ _ _

/-- Administrative store hooks preserve exact pending references and deferred allocation counts. -/
theorem pending_store_hooks (root : NativeEff) (table : RowTable) (refs : List Val) (deferred : Nat) :
    StatePreservation.CommandHooks (interpOf root table)
      (fun state => state.refs = refs ∧ state.deferreds.cells.length = deferred) where
  link := by
    intro mode scope owner state next key held ran
    dsimp only [interpOf] at ran
    split at ran
    · cases ran
    · cases ran; exact held
  drop := by
    intro scope key state next held ran
    change (match state.scopes.entryAt scope with
      | none => none
      | some _ => some {state with scopes := state.scopes.removeFinalizer scope key}) = some next at ran
    split at ran
    · cases ran
    · cases ran; exact held
  due := fun _ held => held
  wake := by
    intro key phase state held
    change (state.wakeList key phase).refs = refs ∧ (state.wakeList key phase).deferreds.cells.length = deferred
    unfold Stores.wakeList
    split
    · exact ⟨held.1, (deferred_wake_length _ _).trans held.2⟩
    · exact held
end Effect4.Program.AnswerSlots.AllocationAdapter
