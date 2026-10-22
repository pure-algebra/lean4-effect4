import Effect4.Laws.Program.StackRegion
import Effect4.Laws.Program.ReleaseCustody.CommandStacks

/-!
Concept: scope-lifetime-finalization, R11.
Question: evaluator installation protects queued stacks for Execution.history.
Reach: every actual native evaluator and iteration, inspecting existing fiber rows.
Limit: stack transport alone establishes neither funding nor complete command closure.
Unlock: GuardQueue transports pending administrative overwrite obligations.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Effect4.Program.ReleaseCustody.NativeStacks
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.CommandStacks
abbrev Interp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev Action := WithFiberAction EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev Fiber := Moves.NFiber

/-- The shared forward classification gives exact stored-stack transport.
Consumer: every native evaluator interface below. -/
theorem lookup_links {before after : NativeMachine} (held : Moves.LookupEdits before after) :
    StackLinks before after := by
  intro id fiber found
  obtain ⟨next, seen, edits⟩ := held id fiber found
  exact ⟨next, seen, Moves.OtherEdits.stack edits⟩

/-- Metadata edits retain every old stored stack; consumer: native observer cancellation. -/
theorem map_links (m : NativeMachine) (edit : Fiber → Fiber)
    (key : ∀ f, (edit f).id = f.id) (stack : ∀ f, (edit f).frame.stack = f.frame.stack) :
    StackLinks m {m with fibers := m.fibers.map edit} := by
  intro id fiber found
  refine ⟨edit fiber, ?_, stack fiber⟩
  unfold RunMachine.fiber? at found ⊢
  rw [List.find?_map]
  have predicate : ((fun f : Fiber => decide (f.id = id)) ∘ edit) =
      (fun f : Fiber => decide (f.id = id)) := by
    funext f
    simp only [Function.comp_def, key]
  rw [predicate, found]
  rfl


/-- A spawned child appends its row; consumer: actual fork actions. -/
theorem spawn_links (interp : Interp) (m : NativeMachine) (f : Fiber) (program : NCode)
    (options : Supervision.ForkOptions) (site : List Nat) :
    StackLinks m (spawn interp m f program options site).1 :=
  lookup_links (Moves.InterferesWithLookup.spawn interp m f program options site).lookup

/-- Scheduling a spawned child retains the table; consumer: fork action transport. -/
theorem start_links (m : NativeMachine) (f : Fiber) (child : FiberId) (immediately : Bool) :
    StackLinks m (start m f child immediately).1 :=
  lookup_links (Moves.InterferesWithLookup.start m f child immediately).lookup

/-- Countdown registration edits observers only; consumer: native await and park cases. -/
theorem countdown_links (interp : Interp) (m : NativeMachine) (f : Fiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool) :
    StackLinks m (countdownPark interp m f targets resume failFast).1 :=
  lookup_links (Moves.InterferesWithLookup.countdownPark interp m f targets resume failFast).lookup

/-- Parallel cleanup appends children without replacing old rows; consumer: closePar. -/
theorem finalizers_links (interp : Interp) (m : NativeMachine) (f : Fiber) (programs : List NCode) :
    StackLinks m (forkFinalizers interp m f programs).1 :=
  lookup_links (Moves.InterferesWithLookup.forkFinalizers interp f m programs).lookup

/-- Recording an interrupt retains the stored target stack; consumer: interruptAs. -/
theorem interrupt_links (root : NativeEff) (table : RowTable) (m : NativeMachine) (f : Fiber)
    (y : Bool) (target who : FiberId) :
    StackLinks m (evaluatePrim.interruptAs (interpAt root m.completedExits table) m f y target who).machine :=
  lookup_links (Moves.withFiber_interference (interpAt root m.completedExits table) m f y (.interruptAs target who)).lookup

/-- Every actual fiber action protects existing queued stacks. Consumer: primitive evaluator transport. -/
theorem action_links (root : NativeEff) (table : RowTable) (m : NativeMachine) (f : Fiber)
    (y : Bool) (action : Action) :
    StackLinks m (evaluatePrim.withFiber (interpAt root m.completedExits table) m f y action).machine :=
  lookup_links (Moves.withFiber_interference (interpAt root m.completedExits table) m f y action).lookup

/-- Frame delegation only emits events; consumer: native primitive evaluation. -/
theorem frame_links (interp : Interp) (m : NativeMachine) (f : Fiber) (y : Bool) :
    StackLinks m (evaluatePrim.stepFrame interp m f y).machine :=
  lookup_links (Moves.stepFrame_interference interp m f y).lookup

/-- A selected finalizer changes only the local frame; consumer: native exits. -/
theorem finalizer_links (interp : Interp) (m : NativeMachine) (f : Fiber) (y : Bool) (exit : ExitV) :
    StackLinks m (evaluatePrim.finalizerOr interp m f y exit).machine :=
  lookup_links (Moves.finalizerOr_interference interp m f y exit).lookup

/-- All primitive evaluator cases protect pending command stacks; consumer: native evaluator. -/
theorem primitive_links (root : NativeEff) (table : RowTable) (m : NativeMachine) (f : Fiber) (y : Bool) :
    StackLinks m (evaluatePrim (interpAt root m.completedExits table) m f y).machine :=
  lookup_links (Moves.evaluatePrim_interference (interpAt root m.completedExits table) m f y).lookup

/-- Native scoped close also leaves stored stacks unchanged; consumer: actual native evaluation. -/
theorem scoped_links (root : NativeEff) (m : NativeMachine) (f : Fiber) (y : Bool) (exit : ExitV) :
    StackLinks m (exitScoped root m f y exit).machine :=
  lookup_links (Moves.exitScoped_interference root m f y exit).lookup

/-- Actual native evaluation preserves every old stored stack until settle installs its local fiber. -/
theorem native_links (root : NativeEff) (table : RowTable) (m : NativeMachine) (f : Fiber) (y : Bool) :
    StackLinks m (evaluateNative root m f y table).machine :=
  lookup_links (Moves.evaluateNative_interference root table m f y).lookup

/-- Counted iteration and forced yield retain every old stored stack for queue ownership transport. -/
theorem iteration_links (root : NativeEff) (table : RowTable) (m : NativeMachine) (f : Fiber) (y : Bool) :
    StackLinks m (iteration (evaluator := evaluatorFor root table) (interpOf root table) m f y).machine :=
  lookup_links (Moves.iteration_interference root table (interpOf root table) m f y).lookup

end Effect4.Program.ReleaseCustody.NativeStacks
