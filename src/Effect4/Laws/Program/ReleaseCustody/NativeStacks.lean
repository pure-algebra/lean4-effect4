import Effect4.Laws.Program.ReleaseCustody.NativeSequencing
import Effect4.Laws.Program.ReleaseCustody.CommandStackSteps

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
open Effect4.Program.ReleaseCustody.RuntimeShape Effect4.Program.ReleaseCustody.CommandStacks
abbrev Interp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev Action := WithFiberAction EffName EffThunk Val Err Defect FiberId Ann Ctx

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
  append_links _ _

/-- Scheduling a spawned child retains the table; consumer: fork action transport. -/
theorem start_links (m : NativeMachine) (f : Fiber) (child : FiberId) (immediately : Bool) :
    StackLinks m (start m f child immediately).1 := by
  unfold start
  split <;> exact StackLinks.of_fibers rfl

/-- Countdown registration edits observers only; consumer: native await and park cases. -/
theorem countdown_links (interp : Interp) (m : NativeMachine) (f : Fiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool) :
    StackLinks m (countdownPark interp m f targets resume failFast).1 := by
  unfold countdownPark
  dsimp only
  split
  · exact StackLinks.of_fibers rfl
  · rename_i exits target rest found
    exact ((StackLinks.of_fibers (m := m) (n := {m with nextToken := m.nextToken + 1}) rfl).trans
      (modify_links _ target (fun g => {g with observers := g.observers ++ [.countdown f.id m.nextToken]})
        (fun _ => rfl) (fun _ => rfl))).emit _

/-- Parallel cleanup appends children without replacing old rows; consumer: closePar. -/
theorem finalizers_links (interp : Interp) (m : NativeMachine) (f : Fiber) (programs : List NCode) :
    StackLinks m (forkFinalizers interp m f programs).1 := by
  induction programs generalizing m with
  | nil => exact StackLinks.of_fibers rfl
  | cons program rest ih =>
    exact (spawn_links interp m f program ⟨true,true,.inherit⟩ []).trans (ih _)

/-- Recording an interrupt retains the stored target stack; consumer: interruptAs. -/
theorem interrupt_links (root : NativeEff) (table : RowTable) (m : NativeMachine) (f : Fiber)
    (y : Bool) (target who : FiberId) :
    StackLinks m (evaluatePrim.interruptAs (interpAt root m.completedExits table) m f y target who).machine := by
  unfold evaluatePrim.interruptAs
  split
  · exact StackLinks.of_fibers rfl
  · rename_i fiber found
    exact CommandStacks.interrupt_links root table m fiber
      (by rw [Guard.fiber_id_of_lookup found]; exact found) (some who) _ |>.emit _

/-- Every actual fiber action protects existing queued stacks. Consumer: primitive evaluator transport. -/
theorem action_links (root : NativeEff) (table : RowTable) (m : NativeMachine) (f : Fiber)
    (y : Bool) (action : Action) :
    StackLinks m (evaluatePrim.withFiber (interpAt root m.completedExits table) m f y action).machine := by
  cases action <;> simp only [evaluatePrim.withFiber]
  case fork program options site =>
    let base : NativeMachine := if options.daemon then m else {m with middlewareInstalled := true}
    have first : StackLinks m base := StackLinks.of_fibers (by unfold base; split <;> rfl)
    have born := spawn_links (interpAt root m.completedExits table) base f program options site
    have begun := start_links (spawn (interpAt root m.completedExits table) base f program options site).1
      (spawn (interpAt root m.completedExits table) base f program options site).2.1
      (spawn (interpAt root m.completedExits table) base f program options site).2.2 options.startImmediately
    exact first.trans (born.trans begun)
  case forkIn program options scope site =>
    have born := spawn_links (interpAt root m.completedExits table) m f program {options with daemon := true} site
    exact born.trans (start_links _ _ _ options.startImmediately)
  case forkScoped program options site =>
    split
    · have born := spawn_links (interpAt root m.completedExits table) m f program {options with daemon := true} site
      exact born.trans (start_links _ _ _ options.startImmediately)
    · exact StackLinks.of_fibers rfl
  case runIn target scope =>
    have same : linkScope (interpAt root m.completedExits table) m .fiberRunIn scope target
        (some target) ReasonAnnotations.empty =
      linkScope (interpOf root table) m .fiberRunIn scope target (some target) ReasonAnnotations.empty := by
      unfold linkScope
      simp only [interpAt]
      rfl
    rw [same]
    exact linkScope_links root table m .fiberRunIn scope target (some target) ReasonAnnotations.empty
  case interruptAs target who => exact interrupt_links root table m f y target who
  case awaitAll targets => exact countdown_links (interpAt root m.completedExits table) m f targets .exitsValue false
  case awaitAllFailFast targets => exact countdown_links (interpAt root m.completedExits table) m f targets .exitsValue true
  case awaitNewChildren snapshot => exact countdown_links (interpAt root m.completedExits table) m f _ .void false
  case closePar finalizers => exact finalizers_links (interpAt root m.completedExits table) m f finalizers
  case dropObservers => exact map_links _ _ (fun _ => rfl) (fun _ => rfl)
  case ambientScope =>
    cases (interpAt root m.completedExits table).ambientScope f.context <;> exact StackLinks.of_fibers rfl
  case interruptScoped target =>
    by_cases same : target = f.id <;> simp only [same, if_true, if_false]
    all_goals exact StackLinks.of_fibers rfl
  case setInterruptible body flag => cases flag <;> exact StackLinks.of_fibers rfl
  case setContext context =>
    cases (interpAt root m.completedExits table).budgetOf context
    exact StackLinks.of_fibers rfl
  case closeScope scope exit =>
    cases (interpAt root m.completedExits table).closeScope scope exit f.frame.interruptible f.id m.state
    all_goals exact StackLinks.of_fibers rfl
  case cancelRace race => cases m.race? race <;> exact StackLinks.of_fibers rfl
  all_goals exact StackLinks.of_fibers rfl

/-- Frame delegation only emits events; consumer: native primitive evaluation. -/
theorem frame_links (interp : Interp) (m : NativeMachine) (f : Fiber) (y : Bool) :
    StackLinks m (evaluatePrim.stepFrame interp m f y).machine := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  dsimp only
  split <;> exact StackLinks.of_fibers rfl

/-- A selected finalizer changes only the local frame; consumer: native exits. -/
theorem finalizer_links (interp : Interp) (m : NativeMachine) (f : Fiber) (y : Bool) (exit : ExitV) :
    StackLinks m (evaluatePrim.finalizerOr interp m f y exit).machine := by
  unfold evaluatePrim.finalizerOr
  dsimp only
  split
  · split
    · exact StackLinks.of_fibers rfl
    · exact frame_links _ _ _ _
  · exact frame_links _ _ _ _

/-- All primitive evaluator cases protect pending command stacks; consumer: native evaluator. -/
theorem primitive_links (root : NativeEff) (table : RowTable) (m : NativeMachine) (f : Fiber) (y : Bool) :
    StackLinks m (evaluatePrim (interpAt root m.completedExits table) m f y).machine := by
  unfold evaluatePrim
  split
  · exact StackLinks.of_fibers rfl
  · dsimp only
    split
    · exact StackLinks.of_fibers rfl
    · split <;> exact StackLinks.of_fibers rfl
  · split
    · exact StackLinks.of_fibers rfl
    · unfold registerRace
      split <;> exact StackLinks.of_fibers rfl
    · exact countdown_links _ _ _ _ _ _
    · split
      · exact StackLinks.of_fibers rfl
      · rename_i fiber found
        split
        · exact StackLinks.of_fibers rfl
        · apply update_links _ fiber _
          · rw [Guard.fiber_id_of_lookup found]; exact found
          · rfl
    · split
      · split
        · exact action_links root table m f y _
        · exact frame_links _ _ _ _
      · split <;> exact StackLinks.of_fibers rfl
      · exact finalizer_links _ _ _ _ _
      · exact finalizer_links _ _ _ _ _
      · exact frame_links _ _ _ _

/-- Native scoped close also leaves stored stacks unchanged; consumer: actual native evaluation. -/
theorem scoped_links (root : NativeEff) (m : NativeMachine) (f : Fiber) (y : Bool) (exit : ExitV) :
    StackLinks m (exitScoped root m f y exit).machine := by
  unfold exitScoped
  dsimp only
  split
  · split
    · exact StackLinks.of_fibers rfl
    · rename_i state program found
      cases program <;> exact StackLinks.of_fibers rfl
  · exact primitive_links root [] m f y

/-- Actual native evaluation preserves every old stored stack until settle installs its local fiber. -/
theorem native_links (root : NativeEff) (table : RowTable) (m : NativeMachine) (f : Fiber) (y : Bool) :
    StackLinks m (evaluateNative root m f y table).machine := by
  unfold evaluateNative
  split
  · split
    · exact StackLinks.of_fibers rfl
    · exact primitive_links root table m f y
  · exact scoped_links root m f y _
  · exact scoped_links root m f y _
  · exact primitive_links root table m f y

/-- Counted iteration and forced yield retain every old stored stack for queue ownership transport. -/
theorem iteration_links (root : NativeEff) (table : RowTable) (m : NativeMachine) (f : Fiber) (y : Bool) :
    StackLinks m (iteration (evaluator := evaluatorFor root table) (interpOf root table) m f y).machine := by
  unfold iteration
  dsimp only
  cases injected : injectYield m (countOp (runloopTop f)) y with
  | none => exact native_links root table m _ y
  | some it =>
    unfold injectYield at injected
    split at injected
    · cases injected
      dsimp only
      apply StackLinks.trans (n := m.emit [.yieldInjected (countOp (runloopTop f)).id (countOp (runloopTop f)).currentOpCount])
      · exact StackLinks.of_fibers rfl
      · exact native_links root table _ _ _
    · cases injected
end Effect4.Program.ReleaseCustody.NativeStacks
