import Effect4.Laws.Program.AnswerSlots.InitializedNativeRows
import Effect4.Laws.Program.Guard.ReturnCommands
import Effect4.Laws.Program.MaskRuns
import Effect4.Laws.Program.NativeAdminOrigin

/-!
Concept: store-typing R4 and reactive-scheduling R11.
Question: administrative action commands retain the actual broad-root saved suffix.
Reach: native action entry and its actual post-operation store, including interruption metadata.
Limit: the coupled command queue carries this demand through actual command settlement.
Consumer: afterInterrupt and closePar fields of the initialized command producer.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- An administrative answer enters the broad root class at the actual retained suffix. -/
def RootPath (spec : Spec) (world : World) (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) : Prop :=
  Ready spec world ∧ ∃ output, Effect4.Contracts.Path (Edge spec [] world) (.stable .root) output frame.stack

/-- Administrative queue permission reads the addressed row's saved suffix, independently of current code. -/
def AdminDemand (spec : Spec) (machine : NativeMachine) (command : Guard.NCmd) : Prop :=
  ∀ host, Guard.ReturnCommands.Local host command →
    ∀ fiber, machine.fiber? host = some fiber → RootPath spec ⟨host, machine.state⟩ fiber.frame

/-- The actual action retains the same broad-root input at its post-operation store. -/
theorem action_root_path (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (input output : Kind) (thunk : EffThunk) (action : Guard.ReturnFields.NAction)
    (current : fiber.frame.current = .withFiber thunk)
    (owned : CodeAt spec ⟨fiber.id, machine.state⟩ input fiber.frame.current)
    (saved : Effect4.Contracts.Path (Edge spec [] ⟨fiber.id, machine.state⟩) input output fiber.frame.stack)
    (found : (interpAt spec.root view spec.table).withFiberOf thunk = some action)
    (scopes : Effect4.Machine.ScopeFields.ScopesAt (Typed.scopeModel spec.toSpec) machine.state.scopes) :
    let next := evaluatePrim.withFiber (interpAt spec.root view spec.table) machine fiber yielding action
    RootPath spec ⟨fiber.id, next.machine.state⟩ next.fiber.frame := by
  obtain ⟨same, ready, permission⟩ := action_shape spec _ input thunk (current ▸ owned)
  subst input
  let next := evaluatePrim.withFiber (interpAt spec.root view spec.table) machine fiber yielding action
  have counts := action_counts spec view machine fiber yielding action
  have future : Future ⟨fiber.id, machine.state⟩ ⟨fiber.id, next.machine.state⟩ :=
    ⟨rfl, Nat.le_of_eq counts.1.symm, Nat.le_of_eq counts.2.symm⟩
  have afterReady := ready_future spec _ _ future ready
  have actual := Typed.interp_action_at spec.toSpec fragment view thunk action permission found
  have programs := SourceScope.ActionProgramsAt.mono spec.root action actual
    (fun _ _ code => CodeAt.stable afterReady code)
  have result := SourceScope.with_fiber_path (model spec view) (Edge spec view)
    spec.root view spec.table ⟨fiber.id, next.machine.state⟩ (.stable .root) output machine fiber yielding action
    (action_facts spec view _ afterReady)
    (code_rebase spec _ _ _ owned _ future counts.1.symm counts.2.symm)
    (path_future spec view _ _ future _ output fiber.frame.stack saved) programs
    (by
      intro scope exit state program closed
      exact .stable afterReady ((Typed.interp_close spec.toSpec view scope exit fiber.frame.interruptible
        fiber.id machine.state state (some program) scopes closed).2 program rfl))
  exact ⟨afterReady, output, result.2⟩

/-- Interruption changes no saved continuation and therefore retains administrative demand. -/
theorem RootPath.interruption (spec : Spec) (world : World) (fiber : SourceScope.SourceFiber) (cause : CauseV)
    (held : RootPath spec world fiber.frame) : RootPath spec world (interruptWithCause cause fiber).1.frame := by
  unfold interruptWithCause
  dsimp only
  repeat' split
  all_goals exact held

/-- Growing stores retain an already-ready administrative suffix. -/
theorem RootPath.future (spec : Spec) (first last : World) (future : Future first last)
    (frame : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (held : RootPath spec first frame) :
    RootPath spec last frame := by
  obtain ⟨ready, output, saved⟩ := held
  exact ⟨ready_future spec first last future ready, output, path_future spec [] first last future _ _ _ saved⟩

/-- An environment message preserves the saved suffix even when it delivers interruption. -/
theorem otherEdit_stack {before after : SourceScope.SourceFiber} (edit : Moves.OtherEdit before after) :
    after.frame.stack = before.frame.stack := by
  cases edit with
  | observe => rfl
  | filterObservers => rfl
  | interruptCause cause =>
    unfold interruptWithCause
    dsimp only
    repeat' split
    all_goals rfl

/-- The existing environment edit word preserves the actual saved suffix. -/
theorem otherEdits_stack {before after : SourceScope.SourceFiber} (edits : Moves.OtherEdits before after) :
    after.frame.stack = before.frame.stack := by
  induction edits with
  | refl => rfl
  | tail prior edit ih => exact (otherEdit_stack edit).trans ih

/-- Existing forward lookup edits transport a reserved administrative host's demand. -/
theorem AdminDemand.transport (spec : Spec) (before after : NativeMachine) (command : Guard.NCmd)
    (held : AdminDemand spec before command)
    (present : ∀ host, Guard.ReturnCommands.Local host command → ∃ fiber, before.fiber? host = some fiber)
    (edits : Moves.LookupEdits before after)
    (refs : before.state.refs.length ≤ after.state.refs.length)
    (deferred : before.state.deferreds.cells.length ≤ after.state.deferreds.cells.length) :
    AdminDemand spec after command := by
  intro host isLocal fiber found
  obtain ⟨old, previous⟩ := present host isLocal
  obtain ⟨next, seen, word⟩ := edits host old previous
  have same := Option.some.inj (seen.symm.trans found)
  subst next
  obtain ⟨ready, output, saved⟩ := held host isLocal old previous
  refine ⟨ready_future spec ⟨host, before.state⟩ ⟨host, after.state⟩ ⟨rfl, refs, deferred⟩ ready, output, ?_⟩
  rw [otherEdits_stack word]
  exact path_future spec [] ⟨host, before.state⟩ ⟨host, after.state⟩ ⟨rfl, refs, deferred⟩ _ _ _ saved

/-- Tracked children exist only after the source initializer completes. -/
def ChildrenReady (spec : Spec) (machine : NativeMachine) : Prop :=
  ∀ fiber ∈ machine.fibers, fiber.children ≠ [] → Ready spec ⟨fiber.id, machine.state⟩

/-- The sole command that adds a tracked child carries readiness from its source action. -/
def TrackDemand (spec : Spec) (machine : NativeMachine) : Guard.NCmd → Prop
  | .trackChild _ _ => Ready spec ⟨⟨0⟩, machine.state⟩
  | _ => True

/-- Other-fiber messages never add or remove tracked children. -/
theorem otherEdit_children {before after : SourceScope.SourceFiber} (edit : Moves.OtherEdit before after) :
    after.children = before.children := by
  cases edit with
  | observe => rfl
  | filterObservers => rfl
  | interruptCause cause =>
    unfold interruptWithCause
    dsimp only
    repeat' split
    all_goals rfl

/-- The existing message word preserves tracked children. -/
theorem otherEdits_children {before after : SourceScope.SourceFiber} (edits : Moves.OtherEdits before after) :
    after.children = before.children := by
  induction edits with
  | refl => rfl
  | tail prior edit ih => exact (otherEdit_children edit).trans ih

/-- Existing interference preserves child readiness; its actual births have empty children. -/
theorem ChildrenReady.interferes (spec : Spec) (before after : NativeMachine)
    (held : ChildrenReady spec before) (changes : Moves.Interferes before after)
    (refs : before.state.refs.length ≤ after.state.refs.length)
    (deferred : before.state.deferreds.cells.length ≤ after.state.deferreds.cells.length) :
    ChildrenReady spec after := by
  intro fiber member nonempty
  rcases changes.fibers fiber member with ⟨old, present, edits⟩ | ⟨lower, program, flag, budget, context, edits⟩
  · have ready := held old present (by rw [← otherEdits_children edits]; exact nonempty)
    exact ⟨Nat.le_trans ready.1 refs, Nat.le_trans ready.2 deferred⟩
  · have empty : fiber.children = [] := otherEdits_children edits
    exact (nonempty empty).elim

/-- Actual native evaluation preserves readiness of every tracked child list. -/
theorem native_children (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : ChildrenReady spec machine) :
    ChildrenReady spec (evaluateNative spec.root machine fiber yielding spec.table).machine := by
  have growth := native_growth spec machine fiber yielding
  exact ChildrenReady.interferes spec machine _ held (Moves.evaluateNative_interferes spec.root spec.table machine fiber yielding)
    growth.1 growth.2

/-- Actual charged iteration preserves readiness of every tracked child list. -/
theorem iteration_children (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : ChildrenReady spec machine) :
    ChildrenReady spec (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).machine := by
  have growth := iteration_growth spec machine fiber yielding
  exact ChildrenReady.interferes spec machine _ held (Moves.iteration_interferes spec.root spec.table (interpOf spec.root spec.table) machine fiber yielding)
    growth.1 growth.2

/-- A pending finish addresses the actual drained suffix, independently of its retained current code. -/
def TerminalDemand (spec : Spec) (machine : NativeMachine) : Guard.NCmd → Prop
  | .finish host _ => ∀ fiber, machine.fiber? host = some fiber → fiber.frame.stack = [] ∧ (fiber.children ≠ [] → Ready spec ⟨host, machine.state⟩)
  | _ => True

/-- Installing the returned parent retains child readiness from its actual unchanged child list. -/
theorem ChildrenReady.install (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (held : ChildrenReady spec machine)
    (parent : fiber.children ≠ [] → Ready spec ⟨fiber.id, machine.state⟩) :
    ChildrenReady spec (machine.update fiber) := by
  intro row member nonempty
  obtain ⟨old, present, same⟩ := List.mem_map.mp member
  rw [← same] at nonempty ⊢
  by_cases key : old.id = fiber.id
  · simp only [if_pos key] at nonempty ⊢
    exact parent nonempty
  · simp only [if_neg key] at nonempty ⊢
    exact held old present nonempty

/-- The loaded machine has no tracked children. -/
theorem initial_children (spec : Spec) (fuel : Nat) : ChildrenReady spec (Api.load spec.root fuel) := by
  intro fiber member nonempty
  have same := List.mem_singleton.mp member
  subst fiber
  exact (nonempty rfl).elim

/-- The existing native mask theorem supplies the actual drained finished suffix. -/
theorem native_finished_stack (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (exit : ExitV)
    (finished : (evaluateNative spec.root machine fiber yielding spec.table).outcome = .finished exit) :
    (evaluateNative spec.root machine fiber yielding spec.table).fiber.frame.stack = [] :=
  (Effect4.Program.evaluateNative_keepsMask spec.root spec.table machine fiber yielding).finished_stack finished

/-- The existing generic charged mask theorem supplies the actual drained finished suffix. -/
theorem iteration_finished_stack (spec : Spec) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (yielding : Bool) (exit : ExitV)
    (finished : (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).outcome = .finished exit) :
    (iteration (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table) machine fiber yielding).fiber.frame.stack = [] := by
  have kept := iteration_keepsMask (evaluator := evaluatorFor spec.root spec.table) (interpOf spec.root spec.table)
    (fun m f y => Effect4.Program.evaluateNative_keepsMask spec.root spec.table m f y) machine fiber yielding
  exact kept.finished_stack finished

/-- The queued administrative host retains the source action head until its command executes. -/
def AdminHead (machine : NativeMachine) (command : Guard.NCmd) : Prop :=
  ∀ host, Guard.ReturnCommands.Local host command → ∀ fiber, machine.fiber? host = some fiber →
    ∃ thunk, fiber.frame.current = .withFiber thunk

/-- Actual current-code classification recovers the root suffix when the queued command executes. -/
theorem admin_of_head (spec : Spec) (machine : NativeMachine) (command : Guard.NCmd)
    (frames : FramesAt spec machine) (head : AdminHead machine command) : AdminDemand spec machine command := by
  intro host isLocal fiber found
  obtain ⟨thunk, current⟩ := head host isLocal fiber found
  obtain ⟨input, output, code, saved⟩ := frames fiber (List.mem_of_find?_eq_some found)
  obtain ⟨same, ready, permission⟩ := action_shape spec ⟨fiber.id, machine.state⟩ input thunk (current ▸ code)
  subst input
  rw [← Guard.fiber_id_of_lookup found]
  exact ⟨ready, output, saved⟩

/-- The existing guard current-code transport carries administrative heads without saved-graph transport. -/
theorem AdminHead.transport (root : NativeEff) (table : RowTable) (before after : NativeMachine)
    (command : Guard.NCmd) (head : AdminHead before command)
    (authority : Guard.CommandAuthority root table before command)
    (controls : Guard.CommandControlsPreserved before after) : AdminHead after command := by
  intro host isLocal fiber found
  have owner := NativeAdminOrigin.owner before command host (NativeAdminOrigin.of_guard command host isLocal)
  obtain ⟨old, previous, running, parked⟩ := Guard.commandAuthority_owner_active root table before command host authority owner
  obtain ⟨next, seen, nextRunning, nextParked, current⟩ := controls.active host old previous running parked
  have same := Option.some.inj (seen.symm.trans found)
  subst next
  obtain ⟨thunk, source⟩ := head host isLocal old previous
  exact ⟨thunk, current.trans source⟩
end Effect4.Program.AnswerSlots.Initialized
