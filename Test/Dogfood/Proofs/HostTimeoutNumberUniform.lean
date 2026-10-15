import Test.Dogfood.Proofs.HostTimeoutNumberPhasePureHead
import Effect4.Laws.Machine.AnswerFlowViewsRefined
import Effect4.Laws.Contracts.FramePathOrder

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: both Timeout numeric goals retain one set of saved answer classes across actual interpreter views.
Consumer: the pending native producer and its actual finalizer installation.
Reach: nonrecursive numeric saved frames with common input and output classes.
Limit: source capture and actual cleanup provenance remain separate premises.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberUniform
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberPhaseFlow

/-- One saved certificate keeps its classes and actual restoring-mask authority together. -/
structure Edge (state : Stores) (input output : Kind) (frame : NCode)
    extends AnswerFlow.ViewSavedAt (fun view => model view)
      (fun view => (HostTimeoutFlow.interpreter view).toPrimInterp) state input output frame where
  restores : frame = .setInterruptible true → HostTimeoutNumberMaskClass.Restorable input
  generated : ∀ fiber : HostTimeoutFrames.NativeFrame,
    (frame.ensure fiber).1.stack = .setInterruptible true :: fiber.stack →
    HostTimeoutNumberMaskClass.Restorable output
  ordered : input.grade ≤ output.grade
  finalizerInput : ∀ body name flag, frame = .onExit body name flag → input.grade ≤ 1
  finalizerFlag : ∀ body name flag, frame = .onExit body name flag → flag = false
  crossing : input.grade ≤ 1 → 1 < output.grade → ∃ body point, frame = .onExit body (.fin point) false
  owner : input.ownerCount = output.ownerCount
  valid : output.Valid → input.Valid

/-- The same authored saved edge retains its numeric classes after an admitted reference write. -/
theorem Edge.future (before after : Stores) (input output : Kind) (frame : NCode)
    (future : HostTimeoutNumberFlow.Future before after) (held : Edge before input output frame) :
    Edge after input output frame :=
  ⟨AnswerFlow.ViewSavedAt.future (fun view => model view)
    (fun view => (HostTimeoutFlow.interpreter view).toPrimInterp) (fun _ => future) held.toViewSavedAt, held.restores, held.generated, held.ordered, held.finalizerInput, held.finalizerFlag, held.crossing, held.owner, held.valid⟩

/-- A hook that keeps its stack cannot also push a restoring mask. -/
theorem no_push (before after : List NCode) (same : after = before)
    (pushed : after = .setInterruptible true :: before) : False := by
  have lengths := congrArg List.length (same.symm.trans pushed)
  simp only [List.length_cons] at lengths
  omega

/-- A numeric frame retains one input class and one uniformly certified saved path. -/
def FrameAt (state : Stores) (output : Kind) (frame : HostTimeoutFrames.NativeFrame) : Prop :=
  AnswerFlow.FamilyResult (model []) Edge state output frame.current frame.stack

/-- The shared view family supplies actual callbacks without another saved-frame induction. -/
theorem family (view : HostTimeoutFlow.View) :
    AnswerFlow.SavedFamily (model view) (HostTimeoutFlow.interpreter view).toPrimInterp Edge :=
  AnswerFlow.ViewSavedAt.refined_family (fun view => model view)
    (fun view => (HostTimeoutFlow.interpreter view).toPrimInterp) Edge
    (fun _ _ _ _ held => held.toViewSavedAt) view

/-- A uniformly certified saved path gives its ordinary semantic path at the actual view. -/
theorem path (view : HostTimeoutFlow.View) (state : Stores) (input output : Kind) (stack : List NCode)
    (held : Effect4.Contracts.Path (Edge state) input output stack) :
    AnswerFlow.StackAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp state input output stack := by
  exact AnswerFlow.path_stack (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
    (Effect4.Contracts.Path.map (fun _ _ _ edge => edge.each view) held)

/-- The uniform frame supplies every previous view-specific frame reader with the same input class. -/
theorem FrameAt.each (state : Stores) (output : Kind) (frame : HostTimeoutFrames.NativeFrame)
    (held : FrameAt state output frame) (view : HostTimeoutFlow.View) :
    AnswerFlow.FrameAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp state output frame := by
  obtain ⟨input, code, saved⟩ := held
  exact ⟨input, code, path view state input output frame.stack saved⟩

/-- All numeric head constructors introduce the same nonrecursive saved shapes once. -/
theorem head_edges : HostTimeoutNumberPhaseHead.HeadEdges Edge := by
  constructor
  · intro state input output body name ordered region owner valid each
    refine ⟨⟨each, ?_, ?_⟩, ?_, ?_, ordered, ?_, ?_, ?_, owner, valid⟩
    · intro name cursor impossible; cases impossible
    · intro name cursor impossible; cases impossible
    · intro impossible; cases impossible
    · intro fiber pushed; exact False.elim (no_push _ _ rfl pushed)
    · intro body name flag impossible; cases impossible
    · intro body name flag impossible; cases impossible
    · intro early later
      exact False.elim (Nat.not_le_of_gt later (region early))
  · intro state input output body name ordered region owner valid each
    refine ⟨⟨each, ?_, ?_⟩, ?_, ?_, ordered, ?_, ?_, ?_, owner, valid⟩
    · intro name cursor impossible; cases impossible
    · intro name cursor impossible; cases impossible
    · intro impossible; cases impossible
    · intro fiber pushed; exact False.elim (no_push _ _ rfl pushed)
    · intro body name flag impossible; cases impossible
    · intro body name flag impossible; cases impossible
    · intro early later
      exact False.elim (Nat.not_le_of_gt later (region early))
  · intro state input output body next ordered region owner valid each
    refine ⟨⟨each, ?_, ?_⟩, ?_, ?_, ordered, ?_, ?_, ?_, owner, valid⟩
    · intro name cursor impossible; cases impossible
    · intro name cursor impossible; cases impossible
    · intro impossible; cases impossible
    · intro fiber pushed; exact False.elim (no_push _ _ rfl pushed)
    · intro body name flag impossible; cases impossible
    · intro body name flag impossible; cases impossible
    · intro early later
      exact False.elim (Nat.not_le_of_gt later (region early))
  · intro state input output body name flag low flagFalse finName restorable ordered owner valid each
    refine ⟨⟨each, ?_, ?_⟩, ?_, ?_, ordered, ?_, ?_, ?_, owner, valid⟩
    · intro name cursor impossible; cases impossible
    · intro name cursor impossible; cases impossible
    · intro impossible; cases impossible
    · intro fiber pushed; exact restorable
    · intro selectedBody selectedName selectedFlag actual
      exact low
    · intro selectedBody selectedName selectedFlag actual
      cases actual
      exact flagFalse
    · intro early later
      obtain ⟨point, same⟩ := finName
      cases same
      cases flagFalse
      exact ⟨body, point, rfl⟩

/-- The single numeric head proof also supplies uniform saved edges. -/
theorem head (view : HostTimeoutFlow.View) (state : Stores) (kind : Kind) (program : NCode)
    (owned : CodeAt state kind program) (noSync : ∀ thunk, program ≠ .sync thunk)
    (noAction : ∀ thunk, program ≠ .withFiber thunk) :
    AnswerFlow.HeadAt (model view) (HostTimeoutFlow.interpreter view).toPrimInterp Edge state kind program :=
  HostTimeoutNumberPhaseHead.head_over Edge head_edges view state kind program owned noSync noAction

/-- Actual ordinary delegation retains the one uniform path at the actual interpreter view. -/
theorem ordinary_native (view : HostTimeoutFlow.View) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (output : Kind)
    (held : FrameAt machine.state output fiber.frame)
    (noSuccess : ∀ value, fiber.frame.current ≠ .success value)
    (noFailure : ∀ cause, fiber.frame.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.frame.current ≠ .sync thunk)
    (ordinary : ∀ thunk, fiber.frame.current = .withFiber thunk →
      (HostTimeoutFlow.interpreter view).withFiberOf thunk = none) :
    let next := evaluatePrim.stepFrame (HostTimeoutFlow.interpreter view) machine fiber yielding
    FrameAt next.machine.state output next.fiber.frame := by
  obtain ⟨next, events, actual, good⟩ := HostTimeoutNumberPhaseHead.ordinary_running_over Edge head_edges
    view machine.state output fiber.frame held noSuccess noFailure noSync ordinary
  simp only [evaluatePrim.stepFrame, actual, evaluatePrim.finishFrame]
  exact good

/-- A saved interruptibility flag is uniform and retains exactly the same numeric answer class. -/
theorem mask (state : Stores) (kind : Kind) (flag : Bool)
    (restorable : HostTimeoutNumberMaskClass.Restorable kind) :
    Edge state kind kind (.setInterruptible flag) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, Nat.le_refl _, ?_, ?_, ?_, rfl, (fun good => good)⟩
  · intro view
    exact AnswerFlow.saved_mask (model view) (HostTimeoutFlow.interpreter view).toPrimInterp state kind flag
  · intro name cursor impossible; cases impossible
  · intro name cursor impossible; cases impossible
  · intro actual; exact restorable
  · intro fiber pushed
    exact False.elim (no_push _ _ (Prim.ensure_setInterruptible_stack flag fiber) pushed)
  · intro body name flag impossible; cases impossible
  · intro body name flag impossible; cases impossible
  · intro early later
    exact False.elim (Nat.not_le_of_gt later early)

/-- Only the actual source edge authorizes its generated mask's answer class. -/
theorem hook_mask : AnswerFlow.Contextual.HookMask Edge := by
  intro state input output code held fiber pushed
  exact mask state output true (held.generated fiber pushed)

/-- One actual saved path retains its numeric owner count and pending endpoint validity together. -/
theorem anchors (state : Stores) (input output : Kind) (stack : List NCode)
    (path : Effect4.Contracts.Path (Edge state) input output stack) :
    input.ownerCount = output.ownerCount ∧ (output.Valid → input.Valid) := by
  exact Effect4.Contracts.Path.endpoints
    (fun first last : Kind => first.ownerCount = last.ownerCount ∧ (last.Valid → first.Valid))
    (fun _ => ⟨rfl, fun good => good⟩)
    (fun _ _ _ first second => ⟨first.1.trans second.1, fun good => first.2 (second.2 good)⟩)
    (fun _ _ _ edge => ⟨edge.owner, edge.valid⟩) path

/-- An actual early numeric answer with a later saved output retains an authored protected finalizer. -/
theorem early_finalizer (state : Stores) (input output : Kind) (stack : List NCode)
    (path : Effect4.Contracts.Path (Edge state) input output stack)
    (early : input.grade ≤ 1) (later : 1 < output.grade) :
    ∃ body point, (.onExit body (.fin point) false : NCode) ∈ stack := by
  obtain ⟨first, last, frame, member, owned, low, high⟩ :=
    Effect4.Contracts.Path.crossing_member Kind.grade 1 path early later
  obtain ⟨body, point, actual⟩ := owned.crossing low high
  cases actual
  exact ⟨body, point, member⟩

/-- An ordinary constant frame cannot stand in for the authored early-to-late finalizer crossing.
Control: pre-entry yield uses the actual paused class instead of this fabricated saved annotation. -/
theorem early_constant_control (state : Stores) (before entered : HostTimeoutNumberPhase.Phase)
    (own : entered.count = entered.cleanups.length + 1) (first body : NCode) :
    ¬ Edge state (.fresh before) (.attempt before entered own) (.onSuccessConst first body) := by
  intro held
  obtain ⟨saved, point, impossible⟩ := held.crossing (by dsimp only [Kind.grade]; decide)
    (by dsimp only [Kind.grade]; decide)
  cases impossible

end Test.Dogfood.Proofs.HostTimeoutNumberUniform
