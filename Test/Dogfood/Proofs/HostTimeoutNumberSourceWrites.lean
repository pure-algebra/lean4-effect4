import Test.Dogfood.Proofs.HostTimeoutNumberSourceSlots
import Test.Dogfood.Proofs.HostTimeoutNumberSourceActions
import Effect4.Laws.Program.CodeClosure.Qualified.Stable
import Effect4.Laws.Machine.AnswerFlowNativeExit

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the actual pending attempt retains the source operation selected for a numeric write.
Consumer: the coupled cleanup and count producers of both Timeout numeric endpoint goals.
Reach: the direct attempt subtree, actual captured bindings, and the existing reference census.
Limit: the writer annotation supplies no heap phase, race assignment, or initialized history.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberSourceWrites
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration HostTimeoutNumberSourceSlots

/-- A numeric writer retains its actual source leaf, evaluated request, and selected synchronous operation. -/
def Writes (context : CountContext) (operation : SyncOp) : Prop :=
  ∃ (point : Point) (row : NativeOp) (request : Term) (value : Val),
    At context point ∧
    Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.perform row request)) ∧
    evalTerm point.env request = some value ∧ row.syncOpOf point.env value = some operation

/-- Actual compiler operations retain exact source provenance instead of only their captured environment. -/
theorem operation (context : CountContext) (point : Point) (row : NativeOp) (request : Term)
    (value : Val) (op : SyncOp) (held : At context point)
    (found : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.perform row request)))
    (evaluated : evalTerm point.env request = some value)
    (selected : row.syncOpOf point.env value = some op) :
    CodeClosure.Qualified.OpAt (At context) (AnswerSlots.Prefix (bindings context)) (Writes context) op := by
  have actual : Writes context op := ⟨point, row, request, value, held, found, evaluated, selected⟩
  have broad := CodeClosure.Slots.operation_at (At context) (AnswerSlots.Prefix (bindings context))
    point.env row value op held.leading selected
  fun_cases CodeClosure.Qualified.OpAt (At context) (AnswerSlots.Prefix (bindings context)) (Writes context) op
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeClosure.Slots.OpAt, CodeClosure.Qualified.OpAt])

/-- The shared compiler and callback proof consumes the stronger actual-operation contract. -/
theorem contract (context : CountContext) : CodeClosure.Qualified.Contract HostTimeoutSource.program
    (At context) (AnswerSlots.Prefix (bindings context)) (Writes context) where
  compilation := CodeClosure.Qualified.compile_contract _ _ _ _ (transport context)
    (fun point row request value op found held evaluated selected =>
      operation context point row request value op held found evaluated selected)
  child := (transport context).child
  childWith := (transport context).childWith
  capture := (transport context).capture

/-- The actual attempt entry establishes the stronger writer graph using the existing compiler fold. -/
theorem entry_code (context : CountContext) :
    CodeClosure.Qualified.CodeAt (At context) (AnswerSlots.Prefix (bindings context))
      (Writes context) context.entry :=
  CodeClosure.Qualified.resolve_at _ fragment _ _ _ (contract context) _ (entry context)

/-- A selected update exposes the same operation's actual source permission. -/
theorem update_origin (context : CountContext) (key : RefKey) (term : Term) (env : List Val)
    (owned : CodeClosure.Qualified.CodeAt (At context) (AnswerSlots.Prefix (bindings context))
      (Writes context) (.sync (.op (.refUpdate key term env)))) :
    Writes context (.refUpdate key term env) := owned

/-- The writer witness retains the actual source update row and its evaluated reference. -/
theorem update_source (context : CountContext) (key : RefKey) (term : Term) (env : List Val)
    (owned : Writes context (.refUpdate key term env)) :
    ∃ (point : Point) (request : Term), At context point ∧ point.env = env ∧
      Node.at_ (.eff HostTimeoutSource.program) point.path =
        some (.eff (.perform (.refUpdateWith term) request)) ∧
      evalTerm point.env request = some (.cell key) := by
  obtain ⟨point, row, request, value, held, found, evaluated, selected⟩ := owned
  fun_cases NativeOp.syncOpOf row point.env value
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [NativeOp.syncOpOf])

/-- The existing reference census restricts an attempt's authored updates to its count and cleanup leaves. -/
theorem update_paths (context : CountContext) (point : Point) (term request : Term)
    (held : At context point)
    (found : Node.at_ (.eff HostTimeoutSource.program) point.path =
      some (.eff (.perform (.refUpdateWith term) request))) :
    point.path = origin ++ [0, 0] ∨ point.path = origin ++ [1, 1, 0] := by
  have member := HostTimeoutNumberSteps.ref_at point.path (.refUpdateWith term) request found
    (.inr (.inr ⟨term, rfl⟩))
  rw [HostTimeoutNumberSteps.refPaths_eq] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  have lower := held.subtree.length_le
  change 12 ≤ point.path.length at lower
  rcases member with first | second | third | count | read | cleanup | formRead | formWrite
  · rw [first] at lower; change 12 ≤ 1 at lower; omega
  · rw [second] at lower; change 12 ≤ 2 at lower; omega
  · rw [third] at lower; change 12 ≤ 3 at lower; omega
  · exact .inl count
  · rw [read] at found
    change (some (Node.eff (.perform .refGet (.var 0))) : Option (Node NativeOp)) =
      some (Node.eff (.perform (.refUpdateWith term) request)) at found
    cases found
  · exact .inr cleanup
  · rw [formRead] at lower; change 12 ≤ 10 at lower; omega
  · rw [formWrite] at lower; change 12 ≤ 10 at lower; omega

/-- Every selected synchronous update retains one of the two numeric writer positions. -/
theorem selected_update_paths (context : CountContext) (key : RefKey) (term : Term) (env : List Val)
    (owned : Writes context (.refUpdate key term env)) :
    ∃ point : Point, point.env = env ∧ At context point ∧
      (point.path = origin ++ [0, 0] ∨ point.path = origin ++ [1, 1, 0]) := by
  obtain ⟨point, request, held, same, found, evaluated⟩ := update_source context key term env owned
  exact ⟨point, same, held, update_paths context point term request held found⟩

/-- An actual attempt update writes only the counter or cleanup cell with its authored term. -/
theorem selected_update_shape (context : CountContext) (key : RefKey) (term : Term) (env : List Val)
    (owned : Writes context (.refUpdate key term env)) :
    (key = ⟨0⟩ ∧ term = HostTimeoutNumberEntry.countTerm) ∨
      (key = ⟨1⟩ ∧ term = HostTimeoutNumberPhaseFlow.cleanupTerm) := by
  obtain ⟨point, request, held, same, found, evaluated⟩ := update_source context key term env owned
  rcases update_paths context point term request held found with count | cleanup
  · rw [count] at found
    change (some (Node.eff (.perform (.refUpdateWith HostTimeoutNumberEntry.countTerm) (.var 0))) :
      Option (Node NativeOp)) = some (Node.eff (.perform (.refUpdateWith term) request)) at found
    cases found
    have value := held.leading.read 0 (by change 0 < 5; decide)
    change point.env[0]? = some (.cell ⟨0⟩) at value
    change point.env[0]? = some (.cell key) at evaluated
    rw [value] at evaluated
    exact .inl ⟨(Typed.cell_inj (Option.some.inj evaluated)).symm, rfl⟩
  · rw [cleanup] at found
    change (some (Node.eff (.perform (.refUpdateWith HostTimeoutNumberPhaseFlow.cleanupTerm) (.var 1))) :
      Option (Node NativeOp)) = some (Node.eff (.perform (.refUpdateWith term) request)) at found
    cases found
    have value := held.leading.read 1 (by change 1 < 5; decide)
    change point.env[1]? = some (.cell ⟨1⟩) at value
    change point.env[1]? = some (.cell key) at evaluated
    rw [value] at evaluated
    exact .inr ⟨(Typed.cell_inj (Option.some.inj evaluated)).symm, rfl⟩

/-- The older source annotation admits a fabricated update when only its environment matches. -/
theorem env_only_forged_update (context : CountContext) :
    CodeClosure.Slots.CodeAt (At context) (AnswerSlots.Prefix (bindings context))
      (.sync (.op (.refUpdate ⟨9⟩ HostTimeoutNumberEntry.countTerm (bindings context)))) := by
  change AnswerSlots.Prefix (bindings context) (bindings context)
  unfold AnswerSlots.Prefix
  exact List.take_length

/-- Exact writer provenance rejects the same fabricated update to an unrelated cell. -/
theorem forged_update_rejected (context : CountContext) :
    ¬ CodeClosure.Qualified.CodeAt (At context) (AnswerSlots.Prefix (bindings context)) (Writes context)
      (.sync (.op (.refUpdate ⟨9⟩ HostTimeoutNumberEntry.countTerm (bindings context)))) := by
  intro owned
  rcases selected_update_shape context ⟨9⟩ HostTimeoutNumberEntry.countTerm (bindings context) owned with
    ⟨same, term⟩ | ⟨same, term⟩
  all_goals cases same

/-- The pending frame keeps both its callback annotation and the selected-source writer graph. -/
structure FrameAt (context : CountContext) (frame : HostTimeoutFrames.NativeFrame) : Prop
    extends HostTimeoutNumberSourceSlots.FrameAt context frame where
  currentWrites : CodeClosure.Qualified.CodeAt (At context) (AnswerSlots.Prefix (bindings context))
    (Writes context) frame.current
  savedWrites : ∀ code ∈ frame.stack, CodeClosure.Qualified.CodeAt (At context)
    (AnswerSlots.Prefix (bindings context)) (Writes context) code
  actions : HostTimeoutNumberSourceActions.FrameAt context frame

/-- Frame metadata transport keeps the same current writer and each actual saved writer. -/
theorem FrameAt.fields (context : CountContext) (before after : HostTimeoutFrames.NativeFrame)
    (held : FrameAt context before) (current : after.current = before.current)
    (stack : after.stack = before.stack) : FrameAt context after := by
  refine ⟨held.toFrameAt.fields context before after current stack, ?_, ?_, held.actions.fields context before after current stack⟩
  · rw [current]; exact held.currentWrites
  · rw [stack]; exact held.savedWrites

/-- The actual compiler entry also supplies the count binder and its selected counter operation. -/
theorem entry_parts (context : CountContext) :
    CodeClosure.Qualified.CodeAt (At context) (AnswerSlots.Prefix (bindings context)) (Writes context) context.bound ∧
    CodeClosure.Qualified.CodeAt (At context) (AnswerSlots.Prefix (bindings context)) (Writes context) context.write := by
  have source := entry_code context
  change CodeClosure.Qualified.CodeAt (At context) (AnswerSlots.Prefix (bindings context)) (Writes context)
    (resolve HostTimeoutSource.program
      (HostTimeoutNumberEntry.attemptPoint context.captured (context.fuel + 1) context.delay context.n context.previous)) at source
  rw [HostTimeoutNumberEntry.attempt_code] at source
  exact ⟨source.1, source.1.1⟩

/-- Each admitted pre-count control position retains the exact source writer permission. -/
theorem count_frame (context : CountContext) (frame : HostTimeoutFrames.NativeFrame)
    (held : CountFrameAt context frame) : FrameAt context frame := by
  have broad := HostTimeoutNumberSourceSlots.count_frame context frame held
  have binder : CodeClosure.Qualified.CodeAt (At context) (AnswerSlots.Prefix (bindings context)) (Writes context)
      (.onSuccess context.write (.cont (context.point.child 0))) :=
    ⟨(entry_parts context).2, (transport context).child (entry context) 0⟩
  have finalizer : CodeClosure.Qualified.CodeAt (At context) (AnswerSlots.Prefix (bindings context)) (Writes context)
      (.onExit context.bound (.fin context.point) false) := ⟨(entry_parts context).1, entry context⟩
  have safeBinder : HostTimeoutNumberSourceActions.CodeAt context
      (.onSuccess context.write (.cont (context.point.child 0))) :=
    ⟨(HostTimeoutNumberSourceActions.entry_parts context).2, (transport context).child (entry context) 0⟩
  have safeFinalizer : HostTimeoutNumberSourceActions.CodeAt context
      (.onExit context.bound (.fin context.point) false) :=
    ⟨(HostTimeoutNumberSourceActions.entry_parts context).1, entry context⟩
  cases held with
  | entry current stack =>
    refine ⟨broad, ?_, ?_, ?_⟩
    · rw [current]; exact entry_code context
    · rw [stack]; intro code member; cases member
    · constructor
      · rw [current]; exact HostTimeoutNumberSourceActions.entry_code context
      · rw [stack]; intro code member; cases member
  | finalizer current stack =>
    refine ⟨broad, ?_, ?_, ?_⟩
    · rw [current]; exact (entry_parts context).1
    · rw [stack]; intro code member
      rw [List.mem_singleton] at member
      rw [member]; exact finalizer
    · constructor
      · rw [current]; exact (HostTimeoutNumberSourceActions.entry_parts context).1
      · rw [stack]; intro code member
        rw [List.mem_singleton] at member
        rw [member]; exact safeFinalizer
  | binder current stack =>
    refine ⟨broad, ?_, ?_, ?_⟩
    · rw [current]; exact (entry_parts context).2
    · rw [stack]; intro code member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same
      · rw [same]; exact binder
      · rw [same]; exact finalizer
    · constructor
      · rw [current]; exact (HostTimeoutNumberSourceActions.entry_parts context).2
      · rw [stack]; intro code member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with same | same
        · rw [same]; exact safeBinder
        · rw [same]; exact safeFinalizer

/-- The committed count reply retains its exact captured-source writer suffix. -/
theorem counted_frame (context : CountContext) (frame : HostTimeoutFrames.NativeFrame)
    (stack : frame.stack = [.onSuccess context.write (.cont (context.point.child 0)),
      .onExit context.bound (.fin context.point) false]) :
    FrameAt context {frame with current := .success .unit} := by
  have before := count_frame context {frame with current := context.write} (.binder _ rfl stack)
  exact ⟨HostTimeoutNumberSourceSlots.counted_frame context frame stack, trivial, before.savedWrites,
    ⟨trivial, before.actions.saved⟩⟩

/-- The exact selected-writer annotation specializes the existing shared stable family. -/
abbrev sourceSpec (context : CountContext) :=
  CodeClosure.Qualified.prefixSpec HostTimeoutSource.program Test.Dogfood.Scenario.Timeout.fetch.table
    (At context) (AnswerSlots.Prefix (bindings context)) (Writes context)

/-- Actual native finalizer dispatch retains the exact writer graph through the shared callback family. -/
theorem finalizer_frame (context : CountContext) (view : HostTimeoutFlow.View)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (current : fiber.frame.current = Prim.ofExit exit) (held : FrameAt context fiber.frame) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit
    FrameAt context next.fiber.frame := by
  let edge := CodeClosure.Qualified.prefixEdge (At context) (AnswerSlots.Prefix (bindings context)) (Writes context)
  have path := CodeClosure.Qualified.prefix_path (At context) (AnswerSlots.Prefix (bindings context))
    (Writes context) fiber.frame.stack held.savedWrites
  have good : AnswerFlow.ExitAt ((sourceSpec context).model view) () () exit := by cases exit <;> trivial
  obtain ⟨output, next⟩ := AnswerFlow.External.Native.finalizer_frame ((sourceSpec context).model view)
    (HostTimeoutFlow.interpreter view) edge (CodeClosure.Qualified.prefix_family HostTimeoutSource.program fragment (At context)
      (AnswerSlots.Prefix (bindings context)) (Writes context) (contract context)
      (fun p held view => completed context p view held) Test.Dogfood.Scenario.Timeout.fetch.table view)
    (fun world kind => by trivial) () () () machine fiber yielding exit current held.currentWrites path good
    (by intros; trivial) (by intros; rfl)
  obtain ⟨input, code, saved⟩ := next
  exact ⟨HostTimeoutNumberSourceSlots.finalizer_frame context view machine fiber yielding exit current held.toFrameAt,
    code, CodeClosure.Qualified.prefix_path_owned (At context) (AnswerSlots.Prefix (bindings context)) (Writes context) saved, HostTimeoutNumberSourceActions.finalizer_frame context view machine fiber yielding exit current held.actions⟩

/-- Actual terminal native dispatch retains the selected writer graph through its real callbacks.
Consumer: the pending whole-fiber native producer of both Timeout numeric endpoint histories. -/
theorem finalizer_native (context : CountContext) (view : HostTimeoutFlow.View)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (current : fiber.frame.current = Prim.ofExit exit) (held : FrameAt context fiber.frame) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit
    FrameAt context next.fiber.frame :=
  finalizer_frame context view machine fiber yielding exit current held

end Test.Dogfood.Proofs.HostTimeoutNumberSourceWrites
