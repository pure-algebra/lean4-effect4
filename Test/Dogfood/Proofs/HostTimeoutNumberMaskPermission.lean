import Test.Dogfood.Proofs.HostTimeoutNumberConfiguration
import Effect4.Laws.Contracts.FramePathOrder

/-!
Concept: scope-lifetime-finalization R11.
Question: the actual entered attempt cannot expose its protected numeric answer classes while unmasked.
Consumer: the loop-top and interruption branches of both Timeout numeric history endpoints.
Reach: actual authored-finalizer custody and the same uniformly ordered saved path.
Limit: the actual source producer still establishes custody and the selected numeric input class.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberMaskPermission
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration HostTimeoutNumberPhaseFlow

/-- A later saved-answer class has already crossed the authored finalizer's input boundary and therefore stays masked. -/
theorem later_masked (context : CountContext) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (held : FiberAt machine (.pending context) fiber) (heap : At context.entered machine.state)
    (input output : Kind)
    (path : Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge machine.state) input output fiber.frame.stack)
    (later : 1 < input.grade) : fiber.frame.interruptible = false := by
  cases actual : fiber.frame.interruptible with
  | false => rfl
  | true =>
    obtain ⟨point, body, source, installed⟩ := held.pendingCustody context rfl heap actual
    have absent := Effect4.Contracts.Path.not_mem_of_grade Kind.grade
      (fun first last frame edge => edge.ordered) path
      (.onExit body (.fin point) false) 1
      (fun first last edge => edge.finalizerInput _ _ _ rfl) later
    exact False.elim (absent installed)

/-- Actual protected numeric execution reaches the native operation without loop-top failure replacement. -/
theorem later_top (context : CountContext) (machine : NativeMachine) (fiber : SourceScope.SourceFiber)
    (held : FiberAt machine (.pending context) fiber) (heap : At context.entered machine.state)
    (input output : Kind)
    (path : Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge machine.state) input output fiber.frame.stack)
    (later : 1 < input.grade) : runloopTop fiber = fiber := by
  have masked := later_masked context machine fiber held heap input output path later
  have clear := held.pendingDeferred context rfl masked
  simp only [runloopTop, clear, Bool.false_eq_true, ↓reduceIte]

/-- The same actual attempt's late restoring-mask permission excludes its unclean entered heap.
The uniform path supplies owner equality and pending validity; no unrelated published phase is admitted. -/
theorem restoring_late_ne_entered (context : CountContext) (state : Stores) (kind : Kind)
    (owner : kind.ownerCount = context.entered.count) (valid : kind.Valid)
    (restorable : HostTimeoutNumberMaskClass.Restorable kind) (later : 1 < kind.grade)
    (permitted : (∃ value, ValueAt state kind value) ∨ ∃ cause, CauseAt state kind cause) :
    ¬ At context.entered state := by
  intro heap
  have fields : ∀ phase : HostTimeoutNumberPhase.Phase, At phase state →
      phase.count = context.entered.count ∧ phase.cleanups.length = context.entered.cleanups.length := by
    intro phase selected
    have equal := selected.symm.trans heap
    have number := congrArg (fun image : RefHeap => image[0]?) equal
    have cleanups := congrArg (fun image : RefHeap => image[1]?) equal
    change some (Val.nat phase.count) = some (.nat context.entered.count) at number
    change some (Val.list phase.cleanups) = some (.list context.entered.cleanups) at cleanups
    exact ⟨congrArg (fun value : Val => match value with | .nat n => n | _ => 0) (Option.some.inj number),
      congrArg (fun value : Val => match value with | .list xs => xs.length | _ => 0) (Option.some.inj cleanups)⟩
  have completed : ∀ phase : HostTimeoutNumberPhase.Phase,
      ∀ own : phase.count = phase.cleanups.length + 1, ∀ interrupted,
      phase.count = context.entered.count → At (phase.cleanup own interrupted) state → False := by
    intro phase own interrupted anchored selected
    have lengths := (fields _ selected).2
    change (phase.cleanups ++ [Val.list [Val.nat phase.count, Val.bool interrupted]]).length =
      context.before.cleanups.length at lengths
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at lengths
    change phase.count = context.before.count + 1 at anchored
    have previous := context.cleanups
    omega
  cases kind with
  | fresh phase => change 1 < 0 at later; omega
  | countUnit phase => change 1 < 1 at later; omega
  | before phase => change 1 < 1 at later; omega
  | read phase => exact False.elim restorable
  | unit phase => exact False.elim restorable
  | paused phase incoming => exact False.elim restorable
  | published phase => exact False.elim valid
  | cleanupExit phase own =>
    rcases permitted with ⟨value, selected, good⟩ | ⟨cause, selected, good⟩
    · exact completed phase own _ owner good
    · exact completed phase own _ owner good
  | attempt before entered own =>
    rcases permitted with ⟨value, selected, good⟩ | ⟨cause, good⟩
    · exact completed entered own _ owner good
    · rcases good with ⟨selected, good⟩ | ⟨beforeHeap, clean⟩
      · exact completed entered own _ owner good
      · have actualCount := (fields before beforeHeap).1
        change before.count + 1 = entered.count at valid
        change entered.count = context.entered.count at owner
        omega

end Test.Dogfood.Proofs.HostTimeoutNumberMaskPermission
