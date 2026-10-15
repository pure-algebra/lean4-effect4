import Test.Dogfood.Proofs.HostTimeoutNumberMaskPermission
import Effect4.Laws.Machine.AnswerFlowFamilyPop
import Test.Dogfood.Proofs.HostTimeoutNumberPhaseFinalizer

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Question: both Timeout endpoint histories retain actual protected cleanup custody through saved value returns.
Consumer: the pending whole-fiber native producer and its joined numeric command history.
Reach: one actual entered heap, owner-anchored uniform path, and permitted incoming value.
Limit: this relative fact supplies no whole-machine history or host failure-origin certificate.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.HostTimeoutNumberPopAuthority
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberPhaseFlow

/-- A hook raises a masked fiber's flag only at the actual restoring-mask instruction. -/
theorem ensure_raises (head : NCode) (scratch : HostTimeoutFrames.NativeFrame)
    (before : scratch.interruptible = false)
    (after : (head.ensure scratch).1.interruptible = true) :
    head = .setInterruptible true := by
  fun_cases Prim.ensure head scratch <;>
    aesop (add norm simp [Prim.ensure]) (rule_sets := [Effect4.CodeClosure])

/-- Actual selected hooks preserve the early-class permission required by finalizer custody. -/
theorem ensure_permitted (context : HostTimeoutNumberConfiguration.CountContext) (state : Stores)
    (input middle output : Kind) (head : NCode) (rest : List NCode)
    (scratch : HostTimeoutFrames.NativeFrame)
    (heap : At context.entered state)
    (edge : HostTimeoutNumberUniform.Edge state input middle head)
    (path : Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge state) middle output rest)
    (owner : output.ownerCount = context.entered.count) (valid : output.Valid)
    (permitted : (∃ value, ValueAt state input value) ∨ ∃ cause, CauseAt state input cause)
    (authority : scratch.interruptible = true → input.grade ≤ 1)
    (unmasked : (head.ensure scratch).1.interruptible = true) : middle.grade ≤ 1 := by
  have anchors := HostTimeoutNumberUniform.anchors state input output (head :: rest) (.cons edge path)
  have early : input.grade ≤ 1 := by
    cases flag : scratch.interruptible with
    | true => exact authority flag
    | false =>
      have actual := ensure_raises head scratch flag unmasked
      have restorable := edge.restores actual
      by_cases low : input.grade ≤ 1
      · exact low
      · have high : 1 < input.grade := by omega
        exact False.elim (HostTimeoutNumberMaskPermission.restoring_late_ne_entered context state input
          (anchors.1.trans owner) (anchors.2 valid) restorable high permitted heap)
  by_cases low : middle.grade ≤ 1
  · exact low
  · have high : 1 < middle.grade := by omega
    obtain ⟨body, point, actual⟩ := edge.crossing early high
    rw [actual, Effect4.Machine.ProtectedFinalizer.ensure_masked] at unmasked
    cases unmasked

/-- Draining the actual pushed restoring mask retains the same early-class authority. -/
theorem drain_permitted (context : HostTimeoutNumberConfiguration.CountContext) (state : Stores)
    (input middle output : Kind) (head : NCode) (rest : List NCode)
    (scratch : HostTimeoutFrames.NativeFrame) (demand : Effect4.Arm) (skip : Bool)
    (heap : At context.entered state)
    (edge : HostTimeoutNumberUniform.Edge state input middle head)
    (path : Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge state) middle output rest)
    (owner : output.ownerCount = context.entered.count) (valid : output.Valid)
    (empty : scratch.stack = [])
    (permitted : (∃ value, ValueAt state input value) ∨ ∃ cause, CauseAt state input cause)
    (nextPermitted : (∃ value, ValueAt state middle value) ∨ ∃ cause, CauseAt state middle cause)
    (authority : scratch.interruptible = true → input.grade ≤ 1)
    (unmasked : (FrameFiber.passPushed demand skip (head.ensure scratch).1).fiber.interruptible = true) :
    middle.grade ≤ 1 := by
  rcases FrameFiber.ensure_stack_cases head scratch with kept | ⟨pushed, _, _⟩
  · rw [FrameFiber.passPushed_nil demand skip _ (kept.trans empty)] at unmasked
    exact ensure_permitted context state input middle output head rest scratch heap edge path owner valid
      permitted authority unmasked
  · have anchors := HostTimeoutNumberUniform.anchors state middle output rest path
    by_cases low : middle.grade ≤ 1
    · exact low
    · have high : 1 < middle.grade := by omega
      exact False.elim (HostTimeoutNumberMaskPermission.restoring_late_ne_entered context state middle
        (anchors.1.trans owner) (anchors.2 valid) (edge.generated scratch pushed) high
        nextPermitted heap)

/-- The selected value callback retains its actual class and runtime mask authority together. -/
theorem selected_value_early (view : HostTimeoutFlow.View)
    (context : HostTimeoutNumberConfiguration.CountContext) (state : Stores)
    (input output : Kind) (frame : HostTimeoutFrames.NativeFrame) (value : Val) (selected : NCode)
    (heap : At context.entered state)
    (owner : output.ownerCount = context.entered.count) (valid : output.Valid)
    (good : ValueAt state input value)
    (authority : frame.interruptible = true → input.grade ≤ 1)
    (path : Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge state) input output frame.stack)
    (found : (frame.getCont .contA false).answer = .frame selected) :
    ∃ incoming middle, ValueAt state incoming value ∧
      HostTimeoutNumberUniform.Edge state incoming middle selected ∧
      Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge state) middle output
        (frame.getCont .contA false).fiber.stack ∧
      ((frame.getCont .contA false).fiber.interruptible = true → middle.grade ≤ 1) := by
  exact AnswerFlow.Contextual.Hooked.getCont_value_selected_with_authority
    (model view) (HostTimeoutFlow.interpreter view).toPrimInterp HostTimeoutNumberUniform.Edge
    HostTimeoutNumberPhaseFinalizer.Allowed
    (AnswerFlow.SavedFamily.contextual (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
      HostTimeoutNumberUniform.Edge HostTimeoutNumberPhaseFinalizer.Allowed
      (HostTimeoutNumberUniform.family view))
    HostTimeoutNumberUniform.hook_mask
    (fun kind scratch => scratch.interruptible = true → kind.grade ≤ 1)
    (fun kind scratch => scratch.interruptible = true → kind.grade ≤ 1)
    state input output frame value selected
    (by
      intro incoming middle head rest scratch before after edge tail empty good nextGood early passed drained unmasked
      rw [FrameFiber.passPushed_fiber_cause] at unmasked
      exact drain_permitted context state incoming middle output head rest scratch .contA false heap edge tail owner valid
        empty (Or.inl ⟨value, good⟩) (Or.inl ⟨value, nextGood⟩) early unmasked)
    (by
      intro incoming middle rest scratch edge tail empty good early unmasked
      exact ensure_permitted context state incoming middle output selected rest scratch heap edge tail owner valid
        (Or.inl ⟨value, good⟩) early unmasked)
    good authority path found

/-- The actual selected callback preserves early permission at its new current code and saved path. -/
theorem resume_value_selected_early (view : HostTimeoutFlow.View)
    (context : HostTimeoutNumberConfiguration.CountContext) (state : Stores)
    (input output : Kind) (frame : HostTimeoutFrames.NativeFrame) (value : Val)
    (selected next : NCode) (pushed : List NCode) (provided : Option ExitV)
    (heap : At context.entered state)
    (owner : output.ownerCount = context.entered.count) (valid : output.Valid)
    (good : ValueAt state input value)
    (authority : frame.interruptible = true → input.grade ≤ 1)
    (path : Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge state) input output frame.stack)
    (found : (frame.getCont .contA false).answer = .frame selected)
    (supplied : ∀ incoming, ValueAt state incoming value → ∀ exit ∈ provided,
      AnswerFlow.ExitAt (model view) state incoming exit)
    (pure : AnswerFlow.programOf (model view) state selected (provided.getD (.success value)) = none)
    (evaluated : selected.armA (HostTimeoutFlow.interpreter view).toPrimInterp value provided = some (next, pushed)) :
    ∃ events current,
      frame.resumeValue (HostTimeoutFlow.interpreter view).toPrimInterp value provided =
        (.running {(frame.getCont .contA false).fiber with
          current := next
          stack := pushed ++ (frame.getCont .contA false).fiber.stack}, events) ∧
      CodeAt state current next ∧
      Effect4.Contracts.Path (HostTimeoutNumberUniform.Edge state) current output
        (pushed ++ (frame.getCont .contA false).fiber.stack) ∧
      ((frame.getCont .contA false).fiber.interruptible = true → current.grade ≤ 1) := by
  obtain ⟨incoming, middle, incomingGood, callback, suffix, early⟩ :=
    selected_value_early view context state input output frame value selected heap owner valid good authority path found
  have family := AnswerFlow.SavedFamily.contextual (model view) (HostTimeoutFlow.interpreter view).toPrimInterp
    HostTimeoutNumberUniform.Edge HostTimeoutNumberPhaseFinalizer.Allowed (HostTimeoutNumberUniform.family view)
  obtain ⟨current, code, callbackPath⟩ := family.answer state incoming middle selected callback state
    ((model view).future_refl state) value provided next pushed incomingGood
    (supplied incoming incomingGood) pure evaluated
  have order : current.grade ≤ middle.grade := Effect4.Contracts.Path.endpoints
    (fun first last : Kind => first.grade ≤ last.grade) (fun _ => Nat.le_refl _)
    (fun _ _ _ first second => Nat.le_trans first second)
    (fun _ _ _ edge => edge.ordered) callbackPath
  exact ⟨_, current, FrameFiber.resumeValue_frame (HostTimeoutFlow.interpreter view).toPrimInterp
    frame value provided selected next pushed found evaluated, code,
    Effect4.Contracts.Path.append callbackPath suffix, fun unmasked => Nat.le_trans order (early unmasked)⟩

end Test.Dogfood.Proofs.HostTimeoutNumberPopAuthority
