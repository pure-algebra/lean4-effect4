import Test.Dogfood.Proofs.HostRouting

/-!
# The routing continuation's interruption boundary

Concept: translation-simulation R6, serving `recorded-call-tree-prefix`.
The reader applies the existing interruption rule to the routing program's actual saved frames.
It supplies the interrupted branch of the planned native request-position invariant.
The control retains the mask boundary of `E4-RUN-CE-012`.
These conditional frame facts do not establish the whole reached-machine invariant.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.RoutingInterrupt
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Agreement
open Test.Dogfood.Proofs.HostRouting

/-- The actual routing continuation contains no frame that changes interruption handling. -/
theorem routing_no_hook : ∀ frame ∈ K, frame.hasArm .contAll = false := by
  intro frame member
  simp only [K, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- The actual routing continuation runs no callback when interruption skips its handlers. -/
theorem routing_interrupted (id : Nat) (idText : String) (self : NFiber)
    (stack : self.stack = K) (enabled : self.interruptible = true)
    (pending : CauseV) (recorded : self.interruptedCause = some pending)
    (cause : CauseV) (provided : Option ExitV) :
    ∃ exit, (self.resumeCause (interpOf (routeProg "secret" id idText)
      (Test.Dogfood.Scenario.Routing.request "secret" id idText).table).toPrimInterp
      cause provided).1 = .finished exit := by
  have noHook : ∀ frame ∈ self.stack, frame.hasArm .contAll = false := by
    rw [stack]
    exact routing_no_hook
  have empty := self.interrupt_skips_every_handler .contE pending enabled recorded noHook
  have carried : (self.getCont .contE true (some cause)).answer = .empty := by
    rw [FrameFiber.getCont_answer_cause]
    exact empty
  exact ⟨_, congrArg Prod.fst (self.resumeCause_empty _ cause provided carried)⟩

/-- An uninterruptible mask invalidates the skip premise and permits the enclosed handler. -/
example :
    let cause : CauseV := Cause.interrupt none
    let frame : NFiber :=
      { current := .failure cause
        stack := [.setInterruptible false, .onFailure (.success .unit) (.constant .unit)]
        interruptible := true
        interruptedCause := some cause
        deferredInterrupt := false }
    (frame.resumeCause (interpOf (routeProg "secret" 2 "2")).toPrimInterp cause none).1 =
      .running { frame with current := .success .unit, stack := [], interruptible := false } := by
  dsimp only
  kernel_rfl

end Test.Dogfood.Scenario.RoutingInterrupt
