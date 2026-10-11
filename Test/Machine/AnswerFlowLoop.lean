import Effect4.Laws.Machine.AnswerFlow
import Effect4.Laws.Machine.PopTraceFamily
import Effect4.Laws.Program.Typed.Contracts

/-!
Concept: residual-program-typing and scope-lifetime-finalization, R4/R11.
Question: can the shared saved-frame connector express partial correctness for a continuing loop?
Consumer: the proposed one-step contract-family seam for the unchanged Timeout saved-source family.
Control: an actual unit-valued primitive loop resaves exactly itself on every answer.
This proves a limitation of the inductive contract, not failure of the machine or of Timeout.
-/
set_option autoImplicit false
namespace Test.Machine.AnswerFlowLoop
open Effect4 Effect4.Machine Effect4.Machine.AnswerFlow
abbrev Code := Prim Unit Unit Unit Unit Unit Unit Unit
private def interp : PrimInterp Unit Unit Unit Unit Unit Unit Unit where
  contA _ _ := .success ()
  contE _ cause := .failure cause
  syncValue _ := ()
  suspendBody _ := .success ()
  finalizerExit _ _ := .success ()
  reifyExit _ := ()
  iterNext _ _ := ([], .done ())
  loopEnter _ cursor := .continue cursor (.success ())
  loopResume _ cursor _ := .continue cursor (.success ())
  notImplemented := ()
  cancelThenFail _ cause := .failure cause
private def model : Model (ν := Unit) (σ := Unit) (β := Unit)
    (ε := Unit) (δ := Unit) (ι := Unit) (α := Unit) Unit Unit where
  future _ _ := True
  future_refl _ := trivial
  future_trans _ _ _ _ _ := trivial
  value _ _ _ := True
  cause _ _ _ := True
  code _ _ _ := True
  finalizer _ _ _ := none
  success _ _ _ _ := trivial
  failure _ _ _ _ := trivial
private def loop : Code := .whileLoop () ()

-- Actual one-step behaviour: the answer runs the body and resaves the same loop.
#guard loop.armA interp () none = some (.success (), [loop])

/-- No inductive saved contract admits this safe, forever-resuming loop. -/
theorem not_saved (world input output : Unit) : ¬ SavedAt model interp world input output loop := by
  intro saved
  have excluded := SavedAt.rec
    (motive_1 := fun _ _ _ frame _ => frame ≠ loop)
    (motive_2 := fun _ _ _ frames _ => loop ∉ frames)
    (motive_3 := fun _ _ _ pushed _ => loop ∉ pushed)
    (mk := by
      intro world input output frame skip skipCause answer cause program discard answerIH causeIH equal
      subst frame
      have absent := answerIH world trivial () none (.success ()) [loop] trivial
        (by intro exit member; cases member) rfl rfl
      exact absent (List.mem_cons_self))
    (nil := fun _ _ => List.not_mem_nil)
    (cons := by
      intro world input middle output frame rest head tail headIH tailIH member
      rcases List.mem_cons.mp member with equal | member
      · exact headIH equal.symm
      · exact tailIH member)
    (fun _ _ _ _ _ _ _ ih => ih) saved
  exact excluded rfl
/-- A one-step family asks for preserved answers and a family member at each actual pushed frame.
It does not embed another proof of this closure into the saved frame predicate. -/
def StepClosed (family : Code → Prop) : Prop :=
  ∀ frame, family frame → ∀ value provided next pushed,
    frame.armA interp value provided = some (next, pushed) →
    next = .success () ∧ ∀ saved ∈ pushed, family saved

/-- The actual loop is a closed family despite the inductive connector's refusal. -/
theorem loop_step_closed : StepClosed (fun frame => frame = loop) := by
  intro frame same value provided next pushed answered
  subst frame
  have actual : loop.armA interp value provided = some (.success (), [loop]) := rfl
  have result := Option.some.inj (actual.symm.trans answered)
  cases result
  exact ⟨rfl, fun saved member => (List.mem_singleton.mp member)⟩

/-- The external loop family consumes the shared native pop transport.
The selected frame retains the exact loop witness without an inductive SavedAt proof. -/
theorem loop_pop (fiber : FrameFiber Unit Unit Unit Unit Unit Unit Unit)
    (scratch : fiber.stack = []) :
    ∀ selected, (FrameFiber.popFrom .contA false [loop] fiber).answer = .frame selected → selected = loop := by
  have family : PopTrace.Family .contA false (fun (_ _ : Unit) frame => frame = loop)
      (fun fiber => fiber.stack = [])
      (fun _ _ _ pop => ∀ selected, pop.answer = .frame selected → selected = loop) := by
    constructor
    · intro kind fiber cause empty selected found
      cases found
    · intro input middle output frame rest fiber cause answer saved path empty chosen kept selected found
      have shape := Prim.answerOf_frame_eq frame selected .contA _ (chosen.trans (congrArg some found))
      exact shape.1.trans saved
    · intro input middle frame fiber after saved empty
      rw [FrameFiber.passPushed_fiber_cause]
      exact PopTrace.drain_empty .contA false frame fiber empty
    · intro input middle output frame rest fiber before after tail saved path empty passed drained next
      rcases passed with ⟨absent, _⟩ | ⟨answer, chosen, skipped, _⟩
      · have missing := PopTrace.answer_missing frame .contA _ absent
        rw [saved] at missing
        cases missing
      · cases skipped
    · intro input middle output frame rest fiber before after tail saved path empty passed answered selected found
      unfold FrameFiber.passOn FrameFiber.joinPushed at found
      split at found
      · rename_i drained; exact False.elim (answered drained)
      · rw [FrameFiber.passPushed_answer_cause] at found
        exact False.elim (PopTrace.drain_not_frame .contA false rfl frame selected fiber empty found)
  exact family.popFrom () () [loop] fiber none (.cons rfl (.nil ())) scratch

private def loopStep (family : Unit → Prop) (cursor : Unit) : Prop :=
  ∀ value, match interp.loopResume () cursor value with
    | .continue next body => body = .success () ∧ family next
    | .finish body => body = .success ()

/-- The existing greatest-invariant carrier admits the actual forever-resuming loop.
This is partial correctness of each resume, with no termination or scheduling claim. -/
theorem loop_protocol : Effect4.Program.Typed.Contracts.Greatest loopStep () := by
  apply Effect4.Program.Typed.Contracts.Greatest.coind (I := fun _ => True)
  · intro cursor _ value
    exact ⟨rfl, trivial⟩
  · trivial

end Test.Machine.AnswerFlowLoop
