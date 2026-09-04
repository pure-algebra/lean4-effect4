import Effect4.Machine.Frames

/-!
# Live-stack boundary witnesses

These attacks use the existing primitive, cause, fiber, answer and event
carriers. They do not import the new traversal and stay executable while its
contract is red. `E4-RUN-CE-022` attacks erased observations;
`E4-RUN-CE-023` attacks a stale interruption decision and identifies the
legacy deferred-answer boundary; `E4-RUN-CE-024` records why the current
primitive profile cannot itself witness the source's AsyncFinalizer defect.
No asynchronous primitive or second frame machine is introduced here.
-/

set_option autoImplicit false

namespace Test.Counterexamples.Runtime.LiveStack
open Effect4

private abbrev P := Prim Nat Nat Nat Nat Nat Nat Nat
private abbrev F := FrameFiber Nat Nat Nat Nat Nat Nat Nat
private abbrev C := Cause Nat Nat Nat Nat

private def notes : ReasonAnnotations Nat :=
  ⟨[("z", 17), ("a", 23)], by decide⟩

private def richCause : C :=
  ⟨[.fail 41 notes, .interrupt (some 53) .empty, .fail 41 notes]⟩

private def strippedCause : C :=
  ⟨[.fail 41 .empty, .interrupt (some 53) .empty, .fail 41 .empty]⟩

private def current : P := .onSuccess (.success 101) 107
private def handler : P := .onFailure (.failure richCause) 109
private def finalizer : P := .onExit (.success 113) 127 false

private def payloadFiber : F :=
  ⟨current, [.onSuccess (.failure richCause) 131, handler], false,
    some richCause, false⟩

/-- E4-RUN-CE-022: equal answering-arm shapes do not identify full frames. -/
theorem arm_shape_does_not_identify_payload :
    (Prim.onSuccess (.success 1) 7 : P).arms =
      (Prim.onSuccess (.success 2) 11 : P).arms ∧
    (FrameFiber.getCont
      (⟨current, [.onSuccess (.success 1) 7], false, none, false⟩ : F) .contA false).answer ≠
      (FrameFiber.getCont
        (⟨current, [.onSuccess (.success 2) 11], false, none, false⟩ : F) .contA false).answer := by
  decide

/-- E4-RUN-CE-022: an answer-only comparison cannot see a lost current program. -/
theorem answer_only_misses_current :
    let result := payloadFiber.getCont .contA false
    let erased := { result with fiber := { result.fiber with current := .success 0 } }
    result.answer = erased.answer ∧ result ≠ erased := by
  decide

/-- E4-RUN-CE-022: ordered, repeated reasons keep their ordered annotation maps. -/
theorem cause_tags_do_not_identify_annotations :
    richCause.reasons.map Reason.tag = strippedCause.reasons.map Reason.tag ∧
    richCause ≠ strippedCause ∧
    richCause.reasons.length = 3 ∧ notes.entries = [("z", 17), ("a", 23)] := by
  decide

private def maskThenHandler : F :=
  ⟨current, [.setInterruptible false, handler], true, some richCause, false⟩

/-- E4-RUN-CE-022: reversing a trace leaves its answer unchanged but changes the
promised observation. -/
theorem answer_only_misses_event_order :
    let result := maskThenHandler.getCont .contE true
    let reversed := { result with events := result.events.reverse }
    result.answer = reversed.answer ∧ result ≠ reversed := by
  decide

private def finalizing : F :=
  ⟨current, [finalizer, handler], true, some richCause, false⟩

private def staleFirstDecision (self : F) : ContAnswer Nat Nat Nat Nat Nat Nat Nat :=
  if self.interrupted then .empty else (self.getCont .contE false).answer

/-- E4-RUN-CE-023: the finalizer's hook changes the interruption condition before
the answering frame can be discarded. -/
theorem post_hook_mask_stops_discard :
    finalizing.interrupted = true ∧
    (finalizer.ensure { finalizing with stack := [handler] }).fst.interrupted = false ∧
    (finalizing.getCont .contE true).answer = .frame finalizer ∧
    staleFirstDecision finalizing = .empty := by
  decide

/-- E4-RUN-CE-023 positive control: the deliberately wrong decision agrees when
there is no pending interruption. -/
theorem stale_decision_positive_control :
    staleFirstDecision { finalizing with interruptedCause := none } =
      ({ finalizing with interruptedCause := none }.getCont .contE true).answer := by
  decide

private def maskedDeferred : F :=
  ⟨current, [handler], false, some richCause, true⟩

/-- E4-RUN-CE-023: the inner deferred-first call and legacy fused failure call
are different on a masked state. This is a Lean compatibility boundary, not
a proof that this source state is reachable. -/
theorem masked_deferred_distinguishes_inner_and_legacy :
    (maskedDeferred.getCont .contE false).answer = .deferred richCause ∧
    (maskedDeferred.getCont .contE false).popped = [] ∧
    (maskedDeferred.getCont .contE true).answer = .frame handler ∧
    (maskedDeferred.getCont .contE true).popped = [handler] := by
  decide

/-- E4-RUN-CE-023: even an unmasked pending interruption does not justify
equating the full chronological trace of an observed inner deferred answer
with the old fused traversal's trace. -/
theorem legacy_discards_deferred_event :
    let self := { maskThenHandler with deferredInterrupt := true }
    (self.getCont .contE false).events = [.deferred richCause] ∧
    FrameEvent.deferred richCause ∉ (self.getCont .contE true).events := by
  decide

/-- E4-RUN-CE-024, re-read after the run-loop packet made `AsyncFinalizer` a
constructor: for every *other* constructor, a hook cannot push while failing to
answer the requested arm. `AsyncFinalizer` is exactly the additional shape the row
named, and it is now reachable (`asyncFinalizer_pushes_without_answering` below),
which is why the pop loop had to be unfused (`FrameFiber.popFrom_asyncFinalizer_pops_its_push`). -/
theorem current_profile_no_answer_keeps_stack
    {ν σ ε δ ι α : Type} {β : Type}
    (frame : Prim ν σ β ε δ ι α) (demand : Arm)
    (fiber : FrameFiber ν σ β ε δ ι α)
    (notAsync : ∀ onInterrupt, frame ≠ Prim.asyncFinalizer onInterrupt)
    (missing : Prim.answerOf frame demand (frame.ensure fiber).snd = none) :
    (frame.ensure fiber).fst.stack = fiber.stack := by
  cases frame <;> try rfl
  case onExit body name flag =>
    cases demand <;> cases mask : fiber.interruptible <;> cases flag <;>
      simp [Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, mask] at missing
  case setInterruptible flag =>
    cases cause : fiber.interruptedCause <;> cases flag <;> simp [Prim.ensure, cause]
  case asyncFinalizer onInterrupt =>
    exact absurd rfl (notAsync onInterrupt)

/-- E4-RUN-CE-024, the positive half: on an interruptible fiber `AsyncFinalizer`
answers no `contA` and its hook pushes the restoring frame anyway. -/
theorem asyncFinalizer_pushes_without_answering
    {ν σ ε δ ι α : Type} {β : Type}
    (onInterrupt : ν) (fiber : FrameFiber ν σ β ε δ ι α)
    (interruptible : fiber.interruptible = true) :
    Prim.answerOf (Prim.asyncFinalizer onInterrupt) Arm.contA
        ((Prim.asyncFinalizer onInterrupt : Prim ν σ β ε δ ι α).ensure fiber).snd = none ∧
      ((Prim.asyncFinalizer onInterrupt : Prim ν σ β ε δ ι α).ensure fiber).fst.stack =
        Prim.setInterruptible true :: fiber.stack := by
  constructor
  · simp [Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, interruptible]
  · simp [Prim.ensure, interruptible]

#print axioms arm_shape_does_not_identify_payload
#print axioms answer_only_misses_current
#print axioms cause_tags_do_not_identify_annotations
#print axioms answer_only_misses_event_order
#print axioms post_hook_mask_stops_discard
#print axioms stale_decision_positive_control
#print axioms masked_deferred_distinguishes_inner_and_legacy
#print axioms legacy_discards_deferred_event
#print axioms current_profile_no_answer_keeps_stack
#print axioms asyncFinalizer_pushes_without_answering

end Test.Counterexamples.Runtime.LiveStack
