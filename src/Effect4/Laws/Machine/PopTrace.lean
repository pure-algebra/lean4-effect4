import Effect4.Machine.Frames
import Effect4.Laws.Auto.RuleSets
import Effect4.Laws.Auto.Semantics

/-!
Concept: scope-lifetime-finalization R11 and reactive-scheduling R2.
Question: one actual continuation-pop specification replaces repeated saved-stack traversals.
Consumer: HostTimeoutFrames.pop_from and the labelled frame accounting instances.
Reach: the existing fused pop, its original frames, actual hook drains, and actual carried cause.
The proof-only trace distinguishes original consumed frames from hook-injected popped frames.
It establishes no callback admissibility, reached history, or runtime agreement.
-/
set_option autoImplicit false
namespace Effect4.Machine.PopTrace
open Effect4
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- A passed original frame either lacks an answer or discards it under the actual interrupt flag. -/
def Passes (demand : Arm) (skip : Bool) (frame : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (before after : Option (Cause ε δ ι α)) : Prop :=
  (frame.answerOf demand (frame.ensure fiber).2 = none ∧ after = before) ∨
    (∃ answer, frame.answerOf demand (frame.ensure fiber).2 = some answer ∧
      (skip && (frame.ensure fiber).1.interrupted) = true ∧
      after = FrameFiber.skippedCause demand frame (frame.ensure fiber).1 before)

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- An absent answer cannot declare the requested arm.
Consumers: the exact source and semantic saved-frame instances. -/
theorem answer_missing (frame : Prim ν σ β ε δ ι α) (demand : Arm)
    (replacement : Option (Prim ν σ β ε δ ι α))
    (missing : frame.answerOf demand replacement = none) : frame.hasArm demand = false := by
  unfold Prim.answerOf at missing
  cases replacement with
  | some _ => cases missing
  | none =>
    cases arm : frame.hasArm demand with
    | false => rfl
    | true => rw [arm] at missing; cases missing

/-- The actual hook drain empties a detached scratch stack.
Consumers: selected-frame source provenance and semantic saved-stack transport. -/
theorem drain_empty (demand : Arm) (skip : Bool) (code : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α)
    (empty : fiber.stack = []) :
    (FrameFiber.passPushed demand skip (code.ensure fiber).1).fiber.stack = [] := by
  rcases FrameFiber.ensure_stack_cases code fiber with kept | ⟨pushed, _, _⟩
  · rw [FrameFiber.passPushed_nil _ _ _ (kept.trans empty)]
    exact kept.trans empty
  · rw [FrameFiber.passPushed_fiber _ _ _ (.setInterruptible true) [] (by rw [pushed, empty])]
    exact Prim.ensure_setInterruptible_stack true _

/-- A mask injected by a hook cannot select a callback at an absent arm.
Consumers: selected-frame source provenance and semantic saved-stack transport. -/
theorem drain_not_frame (demand : Arm) (skip : Bool)
    (missing : (Prim.setInterruptible true : Prim ν σ β ε δ ι α).hasArm demand = false)
    (code selected : Prim ν σ β ε δ ι α)
    (fiber : FrameFiber ν σ β ε δ ι α) (empty : fiber.stack = []) :
    (FrameFiber.passPushed demand skip (code.ensure fiber).1).answer ≠ .frame selected := by
  rcases FrameFiber.ensure_stack_cases code fiber with kept | ⟨pushed, _, _⟩
  · rw [FrameFiber.passPushed_nil _ _ _ (kept.trans empty)]
    intro impossible; cases impossible
  · have shape : (code.ensure fiber).1.stack = [.setInterruptible true] := by rw [pushed, empty]
    rw [FrameFiber.passPushed_answer _ _ _ (.setInterruptible true) [] shape]
    intro selectedAnswer
    cases found : Prim.answerOf (.setInterruptible true) demand
        ((Prim.setInterruptible true).ensure {(code.ensure fiber).1 with stack := []}).2 with
    | none => rw [found] at selectedAnswer; cases selectedAnswer
    | some answer =>
      rw [found] at selectedAnswer
      dsimp only at selectedAnswer
      split at selectedAnswer
      · cases selectedAnswer
      have arm := Prim.answerOf_frame_eq (.setInterruptible true) selected demand _
        (found.trans (congrArg some selectedAnswer))
      rw [missing] at arm
      cases arm.2

/-- Each pair records one consumed original frame and the exact frames its hook drain pops. -/
inductive Trace (demand : Arm) (skip : Bool) :
    List (Prim ν σ β ε δ ι α) → FrameFiber ν σ β ε δ ι α → Option (Cause ε δ ι α) →
    List (Prim ν σ β ε δ ι α × List (Prim ν σ β ε δ ι α)) →
    List (Prim ν σ β ε δ ι α) → FramePop ν σ β ε δ ι α → Prop
  | nil (fiber : FrameFiber ν σ β ε δ ι α) (cause : Option (Cause ε δ ι α)) :
      Trace demand skip [] fiber cause [] [] ⟨.empty, [], [], fiber, cause⟩
  | selected (frame : Prim ν σ β ε δ ι α) (rest : List (Prim ν σ β ε δ ι α))
      (fiber : FrameFiber ν σ β ε δ ι α) (cause : Option (Cause ε δ ι α))
      (answer : ContAnswer ν σ β ε δ ι α)
      (chosen : frame.answerOf demand (frame.ensure fiber).2 = some answer)
      (kept : (skip && (frame.ensure fiber).1.interrupted) = false) :
      Trace demand skip (frame :: rest) fiber cause [(frame, [])] rest
        ⟨answer, [frame], frame.passEvents (frame.ensure fiber).2,
          {(frame.ensure fiber).1 with stack := (frame.ensure fiber).1.stack ++ rest}, cause⟩
  | continued (frame : Prim ν σ β ε δ ι α) (rest : List (Prim ν σ β ε δ ι α))
      (fiber : FrameFiber ν σ β ε δ ι α) (before after : Option (Cause ε δ ι α))
      (parts : List (Prim ν σ β ε δ ι α × List (Prim ν σ β ε δ ι α)))
      (suffix : List (Prim ν σ β ε δ ι α)) (tail : FramePop ν σ β ε δ ι α)
      (passed : Passes demand skip frame fiber before after)
      (empty : (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).answer = .empty)
      (next : Trace demand skip rest
        (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).fiber
        (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).carriedCause parts suffix tail) :
      Trace demand skip (frame :: rest) fiber before
        ((frame, (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).popped) :: parts) suffix
        (FrameFiber.passOn frame (frame.ensure fiber).2
          (FrameFiber.joinPushed demand skip (frame.ensure fiber).1 rest tail after))
  | hooked (frame : Prim ν σ β ε δ ι α) (rest : List (Prim ν σ β ε δ ι α))
      (fiber : FrameFiber ν σ β ε δ ι α) (before after : Option (Cause ε δ ι α))
      (tail : FramePop ν σ β ε δ ι α) (passed : Passes demand skip frame fiber before after)
      (answered : (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).answer ≠ .empty) :
      Trace demand skip (frame :: rest) fiber before
        [(frame, (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).popped)] rest
        (FrameFiber.passOn frame (frame.ensure fiber).2
          (FrameFiber.joinPushed demand skip (frame.ensure fiber).1 rest tail after))

/-- One classification of the real fused pop supplies all continuation and accounting instances. -/
theorem popFrom_spec (demand : Arm) (skip : Bool) (frames : List (Prim ν σ β ε δ ι α))
    (fiber : FrameFiber ν σ β ε δ ι α) (cause : Option (Cause ε δ ι α)) :
    ∃ parts suffix, Trace demand skip frames fiber cause parts suffix
      (FrameFiber.popFrom demand skip frames fiber cause) := by
  induction frames generalizing fiber cause with
  | nil => exact ⟨[], [], .nil fiber cause⟩
  | cons frame rest ih =>
    have pass (after : Option (Cause ε δ ι α)) (passed : Passes demand skip frame fiber cause after) :
        ∃ parts suffix, Trace demand skip (frame :: rest) fiber cause parts suffix
          (FrameFiber.passOn frame (frame.ensure fiber).2
            (FrameFiber.joinPushed demand skip (frame.ensure fiber).1 rest
              (FrameFiber.popFrom demand skip rest
                (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).fiber
                (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).carriedCause) after)) := by
      cases answer : (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).answer with
      | empty =>
        obtain ⟨parts, suffix, next⟩ := ih
          (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).fiber
          (FrameFiber.passPushed demand skip (frame.ensure fiber).1 after).carriedCause
        exact ⟨_, suffix, .continued frame rest fiber cause after parts suffix _ passed answer next⟩
      | frame selected => exact ⟨_, rest, .hooked frame rest fiber cause after _ passed (by rw [answer]; intro wrong; cases wrong)⟩
      | replacement code => exact ⟨_, rest, .hooked frame rest fiber cause after _ passed (by rw [answer]; intro wrong; cases wrong)⟩
      | deferred reason => exact ⟨_, rest, .hooked frame rest fiber cause after _ passed (by rw [answer]; intro wrong; cases wrong)⟩
    cases selected : frame.answerOf demand (frame.ensure fiber).2 with
    | none =>
      rw [FrameFiber.popFrom, selected]
      exact pass cause (.inl ⟨selected, rfl⟩)
    | some answer =>
      cases skipped : skip && (frame.ensure fiber).1.interrupted with
      | false =>
        rw [FrameFiber.popFrom, selected, skipped]
        exact ⟨_, rest, .selected frame rest fiber cause answer selected skipped⟩
      | true =>
        rw [FrameFiber.popFrom, selected, skipped]
        exact pass _ (.inr ⟨answer, selected, skipped, rfl⟩)

/-- The original consumed list is separate from its hook-drain contributions. -/
theorem Trace.original {demand : Arm} {skip : Bool} {frames : List (Prim ν σ β ε δ ι α)}
    {fiber : FrameFiber ν σ β ε δ ι α} {cause : Option (Cause ε δ ι α)}
    {parts : List (Prim ν σ β ε δ ι α × List (Prim ν σ β ε δ ι α))}
    {suffix : List (Prim ν σ β ε δ ι α)} {pop : FramePop ν σ β ε δ ι α}
    (trace : Trace demand skip frames fiber cause parts suffix pop) :
    frames = parts.map Prod.fst ++ suffix := by
  induction trace with
  | nil => rfl
  | selected => rfl
  | continued _ _ _ _ _ _ _ _ _ _ _ ih => simpa only [List.map_cons, List.cons_append] using congrArg (List.cons _) ih
  | hooked => rfl

/-- The actual popped frames interleave consumed originals and the frames their hooks pop. -/
theorem Trace.popped {demand : Arm} {skip : Bool} {frames : List (Prim ν σ β ε δ ι α)}
    {fiber : FrameFiber ν σ β ε δ ι α} {cause : Option (Cause ε δ ι α)}
    {parts : List (Prim ν σ β ε δ ι α × List (Prim ν σ β ε δ ι α))}
    {suffix : List (Prim ν σ β ε δ ι α)} {pop : FramePop ν σ β ε δ ι α}
    (trace : Trace demand skip frames fiber cause parts suffix pop) :
    pop.popped = parts.flatMap (fun part => part.1 :: part.2) := by
  induction trace with
  | nil => rfl
  | selected => rfl
  | continued _ _ _ _ _ _ _ _ _ empty _ ih =>
    simp only [FrameFiber.passOn, FrameFiber.joinPushed, empty, List.flatMap_cons, List.cons_append,
      ih]
  | hooked _ _ _ _ _ _ _ answered =>
    unfold FrameFiber.passOn FrameFiber.joinPushed
    split
    · rename_i empty; exact False.elim (answered empty)
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- Actual pop events record precisely the original and hook-drain frames in the trace.
Consumer: labelled frame accounting reads these events rather than an assumed original prefix. -/
theorem Trace.events {demand : Arm} {skip : Bool} {frames : List (Prim ν σ β ε δ ι α)}
    {fiber : FrameFiber ν σ β ε δ ι α} {cause : Option (Cause ε δ ι α)}
    {parts : List (Prim ν σ β ε δ ι α × List (Prim ν σ β ε δ ι α))}
    {suffix : List (Prim ν σ β ε δ ι α)} {pop : FramePop ν σ β ε δ ι α}
    (trace : Trace demand skip frames fiber cause parts suffix pop) :
    FrameEvent.poppedFrames pop.events = parts.flatMap (fun part => part.1 :: part.2) := by
  have append (left right : List (FrameEvent ν σ β ε δ ι α)) :
      FrameEvent.poppedFrames (left ++ right) =
        FrameEvent.poppedFrames left ++ FrameEvent.poppedFrames right :=
    List.filterMap_append
  have exactEvents : FrameEvent.poppedFrames pop.events = pop.popped := by
    induction trace with
    | nil => rfl
    | selected => exact FrameFiber.passEvents_poppedFrames _ _
    | continued _ _ _ _ _ _ _ _ _ empty _ ih =>
      simp only [FrameFiber.passOn, FrameFiber.joinPushed, empty]
      rw [append, FrameFiber.passEvents_poppedFrames, append, FrameFiber.passPushed_events_cause,
        ← FrameFiber.passPushed_popped_eq_events, ih, FrameFiber.passPushed_popped_cause]
      simp only [FrameFiber.passPushed_popped_cause, List.cons_append, List.nil_append]
    | hooked _ _ _ _ _ _ _ answered =>
      unfold FrameFiber.passOn FrameFiber.joinPushed
      split
      · rename_i empty; exact False.elim (answered empty)
      · rw [append, FrameFiber.passEvents_poppedFrames, FrameFiber.passPushed_events_cause,
          ← FrameFiber.passPushed_popped_eq_events, FrameFiber.passPushed_popped_cause]
        simp only [FrameFiber.passPushed_popped_cause, List.cons_append, List.nil_append]
  exact exactEvents.trans trace.popped

/-- The returned stack is the surviving hook scratch over the original unconsumed suffix. -/
theorem Trace.stack {demand : Arm} {skip : Bool} {frames : List (Prim ν σ β ε δ ι α)}
    {fiber : FrameFiber ν σ β ε δ ι α} {cause : Option (Cause ε δ ι α)}
    {parts : List (Prim ν σ β ε δ ι α × List (Prim ν σ β ε δ ι α))}
    {suffix : List (Prim ν σ β ε δ ι α)} {pop : FramePop ν σ β ε δ ι α}
    (trace : Trace demand skip frames fiber cause parts suffix pop) :
    ∃ hooks, pop.fiber.stack = hooks ++ suffix := by
  induction trace with
  | nil fiber cause => exact ⟨fiber.stack, (List.append_nil fiber.stack).symm⟩
  | selected => exact ⟨_, rfl⟩
  | continued _ _ _ _ _ _ _ _ _ empty _ ih =>
    simpa only [FrameFiber.passOn, FrameFiber.joinPushed, empty] using ih
  | hooked _ _ _ _ _ _ _ answered =>
    unfold FrameFiber.passOn FrameFiber.joinPushed
    split
    · rename_i empty; exact False.elim (answered empty)
    · exact ⟨_, rfl⟩

/-- At ordinary answer arms, a selected callback comes from the consumed original prefix.
A detached scratch stack excludes selecting a caller-owned scratch frame.
Consumer: the getCont source witness and semantic selected-callback instances. -/
theorem Trace.selected_original {demand : Arm} {skip : Bool} {frames : List (Prim ν σ β ε δ ι α)}
    {fiber : FrameFiber ν σ β ε δ ι α} {cause : Option (Cause ε δ ι α)}
    {parts : List (Prim ν σ β ε δ ι α × List (Prim ν σ β ε δ ι α))}
    {suffix : List (Prim ν σ β ε δ ι α)} {pop : FramePop ν σ β ε δ ι α}
    (trace : Trace demand skip frames fiber cause parts suffix pop)
    (normal : demand = .contA ∨ demand = .contE) (empty : fiber.stack = [])
    (selected : Prim ν σ β ε δ ι α) (found : pop.answer = .frame selected) :
    selected ∈ parts.map Prod.fst := by
  induction trace with
  | nil => cases found
  | selected head tail fiber cause answer chosen kept =>
    have source := Prim.answerOf_frame_eq head selected demand _ (chosen.trans (congrArg some found))
    rw [← source.1]
    exact List.mem_cons_self
  | continued head tail fiber before after parts suffix tailPop passed drained next ih =>
    simp only [FrameFiber.passOn, FrameFiber.joinPushed, drained] at found
    exact List.mem_cons_of_mem _ (ih (by rw [FrameFiber.passPushed_fiber_cause]; exact drain_empty demand skip head fiber empty) found)
  | hooked head tail fiber before after tailPop passed answered =>
    unfold FrameFiber.passOn FrameFiber.joinPushed at found
    split at found
    · rename_i drained; exact False.elim (answered drained)
    · rw [FrameFiber.passPushed_answer_cause] at found
      have missing : (Prim.setInterruptible true : Prim ν σ β ε δ ι α).hasArm demand = false := by
        rcases normal with rfl | rfl <;> rfl
      exact False.elim (drain_not_frame demand skip missing head selected fiber empty found)

/-- A deferred interrupt pops no frame; every other actual getCont has one shared pop trace.
The trace supplies original-prefix, hook, suffix and actual-event accounting consumers. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem getCont_spec (fiber : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool)
    (cause : Option (Cause ε δ ι α)) :
    ((fiber.deferredInterrupt && !skip) = true ∧
      fiber.getCont demand skip cause =
        ⟨.deferred fiber.pendingCause, [], [.deferred fiber.pendingCause],
          {fiber with deferredInterrupt := false}, cause⟩) ∨
    ((fiber.deferredInterrupt && !skip) = false ∧ ∃ parts suffix, Trace demand skip fiber.stack
      {fiber with stack := [], deferredInterrupt := false} cause parts suffix
        (fiber.getCont demand skip cause) ∧
      ∀ selected, (demand = .contA ∨ demand = .contE) →
        (fiber.getCont demand skip cause).answer = .frame selected → selected ∈ parts.map Prod.fst) := by
  unfold FrameFiber.getCont
  split
  · rename_i deferred; exact .inl ⟨deferred, rfl⟩
  · rename_i ordinary
    obtain ⟨parts, suffix, trace⟩ := popFrom_spec demand skip fiber.stack
      {fiber with stack := [], deferredInterrupt := false} cause
    exact .inr ⟨Bool.eq_false_iff.mpr ordinary, parts, suffix, trace,
      fun selected normal found => trace.selected_original normal rfl selected found⟩

end Effect4.Machine.PopTrace
