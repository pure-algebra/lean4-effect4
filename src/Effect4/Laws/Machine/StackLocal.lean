import Effect4.Laws.Machine.MaskBracket

/-!
# Laws.Machine.StackLocal — a step that goes on is the same step over more frames

`step_under` (`Laws/Machine/MaskBracket.lean`) states the frame rule of the frame machine for the
next fiber alone: a step that goes on keeps the frames under the region. A step's events reach the
fiber machine's trace too, so the fiber machine's frame rule needs the whole step. This module
states it:

* `resumeValue_under_pair`, `resumeCause_under_pair`: a resumption that goes on is the same
  resumption over more frames, with the same events;
* `step_under_pair`: a step that goes on is the same step over more frames, with the same events.

Placement (AGENTS.md, Trust):

- concept `scope-lifetime-finalization` (`docs/core/semantics.md` §2.3), the region bracket; the
  proposed registry claim `stack-local`, role invariant, whose evaluation half is
  `Laws/Program/StackLocal.lean`;
- reach: the polymorphic frame machine, at every interpreter, fiber and stack of frames under it;
- it states nothing of a step that finishes: there the pop answered nothing, and over more frames
  it goes on into them (`getCont_regionEnd`);
- consumer: the native evaluation's frame rule (`Program.StackLocal`), and through it the premise
  `inside` of `compiled_region_bracket` (R11).
-/

set_option autoImplicit false

namespace Effect4.FrameFiber

universe u v

variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- A value resumption that goes on is the same over more frames, events included. -/
@[semantics "scope-lifetime-finalization"]
theorem resumeValue_under_pair (interp : PrimInterp ν σ β ε δ ι α) (f : FrameFiber ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (value : β) (provided : Option (Exit β ε δ ι α))
    (next : FrameFiber ν σ β ε δ ι α) (events : List (FrameEvent ν σ β ε δ ι α))
    (running : f.resumeValue interp value provided = (FrameStep.running next, events)) :
    (f.under below).resumeValue interp value provided =
      (FrameStep.running (next.under below), events) := by
  cases answered : (f.getCont Arm.contA false).answer with
  | empty =>
    rw [resumeValue_empty interp f value provided answered] at running
    cases running
  | deferred c =>
    have kept := getCont_under_answered f below Arm.contA false none
      (by rw [answered]; exact fun h => nomatch h)
    rw [resumeValue_deferred interp f value provided c answered] at running
    cases running
    rw [resumeValue_deferred interp (f.under below) value provided c
      (by rw [kept]; exact answered), kept]
    rfl
  | replacement code =>
    have kept := getCont_under_answered f below Arm.contA false none
      (by rw [answered]; exact fun h => nomatch h)
    rw [resumeValue_replacement interp f value provided code answered] at running
    cases running
    rw [resumeValue_replacement interp (f.under below) value provided code
      (by rw [kept]; exact answered), kept]
    rfl
  | frame answering =>
    have kept := getCont_under_answered f below Arm.contA false none
      (by rw [answered]; exact fun h => nomatch h)
    cases arm : answering.armA interp value provided with
    | none =>
      simp only [resumeValue, answered, arm] at running
      cases running
    | some out =>
      obtain ⟨code, pushed⟩ := out
      rw [resumeValue_frame interp f value provided answering code pushed answered arm] at running
      cases running
      rw [resumeValue_frame interp (f.under below) value provided answering code pushed
        (by rw [kept]; exact answered) arm, kept]
      simp only [under, List.append_assoc]

/-- A cause resumption that goes on is the same over more frames, events included. -/
@[semantics "scope-lifetime-finalization"]
theorem resumeCause_under_pair (interp : PrimInterp ν σ β ε δ ι α) (f : FrameFiber ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (cause : Cause ε δ ι α)
    (provided : Option (Exit β ε δ ι α)) (next : FrameFiber ν σ β ε δ ι α)
    (events : List (FrameEvent ν σ β ε δ ι α))
    (running : f.resumeCause interp cause provided = (FrameStep.running next, events)) :
    (f.under below).resumeCause interp cause provided =
      (FrameStep.running (next.under below), events) := by
  cases answered : (f.getCont Arm.contE true (some cause)).answer with
  | empty =>
    rw [resumeCause_empty interp f cause provided answered] at running
    cases running
  | deferred c =>
    have kept := getCont_under_answered f below Arm.contE true (some cause)
      (by rw [answered]; exact fun h => nomatch h)
    rw [resumeCause_deferred interp f cause c provided answered] at running
    cases running
    rw [resumeCause_deferred interp (f.under below) cause c provided
      (by rw [kept]; exact answered), kept]
    rfl
  | replacement code =>
    have kept := getCont_under_answered f below Arm.contE true (some cause)
      (by rw [answered]; exact fun h => nomatch h)
    rw [resumeCause_replacement interp f cause provided code answered] at running
    cases running
    rw [resumeCause_replacement interp (f.under below) cause provided code
      (by rw [kept]; exact answered), kept]
    rfl
  | frame answering =>
    have kept := getCont_under_answered f below Arm.contE true (some cause)
      (by rw [answered]; exact fun h => nomatch h)
    cases arm : answering.armE interp
        ((f.getCont Arm.contE true (some cause)).carriedCause.getD cause)
        (provided.map (f.getCont Arm.contE true (some cause)).deliveredExit) with
    | none =>
      simp only [resumeCause, answered, arm] at running
      cases running
    | some out =>
      obtain ⟨code, pushed⟩ := out
      rw [resumeCause_frame interp f cause provided answering code pushed answered arm] at running
      cases running
      rw [resumeCause_frame interp (f.under below) cause provided answering code pushed
        (by rw [kept]; exact answered) (by rw [kept]; exact arm), kept]
      simp only [under, List.append_assoc, FramePop.deliveredExit]

/-- **A step that goes on is the same step over more frames, events included**: the frame rule of
the frame machine, as a pair. `step_under` is its first component. -/
@[semantics "scope-lifetime-finalization"]
theorem step_under_pair (interp : PrimInterp ν σ β ε δ ι α) (f : FrameFiber ν σ β ε δ ι α)
    (below : List (Prim ν σ β ε δ ι α)) (next : FrameFiber ν σ β ε δ ι α)
    (events : List (FrameEvent ν σ β ε δ ι α))
    (running : f.step interp = (FrameStep.running next, events)) :
    (f.under below).step interp = (FrameStep.running (next.under below), events) := by
  cases current : f.current with
  | success value =>
    simp only [step, current] at running
    simp only [step, under_current, current]
    exact resumeValue_under_pair interp f below _ _ next events running
  | failure cause =>
    simp only [step, current] at running
    simp only [step, under_current, current]
    exact resumeCause_under_pair interp f below _ _ next events running
  | sync thunk =>
    simp only [step, current] at running
    simp only [step, under_current, current]
    exact resumeValue_under_pair interp f below _ _ next events running
  | iterator generator cursor =>
    simp only [step, current] at running
    simp only [step, under_current, current]
    cases arm : (Prim.iterator generator cursor : Prim ν σ β ε δ ι α).armA interp cursor none with
    | none =>
      simp only [arm] at running ⊢
      cases running
      rfl
    | some out =>
      simp only [arm] at running ⊢
      cases running
      simp only [under, List.append_assoc]
  | whileLoop loop cursor =>
    simp only [step, current] at running
    simp only [step, under_current, current]
    cases entered : interp.loopEnter loop cursor with
    | «continue» cursor' body =>
      simp only [entered] at running ⊢
      cases running
      rfl
    | finish code =>
      simp only [entered] at running ⊢
      cases running
      rfl
  | _ =>
    simp only [step, current] at running
    simp only [step, under_current, current]
    cases running
    rfl

end Effect4.FrameFiber
