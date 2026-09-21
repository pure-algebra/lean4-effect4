import Effect4.Laws.Program.Typed.Residual

/-! Evaluate the proposed divergence: a preempted resume skip sanitizes the escaping cause.
`popR'` is `popR` with one changed branch. Two candidate sanitizers are compared on the
E4-SCHED-CE-006 state: replace by the recorded interrupt (the proposal) and Effect 3's
strip-then-combine (retains defects). Both are clean; only the second keeps a defect. -/
set_option autoImplicit false
namespace Probe.Divergence
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects Effect4.Program.Typed Effect4.Program.Typed.Contracts
abbrev TWorld := Effect4.Program.Typed.World

def cleanExit : ExitV → Bool
  | .success _ => true
  | .failure c => c.reasons.all fun r => r.tag != .fail

/-- Effect 3's `stripFailures`: keep defects and interrupts, drop every `Fail`. -/
def stripFail (c : CauseV) : CauseV := ⟨c.reasons.filter fun r => r.tag != .fail⟩

/-- The sanitized cause at a preempted skip: the original failure without its `Fail`
reasons, combined with the recorded interrupt. -/
def sanitize (cause ic : CauseV) : CauseV := Cause.combine (stripFail cause) ic

theorem sanitize_clean (cause ic : CauseV) (hic : ∀ r ∈ ic.reasons, r.tag ≠ .fail) :
    cleanExit (.failure (sanitize cause ic)) = true := by
  unfold cleanExit sanitize
  rw [List.all_eq_true]
  intro r hr
  rw [bne_iff_ne]
  rcases (Cause.mem_combine _ _ _).mp hr with h | h
  · exact bne_iff_ne.mp (List.mem_filter.mp h).2
  · exact hic r h

/-- `popR` with the divergent branch: a preempted skip passes the sanitized cause on. -/
def popR' (interp : RInterp) (ex : ExitV) : List ScopeFrame → RSaved → RSaved × Option ExitV
  | [], frame => ({ frame with stack := [] }, some ex)
  | slot :: rest, frame =>
    let frame := { frame with stack := rest }
    let failing := match ex with | .failure _ => true | _ => false
    match slot with
    | .restoreMask flag | .finalizerMask flag =>
      let frame := { frame with interruptible := flag }
      match frame.interruptedCause with
      | some cause =>
        if flag && !failing then ({ frame with current := .pure (.failure cause) }, none)
        else popR' interp ex rest frame
      | none => popR' interp ex rest frame
    | .resume kind next =>
      let flag := frame.interruptible
      let frame := match kind with
        | .onExit false => { frame with interruptible := false }
        | _ => frame
      if kind.hasExitArm ex && !(failing && frame.interruptible && frame.interruptedCause.isSome) then
        let frame := match kind with
          | .onExit _ => { frame with stack := .finalizerMask flag :: frame.stack }
          | _ => frame
        ({ frame with current := next ex }, none)
      else
        -- THE DIVERGENCE: a preempted skip of an arm that would have run
        let ex' := match ex, frame.interruptedCause with
          | .failure cause, some ic =>
            if kind.hasExitArm ex then .failure (sanitize cause ic) else ex
          | _, _ => ex
        popR' interp ex' rest frame
    | .answer next =>
      match next ex with
      | .pure ex' => popR' interp ex' rest frame
      | .vis (.inr (.unguard ex')) _ => popR' interp ex' rest frame
      | code => ({ frame with current := code }, none)
    | .asyncFinalizer name =>
      match ex with
      | .failure cause =>
        let stack := if frame.interruptible then .restoreMask true :: rest else rest
        let code := if cause.hasInterrupts then interp.cancelThenFail name cause else .pure ex
        ({ frame with current := code, stack, interruptible := false }, none)
      | .success _ =>
        if frame.interruptible && frame.interruptedCause.isSome then
          ({ frame with current := .pure (.failure frame.pendingCause) }, none)
        else popR' interp ex rest frame
    | .iter generator =>
      match ex with
      | .failure _ => popR' interp ex rest frame
      | .success v =>
        match (interp.iterNext generator v).2 with
        | .done result => ({ frame with current := .pure (.success result) }, none)
        | .halt cause => ({ frame with current := .pure (.failure cause) }, none)
        | .resume code next => ({ frame with current := code, stack := .iter next :: rest }, none)
    | .loop name cursor =>
      match ex with
      | .failure _ => popR' interp ex rest frame
      | .success v =>
        match interp.loopResume name cursor v with
        | .continue next body => ({ frame with current := body, stack := .loop name next :: rest }, none)
        | .finish code => ({ frame with current := code }, none)

def ic : CauseV := Cause.interrupt (some ⟨1⟩)
def failure : ExitV := .failure (Cause.fail (.tag 42))
def failureWithDefect : ExitV := .failure ⟨[.fail (.tag 42) .empty, .die (.user 3) .empty]⟩
def recovery (_ex : ExitV) : RProgram := .pure (.success (.nat 0))
def masked : RSaved :=
  ⟨.pure failure, [.restoreMask true, .resume .onFailure recovery], false, some ic, false⟩

/-- Today: the original Fail escapes. -/
theorem today (interp : RInterp) : (popR interp failure masked.stack masked).2 = some failure := rfl

/-- Diverged: the walk ends with the interrupt only. -/
theorem diverged (interp : RInterp) :
    (popR' interp failure masked.stack masked).2 = some (.failure ic) := rfl

/-- Diverged, with a defect in the original failure: the defect is retained, the Fail is not. -/
theorem diverged_keeps_defect (interp : RInterp) :
    (popR' interp failureWithDefect masked.stack masked).2 =
      some (.failure ⟨[.die (.user 3) .empty, .interrupt (some ⟨1⟩) .empty]⟩) := rfl

/-- The proposal's replace-by-interrupt would drop that defect. -/
theorem proposal_drops_defect :
    (Exit.failure ic : ExitV) ≠ Exit.failure ⟨[.die (.user 3) .empty, .interrupt (some ⟨1⟩) .empty]⟩ := by
  intro h; cases h

/-- The diverged result fits the catch's output type, at any world. -/
theorem diverged_fits (w : TWorld) : StrongExit w (EffTy.pure .nat) (.failure ic) := by
  refine ⟨rfl, (fun _ heq => nomatch heq), fun c heq => ?_⟩
  cases heq
  intro r hr
  change r ∈ [Reason.interrupt (some ⟨1⟩) ReasonAnnotations.empty] at hr
  simp only [List.mem_singleton] at hr
  subst hr
  trivial

#print axioms sanitize_clean
#print axioms diverged
#print axioms diverged_keeps_defect
#print axioms diverged_fits
end Probe.Divergence
