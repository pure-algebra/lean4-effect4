import Effect4.Laws.Program.Typed.Contracts

/-! Focused obstruction probe for the saved-stack interface at 641a0fea.
No assertion of reachability is made for the arbitrary saved state below. -/
set_option autoImplicit false
namespace FoundationsStackProbe
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Effect4.Program.Typed Effect4.Program.Typed.Contracts

/-- A handled Nat failure is removed from the result error column. -/
def beforeCatch : EffTy := ⟨.nat, .nat, Effect4.Machine.Env.Requirement.empty⟩
def afterCatch : EffTy := EffTy.pure .nat
def failure : ExitV := .failure (Cause.fail (.tag 0))
def recovery (_ex : ExitV) : RProgram := .pure (.success (.nat 0))

theorem failure_fits_before (w : Effect4.Program.Typed.World) : ExitFits w beforeCatch failure := rfl

theorem failure_does_not_fit_after (w : Effect4.Program.Typed.World) : ¬ ExitFits w afterCatch failure := by
  intro h
  change false = true at h
  exact Bool.noConfusion h

/-- Even the most permissive program relation cannot admit this handler: the obstruction
is the unconditional failure-passthrough premise, not the continuation's typing. -/
theorem landed_resume_rejects_catch
    (TypedProg : Effect4.Program.Typed.World → EffTy → RProgram → Prop) (hooks : FrameProtocols) (w : Effect4.Program.Typed.World) :
    ¬ FrameAccepts TypedProg hooks w beforeCatch afterCatch (.resume .onFailure recovery) := by
  intro h
  cases h with
  | resume kind next run skip =>
    exact failure_does_not_fit_after w
      (skip failure (failure_fits_before w) (Or.inr ⟨Cause.fail (.tag 0), rfl⟩))

/-- Positive control: unchanged error columns meet the landed skip premise. -/
theorem unchanged_type_is_admitted (hooks : FrameProtocols) (w : Effect4.Program.Typed.World) :
    FrameAccepts (fun _ _ _ => True) hooks w beforeCatch beforeCatch
      (.resume .onFailure recovery) :=
  .resume .onFailure recovery (fun _ _ _ => True.intro) (fun _ h _ => h)

def plainSaved : RSaved :=
  ⟨.pure failure, [.resume .onFailure recovery], true, none, false⟩

def interruptSaved : RSaved :=
  { plainSaved with interruptedCause := some (Cause.interrupt (some ⟨1⟩)) }

/-- With no pending interrupt the real evaluator executes the handler. -/
theorem handler_runs (interp : RInterp) :
    (popR interp failure plainSaved.stack plainSaved).1.current = recovery failure := rfl

/-- With a recorded interrupt the real evaluator skips the handler and returns the
original Nat failure. This arbitrary state is not claimed reachable. -/
theorem handler_skips_original_failure (interp : RInterp) :
    (popR interp failure interruptSaved.stack interruptSaved).2 = some failure := rfl

/-- The existing structural interrupt provenance does not exclude that state. -/
theorem interrupt_saved_has_provenance : InterruptProvenance interruptSaved := by
  constructor
  · intro cause h reason hmem
    change some (Cause.interrupt (some ⟨1⟩)) = some cause at h
    cases h
    change reason ∈ [Reason.interrupt (some ⟨1⟩) ReasonAnnotations.empty] at hmem
    simp only [List.mem_singleton] at hmem
    subst reason
    rfl
  · intro h
    change false = true at h
    exact Bool.noConfusion h

/-- A closing marker can discard a continuation of a different result type. -/
def markerPayload : ExitV := .success (.nat 0)
def markerCode : RProgram :=
  .vis (.inr (.unguard markerPayload)) (fun _ => .pure (.success (.bool true)))

/-- For every protocol that admits this marker, ordinary protocol typing admits the
program at Bool, regardless of its answer postcondition. This is not a claim that the
planned production protocol has been defined. -/
theorem marker_has_continuation_type
    (order : Effect4.Laws.Effects.WorldOrder Effect4.Program.Typed.World)
    (protocol : Effect4.Laws.Effects.Protocol Effect4.Program.Typed.World RSig) (w : Effect4.Program.Typed.World)
    (admitted : protocol.pre w (.inr (.unguard markerPayload))) :
    Effect4.Laws.Effects.Typed order protocol w
      (fun w' ex => ExitFits w' (EffTy.pure .bool) ex) markerCode :=
  .vis admitted (fun _ _ _ _ => .pure rfl)

/-- The payload itself does not have the continuation's result type. -/
theorem marker_payload_wrong (w : Effect4.Program.Typed.World) :
    ¬ ExitFits w (EffTy.pure .bool) markerPayload := by
  intro h
  change false = true at h
  exact Bool.noConfusion h

/-- The actual answer-slot evaluator delivers the payload, ignoring that continuation. -/
theorem answer_marker_discards_continuation (interp : RInterp) :
    (popR interp (.success .unit) [.answer (fun _ => markerCode)] plainSaved).2 =
      some markerPayload := rfl

#print axioms marker_has_continuation_type
#print axioms marker_payload_wrong
#print axioms answer_marker_discards_continuation
#print axioms failure_fits_before
#print axioms failure_does_not_fit_after
#print axioms landed_resume_rejects_catch
#print axioms unchanged_type_is_admitted
#print axioms handler_runs
#print axioms handler_skips_original_failure
#print axioms interrupt_saved_has_provenance
end FoundationsStackProbe
