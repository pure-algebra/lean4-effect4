import Effect4.Laws.Program.Typed.Assembly

/-! H2 part-one controls for shared exit exclusion and buffered race failures.
badName and notImplemented are refused at typed exit boundaries, while ordinary defects,
interruptions, and missingService remain admitted. Since decisions row 152 the exclusion is also
part of membership at an exit type (`Fits`' `exitOf` arm reads `ShapeFree`), so base exit
membership refuses them too; the earlier base judgment is kept below as history over a local
copy of its `exitOf` arm (`oldExitFits`). Historical predicates below retain negative evidence
and are not current admission rules. -/
set_option autoImplicit false
namespace Test.Program.H2PartOne
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

/-- History: membership at `Exit<a, e>` before decisions row 152, a local copy of `Fits`' old
`exitOf` arm (the components read the current `Fits`): the encoded cause's failures fit the
error column, and nothing else is asked of it. -/
def oldExitFits (w : W) (v : Val) (a e : Ty) : Prop :=
  match v with
  | Val.exitOk x => Fits w x a
  | Value.exitErr written =>
    match causeImage.ofVal written with
    | some c => CauseFits (fun x => Fits w x e) c
    | none => False
  | _ => False

/-- History (red against the current judgment): the old base membership admitted a reified
`die badName` at every exit type. -/
theorem old_base_badName_fits (w : W) (ty : EffTy) :
    oldExitFits w (reifyExitVal (.failure (Cause.die .badName))) ty.answer ty.error := by
  show (match causeImage.ofVal (causeImage.toVal (Cause.die .badName)) with
    | some c => CauseFits (fun x => Fits w x ty.error) c
    | none => False)
  rw [Store.Image.ofVal_toVal]
  exact fitsCause_of_clean w ty.error _ rfl

/-- The flip (decisions row 152): base exit membership refuses `die badName` at every type. -/
theorem base_badName_refused (w : W) (ty : EffTy) :
    ¬ FitsExit w ty (.failure (Cause.die .badName)) := fun h =>
  (fitsExit_failure_shape h (.die .badName .empty) (List.mem_singleton_self _)).1 rfl

/-- The flip for `notImplemented`. -/
theorem base_notImplemented_refused (w : W) (ty : EffTy) :
    ¬ FitsExit w ty (.failure (Cause.die .notImplemented)) := fun h =>
  (fitsExit_failure_shape h (.die .notImplemented .empty) (List.mem_singleton_self _)).2 rfl

theorem clean_still_allows_badName :
    cleanExit (.failure (Cause.die .badName)) = true := rfl

theorem badName_refused (w : W) (ty : EffTy) :
    ¬ ExitOk w ty (.failure (Cause.die .badName)) := by
  intro typed
  have excluded := typed.2 (.die .badName .empty) (List.mem_singleton_self _)
  exact excluded.1 rfl

theorem notImplemented_refused (w : W) (ty : EffTy) :
    ¬ ExitOk w ty (.failure (Cause.die .notImplemented)) := by
  intro typed
  have excluded := typed.2 (.die .notImplemented .empty) (List.mem_singleton_self _)
  exact excluded.2 rfl

theorem bad_current_code_refused (root : ProgramSource) (w : W) (ty : EffTy) :
    ¬ TypedProg root w ty (.pure (.failure (Cause.die .badName))) :=
  fun typed => badName_refused w ty (TypedProg.pure_inv typed)

theorem notImplemented_current_code_refused (root : ProgramSource) (w : W) (ty : EffTy) :
    ¬ TypedProg root w ty (.pure (.failure (Cause.die .notImplemented))) :=
  fun typed => notImplemented_refused w ty (TypedProg.pure_inv typed)

/-- The defect clause is finite and independent of requirement rows in part one. -/
theorem ordinary_die_shape (ty : EffTy) (defect : Defect)
    (notBadName : defect ≠ .badName) (implemented : defect ≠ .notImplemented) :
    NoShapeDefect ty (.failure (Cause.die defect)) := by
  intro reason member
  simp only [Cause.die_reasons, List.mem_singleton] at member
  subst member
  exact ⟨notBadName, implemented⟩

theorem user_die_admitted (w : W) (ty : EffTy) (payload : Nat) :
    ExitOk w ty (.failure (Cause.die (.user payload))) :=
  strongExit_of_clean w ty _ rfl
    (ordinary_die_shape ty (.user payload) (by intro h; cases h) (by intro h; cases h))

theorem user_current_code_admitted (root : ProgramSource) (w : W) (ty : EffTy) (payload : Nat) :
    TypedProg root w ty (.pure (.failure (Cause.die (.user payload)))) :=
  TypedProg.pure (user_die_admitted w ty payload)

theorem missingService_admitted_at_any_type (w : W) (ty : EffTy) :
    ExitOk w ty (.failure (Cause.die .missingService)) :=
  strongExit_of_clean w ty _ rfl
    (ordinary_die_shape ty .missingService (by intro h; cases h) (by intro h; cases h))

theorem missingService_empty_admitted (w : W) :
    ExitOk w (EffTy.pure .unit) (.failure (Cause.die .missingService)) :=
  missingService_admitted_at_any_type w _

theorem missingService_nonempty_admitted (w : W) :
    ExitOk w ⟨.unit, .never, Env.Requirement.single nativeScopeKey⟩
      (.failure (Cause.die .missingService)) := missingService_admitted_at_any_type w _

theorem missingService_current_code_admitted (root : ProgramSource) (w : W) (ty : EffTy) :
    TypedProg root w ty (.pure (.failure (Cause.die .missingService))) :=
  TypedProg.pure (missingService_admitted_at_any_type w ty)

#print axioms old_base_badName_fits
#print axioms base_badName_refused
#print axioms base_notImplemented_refused
#print axioms clean_still_allows_badName
#print axioms badName_refused
#print axioms notImplemented_refused
#print axioms bad_current_code_refused
#print axioms notImplemented_current_code_refused
#print axioms ordinary_die_shape
#print axioms user_die_admitted
#print axioms user_current_code_admitted
#print axioms missingService_admitted_at_any_type
#print axioms missingService_empty_admitted
#print axioms missingService_nonempty_admitted
#print axioms missingService_current_code_admitted

theorem interrupt_admitted (w : W) (ty : EffTy) (who : Option FiberId) :
    ExitOk w ty (.failure (Cause.interrupt who)) := by
  apply strongExit_of_clean w ty _ rfl
  apply noShapeDefect_of_interrupts
  intro reason member
  simp only [Cause.interrupt_reasons, List.mem_singleton] at member
  subst member
  rfl

#print axioms interrupt_admitted

/-! Race failure-buffer controls. The whole historical payload predicate isolates the missing
exclusion; the current predicate refuses both forbidden buffers. The actual raceComplete
equality shows why checking only the incoming callback is insufficient. These finite payload
examples make no WorldValid, machine-reachability, or full transition claim. -/
namespace RaceFailureBuffers

def unitTy : EffTy := EffTy.pure .unit
def program : NativeEff := .succeed (.lit .unit)
def child : FiberId := ⟨1⟩
def world : W :=
  { initialWorld unitTy with
    Γ := fun _ => some unitTy
    Θ := fun _ _ => some unitTy }

def race (cause : CauseV) : Effect4.Program.Typed.RRace where
  id := 0
  host := Api.root
  token := 0
  state := {
    unstarted := []
    starting := none
    live := [child]
    remaining := 1
    failures := cause.reasons
    winner := none
    accepted := none
    cleanupNeeded := false
    requests := []
    cleanup := none
    cleanupRequested := false }
  settled := false
  programs := []
  registering := false

/-- Historical intermediate H2 contract: the failure buffer still used base membership,
while accepted and cleanup exits already required ExitOk. It is retained only as negative
evidence; current race admission uses RacePayload. -/
structure OldRacePayload (root : ProgramSource) (w : W) (r : Effect4.Program.Typed.RRace)
    (resultTy : EffTy) : Prop where
  token : w.Θ r.host r.token = some resultTy
  failures : FitsCause w resultTy.error ⟨r.state.failures⟩
  winner : ∀ pair ∈ r.state.winner, Fits w pair.2 resultTy.answer
  accepted : ∀ exit ∈ r.state.accepted, ExitOk w resultTy exit
  cleanup : ∀ wait ∈ r.state.cleanup, ExitOk w resultTy wait.result
  live : ∀ id ∈ r.state.live, ∀ childTy, w.Γ id = some childTy →
    childTy.answer.sub resultTy.answer = true ∧ childTy.error.sub resultTy.error = true
  programs : ∀ code ∈ r.programs, ∃ childTy, TypedProg root w childTy code ∧
    childTy.answer.sub resultTy.answer = true ∧ childTy.error.sub resultTy.error = true

theorem old_admitted (cause : CauseV) (clean : cleanExit (.failure cause) = true) :
    OldRacePayload (program : ProgramSource) world (race cause) unitTy := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fitsCause_of_clean world unitTy.error cause clean
  · intro pair member; cases member
  · intro exit member; cases member
  · intro wait member; cases member
  · intro id member childTy declared
    change some unitTy = some childTy at declared
    cases declared
    exact ⟨Ty.sub_refl _, Ty.sub_refl _⟩
  · intro code member; cases member

theorem old_badName_admitted :
    OldRacePayload (program : ProgramSource) world (race (Cause.die .badName)) unitTy :=
  old_admitted _ rfl

theorem old_notImplemented_admitted :
    OldRacePayload (program : ProgramSource) world (race (Cause.die .notImplemented)) unitTy :=
  old_admitted _ rfl

theorem new_badName_refused :
    ¬ RacePayload (program : ProgramSource) world (race (Cause.die .badName)) unitTy := by
  intro typed
  have excluded := typed.failures.2 (.die .badName .empty) (List.mem_singleton_self _)
  exact excluded.1 rfl

theorem new_notImplemented_refused :
    ¬ RacePayload (program : ProgramSource) world (race (Cause.die .notImplemented)) unitTy := by
  intro typed
  have excluded := typed.failures.2 (.die .notImplemented .empty) (List.mem_singleton_self _)
  exact excluded.2 rfl

theorem new_admitted (cause : CauseV) (typed : ExitOk world unitTy (.failure cause)) :
    RacePayload (program : ProgramSource) world (race cause) unitTy := by
  refine ⟨rfl, typed, ?_, ?_, ?_, ?_, ?_⟩
  · intro pair member; cases member
  · intro exit member; cases member
  · intro wait member; cases member
  · intro id member childTy declared
    change some unitTy = some childTy at declared
    cases declared
    exact ⟨Ty.sub_refl _, Ty.sub_refl _⟩
  · intro code member; cases member

theorem user_die_admitted (value : Nat) :
    RacePayload (program : ProgramSource) world (race (Cause.die (.user value))) unitTy := by
  apply new_admitted
  apply strongExit_of_clean world unitTy _ rfl
  intro reason member
  simp only [Cause.die_reasons, List.mem_singleton] at member
  subst reason
  exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

theorem interrupt_admitted :
    RacePayload (program : ProgramSource) world (race (Cause.interrupt none)) unitTy := by
  apply new_admitted
  apply strongExit_of_clean world unitTy _ rfl
  intro reason member
  change reason ∈ [.interrupt none .empty] at member
  rw [List.mem_singleton] at member
  subst reason
  trivial

theorem missingService_admitted :
    RacePayload (program : ProgramSource) world (race (Cause.die .missingService)) unitTy := by
  apply new_admitted
  apply strongExit_of_clean world unitTy _ rfl
  intro reason member
  simp only [Cause.die_reasons, List.mem_singleton] at member
  subst reason
  exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- The final child can contribute an empty, admitted cause; settlement still publishes all
previously buffered reasons. Thus checking only the new callback exit cannot close the hole. -/
theorem raceComplete_packages_buffer (cause : CauseV) :
    (Supervision.raceComplete (race cause).state child (.failure Cause.empty)).accepted =
      some (.failure cause) := by
  rw [Supervision.raceComplete_failure_last (race cause).state child Cause.empty
    (List.mem_singleton_self _) rfl (Nat.le_refl 1)]
  change (some (.failure ⟨cause.reasons ++ []⟩) : Option ExitV) = some (.failure cause)
  rw [List.append_nil]

theorem last_empty_failure_typed : ExitOk world unitTy (.failure Cause.empty) :=
  strongExit_of_clean world unitTy _ rfl (fun _ member => nomatch member)

theorem raceComplete_publishes_badName :
    (Supervision.raceComplete (race (Cause.die .badName)).state child
      (.failure Cause.empty)).accepted = some (.failure (Cause.die .badName)) :=
  raceComplete_packages_buffer _

theorem raceComplete_publishes_notImplemented :
    (Supervision.raceComplete (race (Cause.die .notImplemented)).state child
      (.failure Cause.empty)).accepted = some (.failure (Cause.die .notImplemented)) :=
  raceComplete_packages_buffer _

#print axioms old_admitted
#print axioms old_badName_admitted
#print axioms old_notImplemented_admitted
#print axioms new_badName_refused
#print axioms new_notImplemented_refused
#print axioms new_admitted
#print axioms user_die_admitted
#print axioms interrupt_admitted
#print axioms missingService_admitted
#print axioms raceComplete_packages_buffer
#print axioms last_empty_failure_typed
#print axioms raceComplete_publishes_badName
#print axioms raceComplete_publishes_notImplemented
end RaceFailureBuffers


/-! E4-TYPED-CE-008: retained part-two saved-frame witness from the model-probe audit.
The local FullExitOk additionally refuses missingService at an empty requirement row.
The accepted loop stack returns that failure unchanged across different requirement rows.
This is a saved-frame witness, not a reachable-run claim or a refutation of base FitsExit;
part one's live ExitOk deliberately admits missingService at both rows. -/
namespace MissingServiceTransport
open Effect4.Program.Typed.Contracts

/-- The proposed full exclusion, retained here only to expose its transport obligation. -/
def fullForbidden (ty : EffTy) : Reason Err Defect FiberId Ann → Bool
  | .die defect _ => defect == .badName || defect == .notImplemented ||
      (defect == .missingService && ty.requires == Env.Requirement.empty)
  | _ => false

def FullNoShapeDefect (ty : EffTy) : ExitV → Prop
  | .success _ => True
  | .failure cause => cause.reasons.any (fullForbidden ty) = false

def FullExitOk (w : W) (ty : EffTy) (ex : ExitV) : Prop :=
  FitsExit w ty ex ∧ FullNoShapeDefect ty ex

def inner : EffTy := ⟨.never, .never, Env.Requirement.single nativeScopeKey⟩
def outer : EffTy := EffTy.pure .unit
def missing : CauseV := Cause.die .missingService
def name : EffName := .abort
def saved : RSaved := ⟨.pure (.success .unit), [], false, none, false⟩

/-- The answer-never loop meets the actual frame protocol, whose continuation is vacuous. -/
theorem loop_admitted (src : ProgramSource) (w : W) :
    StackAccepts (TypedProg src) FullExitOk (frameProtocols src) w inner outer
      [.loop name .unit] := by
  apply StackAccepts.cons (middle := outer)
  · apply FrameAccepts.loop
    intro w' _
    exact LoopProtocol.step (tin := inner) (tout := outer) rfl (fun _ _ _ h => False.elim h)
  · exact StackAccepts.nil outer

theorem input_ok (w : W) : FullExitOk w inner (.failure missing) :=
  ⟨fitsExit_of_clean w inner missing rfl
    (ordinary_die_shape inner .missingService (fun h => nomatch h) (fun h => nomatch h)), rfl⟩

theorem provenance : InterruptProvenance saved := by
  constructor
  · intro c h
    cases h
  · intro h
    cases h

/-- The actual stack walk passes the failure through the loop without changing it. -/
theorem output_eq (interp : RInterp) :
    (popR interp (.failure missing) [.loop name .unit] saved).2 =
      some (.failure missing) := rfl

theorem output_bad (w : W) : ¬ FullExitOk w outer (.failure missing) := by
  intro typed
  have excluded := typed.2
  change true = false at excluded
  exact Bool.noConfusion excluded

#print axioms loop_admitted
#print axioms input_ok
#print axioms provenance
#print axioms output_eq
#print axioms output_bad
end MissingServiceTransport

end Test.Program.H2PartOne
