import Effect4.Laws.Program.Typed.Assembly

/-! H2 part-one controls for shared exit exclusion and buffered race failures.
badName and notImplemented are refused at typed exit boundaries, while ordinary defects,
interruptions, and missingService remain admitted. Since decisions row 152 the exclusion is also
part of membership at an exit type (`Fits`' `exitOf` arm reads `ShapeFree`), so base exit
membership refuses them too. The earlier judgments are history at
`git:def8babcc:Test/Program/H2PartOne.lean` (`oldExitFits`, `OldRacePayload`, `OldLoopProtocol`). -/
set_option autoImplicit false
namespace Test.Program.H2PartOne
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

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

theorem interrupt_admitted (w : W) (ty : EffTy) (who : Option FiberId) :
    ExitOk w ty (.failure (Cause.interrupt who)) := by
  apply strongExit_of_clean w ty _ rfl
  apply noShapeDefect_of_interrupts
  intro reason member
  simp only [Cause.interrupt_reasons, List.mem_singleton] at member
  subst member
  rfl

/-! Race failure-buffer controls. The current predicate refuses both forbidden buffers. The
actual raceComplete equality shows why checking only the incoming callback is insufficient. These finite payload
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
  refine ⟨rfl, typed, ?_, ?_, ?_, ?_⟩
  · intro pair member; cases member
  · intro exit member; cases member
  · intro wait member; cases member
  · intro id member
    exact ⟨unitTy, rfl, Ty.sub_refl _, Ty.sub_refl _⟩

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

end RaceFailureBuffers

/-! E4-TYPED-CE-008: retained part-two saved-frame witness from the model-probe audit.
The local FullExitOk additionally refuses missingService at an empty requirement row.
The accepted loop stack returns that failure unchanged across different requirement rows.
This is a saved-frame witness, not a reachable-run claim or a refutation of base FitsExit;
part one's live ExitOk deliberately admits missingService at both rows.

Decisions row 117's side condition (seat D1, 2026-10-01): the iterator and loop protocols keep
the requirement row from emptying (`LoopProtocol.step`'s `rows`, the condition under which part
two transports along the frame, `exitOk2_transport` in the formal pass's G5), so the witness's
stack is refused (`loop_refused`), and a loop frame that keeps the row is still accepted
(`loop_kept_admitted`). Part two itself (`FullExitOk` as the live exit judgment)
is not landed: it needs the presence clause per position, which the walk does not carry (seat
D1's receipt). -/
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

/-- **The flip** (decisions row 117's side condition, proved): the loop frame's protocol keeps
the requirement row from emptying, and `inner` requires the scope service while `outer` requires
nothing, so the witness's stack is refused, under every exit judgment. -/
theorem loop_refused (src : ProgramSource) (w : W)
    (Ex : W → EffTy → ExitV → Prop) :
    ¬ StackAccepts (TypedProg src) Ex (frameProtocols src) w inner outer [.loop name .unit] := by
  intro h
  cases h with
  | cons head tail =>
    cases tail
    cases head with
    | loop _ _ protocol =>
      exact absurd ((protocol w (leHost_refl w)).unfold.2.1 rfl) (by decide)

/-- A loop that keeps its requirement row. -/
def innerKept : EffTy := ⟨.unit, .never, Env.Requirement.single nativeScopeKey⟩

/-- **Positive control** (proved): a loop frame that does not empty the row is accepted, here
from `inner` to `innerKept`, both requiring the scope service. -/
theorem loop_kept_admitted (src : ProgramSource) (w : W) :
    StackAccepts (TypedProg src) FullExitOk (frameProtocols src) w inner innerKept
      [.loop name .unit] := by
  apply Effect4.Contracts.Path.cons (middle := innerKept)
  · apply FrameAccepts.loop
    intro w' _
    exact LoopProtocol.fold (tin := inner) (tout := innerKept)
      ⟨rfl, fun h => absurd h (by decide), fun _ _ _ _ _ h => False.elim h⟩
  · exact Effect4.Contracts.Path.nil innerKept

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

end MissingServiceTransport

/-! ## Row 117's presence clause, measured (seat D1, 2026-10-01)

The formal pass's G5 proposes a presence clause in `SavedOk`'s current-code typing,
`Provides ctx ty.requires`. Stated here over local copies (`Provides`, `SavedOkPresent`), it is
not landed in `src/`, for two reasons proved below. The walk installs code at a frame's output
type, not at the current code's, so presence at the current code alone is not re-established
by it (`presence_not_walked`: a saved frame meeting the clause pops to one that does not, while
the presence-free walk theorem still types it, `walked_typed`); a clause that holds per position
needs the stack to carry each position's context. And the loaded root runs in the empty context
(`loadR`), so at the load the clause asks the root row to be empty, which the checker does not
(`load_presence_needs_closed_row`): M5 would gain that premise. -/
namespace PresenceMeasure
open Effect4.Program.Typed.Contracts

/-- Presence: every key of the row is bound in the context. -/
def Provides (ctx : Ctx) (r : Env.Requirement) : Prop :=
  ∀ key, key ∈ r → (ctx.services.getV key).isSome = true

/-- `SavedOk` with G5's presence clause at its current code. -/
def SavedOkPresent (root : ProgramSource) (w : W) (final : EffTy) (ctx : Ctx) (x : RSaved) :
    Prop :=
  ∃ tin, TypedProg root w tin x.current ∧ Provides ctx tin.requires ∧
    StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin final x.stack ∧
    InterruptProvenance x

/-- A row that requires the scope service. -/
def keyTy : EffTy := ⟨.unit, .never, Env.Requirement.single nativeScopeKey⟩

/-- An answer continuation the walk installs (it is neither a bare exit nor a closing marker). -/
def next : ExitV → RProgram := fun _ => .vis (.inr (.sync Val.unit)) fun v => .pure (.success v)

/-- Current code at the empty row, one answer frame up to `keyTy`. -/
def x0 : RSaved := ⟨.pure (.success Val.unit), [.answer next], true, none, false⟩

theorem next_typed (root : ProgramSource) (w : W) (ex : ExitV) :
    TypedProg root w keyTy (next ex) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial fun _ _ ans post => by
      change ans = Val.unit at post
      subst post
      exact TypedProg.pure ⟨trivial, trivial⟩

theorem empty_provides (ctx : Ctx) : Provides ctx Env.Requirement.empty :=
  fun key h => absurd h (Row.not_mem_empty key)

theorem emptyCtx_lacks_scope : ¬ Provides emptyCtx keyTy.requires := by
  intro h
  have bound := h nativeScopeKey ((Row.mem_singleton _ _).mpr rfl)
  change ((Env.Context.empty : Env.Ctx).getV nativeScopeKey).isSome = true at bound
  rw [Env.Context.getV_empty] at bound
  exact Bool.noConfusion bound

/-- The input meets the presence clause in the empty context: its current code needs nothing. -/
theorem input_present (root : ProgramSource) (w : W) :
    SavedOkPresent root w keyTy emptyCtx x0 :=
  ⟨EffTy.pure .unit, TypedProg.pure ⟨trivial, trivial⟩, empty_provides emptyCtx,
    .cons (.answer next fun w' _ ex _ => next_typed root w' ex) (.nil keyTy),
    ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩

/-- The walk at a success installs the answer frame's continuation, with nothing left on the
stack. -/
theorem walk_installs (interp : RInterp) :
    popR interp (.success Val.unit) x0.stack x0 =
      ({ x0 with stack := [], current := next (.success Val.unit) }, none) := rfl

/-- **Presence at the current code is not walked** (proved): the frame `x0` meets the clause in
the empty context, and the frame the walk leaves does not, since its code sits at the answer
frame's output row, which requires the scope service. -/
theorem presence_not_walked (root : ProgramSource) (w : W) :
    SavedOkPresent root w keyTy emptyCtx x0 ∧
      ¬ SavedOkPresent root w keyTy emptyCtx
        (popR (interpR root.program) (.success Val.unit) x0.stack x0).1 := by
  refine ⟨input_present root w, ?_⟩
  rw [walk_installs]
  rintro ⟨tin, _, present, stack, _⟩
  cases stack
  exact emptyCtx_lacks_scope present

/-- The presence-free walk theorem still types the same output (`popR_typed`). -/
theorem walked_typed (root : ProgramSource) (w : W) :
    WalkTyped root (frameProtocols root) w keyTy
      (popR (interpRAt root.program []) (.success Val.unit) x0.stack x0) :=
  popR_typed _ _ _ w (hookLawsAt_interpRAt _ w [] (fun _ h => nomatch h)) x0.stack (EffTy.pure .unit) keyTy (.success Val.unit) x0
    (.cons (.answer next fun w' _ ex _ => next_typed root w' ex) (.nil keyTy))
    ⟨trivial, trivial⟩ ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩

/-- A checked program whose row is not empty: `acquireRelease` outside `scoped` requires the
scope service. -/
def openProg : NativeEff := .acquireRelease (.succeed (.lit .unit)) (.succeed (.lit .unit))

theorem openProg_checked :
    Program.typeOfProgram (openProg : ProgramSource).signature openProg = some keyTy := by
  decide +kernel

/-- **At the load the clause needs a closed row** (proved): the loaded root's context is the empty
one (`loadR`), which does not provide the row the checker gives `openProg`. -/
theorem load_presence_needs_closed_row (fuel compileFuel : Nat) :
    (∀ f ∈ (loadR openProg fuel compileFuel).fibers, f.context = emptyCtx) ∧
      ¬ Provides emptyCtx keyTy.requires := by
  refine ⟨fun f hf => ?_, emptyCtx_lacks_scope⟩
  change f ∈ [_] at hf
  rw [List.mem_singleton] at hf
  subst hf
  rfl

end PresenceMeasure

end Test.Program.H2PartOne
