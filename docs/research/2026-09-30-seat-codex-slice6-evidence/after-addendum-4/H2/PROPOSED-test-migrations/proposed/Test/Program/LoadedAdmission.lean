import Test.Counterexamples.Machine.Semantics.TrivialPosts
import Test.Program.H2PartOne

/-!
# Test.Program.LoadedAdmission — the census's second phase, seeded

Admission of the code the reference machine actually loads (`loadR`, i.e. `denoteR` at the root
point) for checker-typed programs, under the repaired protocol (typed-state admission audit §6,
2026-09-23). Each theorem types the whole loaded program at the checker's type, at every world:
one program per repaired precondition class, the timer's certified answer (`sleep`), source
admission of an installed body (`fork`, `scoped`), a race's entrants below the certified type
(`raceAll`), and a generator entered at its own node (`gen`). Source admission's checker runs
are kernel-evaluated (`decide +kernel`) on these finite programs.

The acceptance test of the repair is this file extended to every entry of
`Test/Program/TypedCorpus.lean`; the five here are the pattern, not the whole.
-/

set_option autoImplicit false
namespace Test.Program.LoadedAdmission
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
open Test.Counterexamples.TrivialPosts (sleeping sleepCode sleep_code_typed)
abbrev W := Effect4.Program.Typed.World

theorem env0 (w : W) : EnvTyped w [] [] := ⟨rfl, fun _ _ _ h => nomatch h⟩

/-! ## The timer -/

theorem sleep_loaded : ((loadR sleeping 20 20).fiber? Api.root).map (·.frame.current) = some sleepCode :=
  rfl

theorem sleep_admitted (w : W) (code : RProgram)
    (h : ((loadR sleeping 20 20).fiber? Api.root).map (·.frame.current) = some code) :
    TypedProg sleeping w (EffTy.pure .unit) code := by
  rw [sleep_loaded] at h
  cases h
  exact sleep_code_typed _ w

/-! ## Installed bodies -/

def one : NativeEff := .succeed (.lit (.nat 1))
def forked : NativeEff := .withFiber (.fork one ⟨true, false, .inherit⟩)
def scopedOne : NativeEff := .scoped one
#guard typeOf nativeSignature forked = some (EffTy.pure (.fiberOf .nat .never))
#guard typeOf nativeSignature scopedOne = some (EffTy.pure .nat)

theorem fork_admitted (w : W) :
    TypedProg forked w (EffTy.pure (.fiberOf .nat .never)) (denoteR forked forked (rootPoint 20)) := by
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (EffTy.pure .nat)
    (BodyTyped.at_ _ _ ⟨one, [], rfl, by decide +kernel, env0 w⟩) ?_
  intro w' _ ans hpost
  obtain ⟨id, rfl, hid⟩ := hpost
  exact TypedProg.pure ⟨⟨_, hid, Ty.sub_refl _, Ty.sub_refl _⟩, trivial⟩

theorem scoped_admitted (w : W) :
    TypedProg scopedOne w (EffTy.pure .nat) (denoteR scopedOne scopedOne (rootPoint 20)) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (EffTy.pure .nat) ⟨one, [], rfl, by decide +kernel, env0 w⟩
    (fun _ _ _ hpost => TypedProg.pure hpost)

/-! ## A race -/

def two : NativeEff := .succeed (.lit (.nat 2))
def race : NativeEff := .withFiber (.raceAll (.cons one (.cons two .nil)))
#guard typeOf nativeSignature race = some (EffTy.pure .nat)

theorem race_admitted (w : W) :
    TypedProg race w (EffTy.pure .nat) (denoteR race race (rootPoint 20)) := by
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (EffTy.pure .nat) ?_ (fun _ _ _ hpost => TypedProg.pure hpost)
  intro p hp
  cases hp with
  | head => exact ⟨_, ⟨one, [], rfl, by decide +kernel, env0 w⟩, Ty.sub_refl _, Ty.sub_refl _⟩
  | tail _ hp =>
    cases hp with
    | head => exact ⟨_, ⟨two, [], rfl, by decide +kernel, env0 w⟩, Ty.sub_refl _, Ty.sub_refl _⟩
    | tail _ hp => cases hp

/-! ## A generator -/

def generator : NativeEff := .gen (.cons (.bindYield one) (.cons (.ret (.var 0)) .nil))
#guard typeOf nativeSignature generator = some (EffTy.pure .nat)

theorem generator_checks :
    Checker.check (nativeSignature []) [] [] generator = .ok (EffTy.pure .nat) := by decide +kernel

theorem generator_admitted (w : W) :
    TypedProg generator w (EffTy.pure .nat) (denoteR generator generator (rootPoint 20)) := by
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial ?_
  intro w' _ _ _
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (EffTy.pure .nat) ⟨generator, [], rfl, generator_checks, env0 w'⟩
    (fun _ _ _ hpost => TypedProg.pure hpost)

/-! ## Contexts (decision row 90)

A service read's loaded code: the context read, then the lookup. The context handle's fit
carries its services' static typing, so the looked-up value is typed at the key's type. -/

def natKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def readService : NativeEff := .service natKey
#guard (typeOf nativeSignature readService).map (·.answer) = some .nat

theorem natKey_ty : nativeServiceTy natKey = some .nat := by decide +kernel

/-- Proposed amendment: the input must actually decode as a context; the old implication
was vacuous at malformed values and admitted badName. -/
theorem lookup_typed (w : W) (ty : EffTy) (answer : ty.answer = .nat) (v : Val)
    (isContext : ∃ ctx, Val.context? v = some ctx)
    (typed : ∀ ctx, Val.context? v = some ctx → ServicesFit w ctx.services) :
    TypedProg readService w ty (serviceLookupR natKey v) := by
  obtain ⟨ctx, hctx⟩ := isContext
  unfold serviceLookupR
  rw [hctx]
  split
  · rename_i sv hget
    have hfit := flatFits_fits (typed ctx hctx natKey sv .nat hget natKey_ty)
    refine TypedProg.pure (strongExit_success w ty sv ?_)
    rw [answer]
    exact hfit
  · exact TypedProg.pure (Test.Program.H2PartOne.missingService_admitted_at_any_type w ty)

/-- The existing context fit supplies the finite decoder witness needed by the amended test. -/
theorem context_of_fits (w : W) (v : Val) (typed : Fits w v (.handle Ty.contextTarget)) :
    ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w ctx.services := by
  simp only [Effect4.Program.Typed.Fits] at typed
  split at typed
  · simp only [HandleFits] at typed
    split at typed
    · exact absurd typed.1 (by decide)
    · exact absurd typed.1 (by decide)
    · exact absurd typed (by decide)
    · exact absurd typed.1 (by decide)
    · exact typed.elim
  · obtain ⟨_, ctx, hctx, services, _⟩ := typed
    exact ⟨ctx, hctx, services⟩

theorem service_admitted (w : W) (ty : EffTy) (answer : ty.answer = .nat) :
    TypedProg readService w ty (denoteR readService readService (rootPoint 20)) := by
  refine TypedProg.guard (EffTy.pure (.handle Ty.contextTarget)) ?_ ?_ ?_
  · refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) (Ty.handle Ty.contextTarget) rfl ?_
    intro w' _ ans hpost
    exact TypedProg.unguard (strongExit_success w' _ ans hpost)
  · intro w' _ ex hpost
    cases ex with
    | failure c => exact Bool.noConfusion hpost.1
    | success v =>
      obtain ⟨ctx, hctx, services⟩ := context_of_fits w' v hpost.2.1
      apply lookup_typed w' ty answer v ⟨ctx, hctx⟩
      intro ctx' hctx'
      rw [hctx] at hctx'
      cases hctx'
      exact services
  · intro w' _ ex hex miss
    cases ex with
    | success v => exact Bool.noConfusion miss
    | failure c => exact strongExit_of_clean w' ty c (cleanExit_of_never_fits w' _ c rfl hex.1) hex.2

/-- A memo hit's await is typed at the layer's context: the lookup certifies the layer's own
checked error type, and the hit's deferred is declared at the context handle and that error. -/
def layered : NativeEff :=
  .provideLayer (.effect natKey (.succeed (.lit (.nat 1)))) false (.service natKey)

theorem layer_checks :
    Checker.checkLayer (nativeSignature []) [0] (.effect natKey (.succeed (.lit (.nat 1)))) =
      .ok ⟨Env.Requirement.single natKey, .never, Env.Requirement.empty⟩ := by decide +kernel

def memoAwait (m : MemoMapId) : RProgram :=
  .vis (.inl (.memoGet [0] m)) fun v => match Val.memoHit? v with
    | some (cell, _) => .vis (.inr (.async (.registerAwait cell) (Val.promise cell))) Effects.Program.pure
    | none => .pure (.failure (Cause.interrupt none))

theorem memoAwait_typed (w : W) (m : MemoMapId) :
    TypedProg layered w (EffTy.pure (.handle Ty.contextTarget)) (memoAwait m) := by
  refine TypedProg.store Ty.never ⟨_, _, rfl, layer_checks, rfl⟩ ?_
  intro w' _ ans hpost
  dsimp only [memoAwait]
  split
  · rename_i cell owner hhit
    rcases hpost with hunit | ⟨cell', owner', hhit', hPi⟩
    · subst hunit
      exact nomatch hhit
    · rw [hhit] at hhit'
      cases hhit'
      exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) (EffTy.pure (.handle Ty.contextTarget))
        ⟨_, _, hPi, Ty.sub_refl _, Ty.sub_refl _⟩ (fun _ _ _ hpost => TypedProg.pure hpost)
  · exact TypedProg.pure (Test.Program.H2PartOne.interrupt_admitted w' _ none)

#print axioms sleep_admitted
#print axioms fork_admitted
#print axioms scoped_admitted
#print axioms race_admitted
#print axioms generator_admitted
#print axioms service_admitted
#print axioms lookup_typed
#print axioms memoAwait_typed
end Test.Program.LoadedAdmission
