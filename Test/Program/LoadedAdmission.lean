import Test.Counterexamples.Machine.Semantics.TrivialPosts

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
  refine TypedProg.pure (strongExit_success w' _ _ ⟨rfl, fun id' mem => ?_, fun h mem => ?_⟩)
  · simp only [Val.keys, Handle.ofCode_fiber, Option.toList, List.mem_singleton] at mem
    injection mem with eq_id
    subst eq_id
    exact ⟨_, hid, Ty.sub_refl _, Ty.sub_refl _⟩
  · simp only [Val.keys, Handle.ofCode_fiber, Option.toList, List.mem_singleton] at mem
    subst h
    dsimp only [handleLive]
    rw [hid]
    rfl

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

#print axioms sleep_admitted
#print axioms fork_admitted
#print axioms scoped_admitted
#print axioms race_admitted
#print axioms generator_admitted
end Test.Program.LoadedAdmission
