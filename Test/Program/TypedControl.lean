import Test.Counterexamples.Machine.Semantics.AsyncHookContract

/-!
# Test.Program.TypedControl — the slice 5 contract ruling's controls

Positive and negative controls for the one program judgment `TypedProg` and the amended hook
contracts (`docs/research/2026-09-23-foundations-slice5-contract-ruling.md`). The repaired
counterparts of `E4-SCHED-CE-010/011/012`: the generated sleep cancellation is typed, and the
exact reachable sleep stack is accepted under the landed contracts. The finite controls reuse
the sleep program and its parked stack from `AsyncHookContract.lean`; every theorem here
quantifies over the world. `cancellation_cannot_type` there is the negative control for a
cancellation carrying a typed `Fail` at `unit`/`never`.
-/

set_option autoImplicit false
namespace Test.Program.TypedControl
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects
open Test.Counterexamples.AsyncHookContract (sleeping sleepCancel sleepStack sleep_stack_exact)
abbrev W := Effect4.Program.Typed.World

def natErr (n : Nat) : CauseV := ⟨[.fail (.tag n) .empty]⟩

theorem strongExit_unit (w : W) : StrongExit w (EffTy.pure .unit) (.success .unit) := by
  refine ⟨rfl, fun v heq => ?_, fun _ heq => nomatch heq⟩
  injection heq with heq
  subst heq
  exact ⟨rfl, trivial, fun h mem => by cases mem⟩

theorem strongExit_nat (w : W) (ty : EffTy) (n : Nat) (answer : ty.answer = .nat) :
    StrongExit w ty (.success (.nat n)) := by
  refine ⟨?_, fun v heq => ?_, fun _ heq => nomatch heq⟩
  · change Val.hasTy (.nat n) ty.answer _ = true
    rw [answer]
    rfl
  · injection heq with heq
    subst heq
    rw [answer]
    exact ⟨rfl, trivial, fun h mem => by cases mem⟩

/-- A Nat failure fits a Nat error column. -/
theorem natErr_fits (w : W) (ty : EffTy) (n : Nat) (error : ty.error = .nat) :
    StrongExit w ty (.failure (natErr n)) := by
  refine ⟨?_, (fun _ heq => nomatch heq), fun c heq => ?_⟩
  · change causeAdmits _ ty.error (natErr n) = true
    rw [error]
    rfl
  · cases heq
    intro r hr
    simp only [natErr, List.mem_singleton] at hr
    subst hr
    refine ⟨.nat n, rfl, ?_⟩
    rw [error]
    exact ⟨rfl, trivial, fun h mem => by cases mem⟩

/-! ## Positive: the generated sleep cancellation and the reachable stack -/

/-- The generated cancellation is typed at `unit`/`never` for every clean cause: the store
arm consults `sleepCancel`'s Unit post (CE-012), and the guard's success arm is the only arm
the post admits (CE-011). -/
theorem cancel_typed (w : W) (cause : CauseV) (clean : cleanExit (.failure cause) = true) :
    TypedProg sleeping w (EffTy.pure .unit) ((interpR sleeping).cancelThenFail sleepCancel cause) := by
  refine TypedProg.guard (EffTy.pure .unit) ?_ ?_ ?_
  · refine TypedProg.store () trivial ?_
    intro w' _ ans hpost
    have unit : ans = Val.unit := hpost
    subst unit
    exact TypedProg.unguard (strongExit_unit w')
  · intro w' _ ex hpost
    cases ex with
    | success v => exact TypedProg.pure (strongExit_of_clean w' _ cause clean)
    | failure c => exact Bool.noConfusion hpost.1
  · intro w' _ ex hex _
    exact hex

theorem cancel_interrupt_typed (w : W) :
    TypedProg sleeping w (EffTy.pure .unit)
      ((interpR sleeping).cancelThenFail sleepCancel (Cause.interrupt (some Api.root))) :=
  cancel_typed w _ rfl

/-- The exact stack a checker-typed `sleep(1)` parks on is accepted under the landed contracts
(the repaired counterpart of `sleep_stack_rejected`). -/
theorem sleep_stack_accepted (w : W) :
    Contracts.StackAccepts (TypedProg sleeping) StrongExit (frameProtocols sleeping) w
      (EffTy.pure .unit) (EffTy.pure .unit) sleepStack := by
  rw [sleep_stack_exact]
  refine .cons (.asyncFinalizer _ ⟨rfl, fun cause typed _ => ?_⟩)
    (.cons (.answer _ fun _ hex => TypedProg.pure hex) (.nil _))
  exact cancel_typed w cause (cleanExit_of_never w _ cause rfl typed)

/-! ## Positive: guards whose intermediate type differs from the outer type -/

/-- `denoteR`'s `catchCause` shape with a handler that succeeds with 0: the body fails with a
Nat and the catch removes the error column. -/
def natCatch : RProgram :=
  (guardR .onFailure (.pure (.failure (natErr 7)))).bind fun
    | .success v => .pure (.success v)
    | .failure _ => constructR fun _ => .pure (.success (.nat 0))

theorem natCatch_typed (root : NativeEff) (w : W) :
    TypedProg root w (EffTy.pure .nat) natCatch := by
  refine TypedProg.guard { EffTy.pure .nat with error := .nat } ?_ ?_ ?_
  · exact TypedProg.unguard (natErr_fits w _ 7 rfl)
  · intro w' _ ex hpost
    cases ex with
    | success v => exact Bool.noConfusion hpost.1
    | failure c =>
      refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) () trivial ?_
      intro w'' _ _ _
      exact TypedProg.pure (strongExit_nat w'' _ 0 rfl)
  · intro w' _ ex hex miss
    cases ex with
    | success v => exact ⟨hex.1, hex.2.1, fun _ heq => nomatch heq⟩
    | failure c => exact Bool.noConfusion miss

/-- An `onSuccess` guard that turns a Nat into a Bool: the miss arm passes a clean failure. -/
def natToBool : RProgram :=
  (guardR .onSuccess (.pure (.success (.nat 1)))).bind (seqR fun _ => .pure (.success (.bool true)))

theorem natToBool_typed (root : NativeEff) (w : W) :
    TypedProg root w (EffTy.pure .bool) natToBool := by
  refine TypedProg.guard (EffTy.pure .nat) ?_ ?_ ?_
  · exact TypedProg.unguard (strongExit_nat w _ 1 rfl)
  · intro w' _ ex hpost
    cases ex with
    | success v => exact TypedProg.pure (strongExit_bool w' _ (strongValue_bool_true w'))
    | failure c => exact Bool.noConfusion hpost.1
  · intro w' _ ex hex miss
    cases ex with
    | success v => exact Bool.noConfusion miss
    | failure c => exact strongExit_of_clean w' _ c (cleanExit_of_never w' _ c rfl hex)

/-! ## Negative controls -/

/-- The guard row refuses a failure answer to an `onSuccess` arm (CE-011's challenge). -/
theorem guard_rejects_wrong_arm (w : W) (mid : EffTy) (c : CauseV) :
    ¬ fiberPost w (.guard_ .onSuccess) mid (some (.failure c)) :=
  fun h => Bool.noConfusion h.1

/-- An `onSuccess` guard whose body fails with a Nat cannot be typed at `nat`/`never`, at any
middle type: the miss arm would pass the Nat failure out. -/
def leakyGuard : RProgram :=
  (guardR .onSuccess (.pure (.failure (natErr 7)))).bind (seqR fun v => .pure (.success v))

theorem leakyGuard_rejected (root : NativeEff) (w : W) :
    ¬ TypedProg root w (EffTy.pure .nat) leakyGuard := by
  intro h
  obtain ⟨mid, body, _, skip⟩ := TypedProg.guard_inv h
  have inner := unguard_payload_inv root w mid _ _ body
  exact Bool.noConfusion (skip w (leHost_refl w) _ inner rfl).1

/-- A top-level `unguard` payload outside the current type is refused. -/
theorem unguard_payload_rejected (root : NativeEff) (w : W) (k : ExitV → RProgram) :
    ¬ TypedProg root w (EffTy.pure .unit) (.vis (.inr (.unguard (.success (.nat 1)))) k) :=
  fun h => Bool.noConfusion (unguard_payload_inv root w _ _ k h).1

#print axioms cancel_typed
#print axioms cancel_interrupt_typed
#print axioms sleep_stack_accepted
#print axioms natCatch_typed
#print axioms natToBool_typed
#print axioms guard_rejects_wrong_arm
#print axioms leakyGuard_rejected
#print axioms unguard_payload_rejected
end Test.Program.TypedControl
