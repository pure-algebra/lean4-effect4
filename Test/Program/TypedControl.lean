import Test.Counterexamples.Machine.Semantics.AsyncHookContract
import Test.Program.H2PartOne

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

theorem fitsExit_unit (w : W) : FitsExit w (EffTy.pure .unit) (.success .unit) := trivial

theorem fitsExit_nat (w : W) (ty : EffTy) (n : Nat) (answer : ty.answer = .nat) :
    FitsExit w ty (.success (.nat n)) := by
  change Fits w (.nat n) ty.answer
  rw [answer]
  trivial

/-- A Nat failure fits a Nat error column (and is shape-free, decisions row 152). -/
theorem natErr_fits (w : W) (ty : EffTy) (n : Nat) (error : ty.error = .nat) :
    FitsExit w ty (.failure (natErr n)) := by
  rw [fitsExit_failure_iff]
  refine ⟨?_, ?_⟩
  · intro r hr
    simp only [natErr, List.mem_singleton] at hr
    subst hr
    refine ⟨.nat n, rfl, ?_⟩
    rw [error]
    trivial
  · intro r hr
    simp only [natErr, List.mem_singleton] at hr
    subst hr
    trivial

/-- Test adapters retain the old base membership helpers above. -/
theorem exitOk_unit (w : W) : ExitOk w (EffTy.pure .unit) (.success .unit) :=
  ⟨fitsExit_unit w, trivial⟩

theorem exitOk_nat (w : W) (ty : EffTy) (n : Nat) (answer : ty.answer = .nat) :
    ExitOk w ty (.success (.nat n)) := ⟨fitsExit_nat w ty n answer, trivial⟩

theorem natErr_shape (ty : EffTy) (n : Nat) : NoShapeDefect ty (.failure (natErr n)) := by
  intro reason member
  simp only [natErr, List.mem_singleton] at member
  subst member
  trivial

theorem natErr_exitOk (w : W) (ty : EffTy) (n : Nat) (error : ty.error = .nat) :
    ExitOk w ty (.failure (natErr n)) := ⟨natErr_fits w ty n error, natErr_shape ty n⟩

/-! ## Positive: the generated sleep cancellation and the reachable stack -/

/-- The generated cancellation is typed at `unit`/`never` for a clean cause with explicit
shape exclusion. Cleanliness alone admits excluded defects. The store
arm consults `sleepCancel`'s Unit post (CE-012), and the guard's success arm is the only arm
the post admits (CE-011). -/
theorem cancel_typed (w : W) (cause : CauseV) (clean : cleanExit (.failure cause) = true)
    (shape : NoShapeDefect (EffTy.pure .unit) (.failure cause)) :
    TypedProg sleeping w (EffTy.pure .unit) ((interpR sleeping).cancelThenFail sleepCancel cause) := by
  refine TypedProg.guard (EffTy.pure .unit) ?_ ?_ ?_
  · refine TypedProg.store () trivial ?_
    intro w' _ ans hpost
    have unit : ans = Val.unit := hpost
    subst unit
    exact TypedProg.unguard (exitOk_unit w')
  · intro w' _ ex hpost
    cases ex with
    | success v => exact TypedProg.pure (strongExit_of_clean w' _ cause clean shape)
    | failure c => exact Bool.noConfusion hpost.1
  · intro w' _ ex hex _
    exact hex

theorem cancel_interrupt_typed (w : W) :
    TypedProg sleeping w (EffTy.pure .unit)
      ((interpR sleeping).cancelThenFail sleepCancel (Cause.interrupt (some Api.root))) :=
  cancel_typed w _ rfl (Test.Program.H2PartOne.interrupt_admitted w _ (some Api.root)).2

/-- The exact stack a checker-typed `sleep(1)` parks on is accepted under the landed contracts
(the repaired counterpart of `sleep_stack_rejected`). -/
theorem sleep_stack_accepted (w : W) :
    Contracts.StackAccepts (TypedProg sleeping) ExitOk (frameProtocols sleeping) w
      (EffTy.pure .unit) (EffTy.pure .unit) sleepStack := by
  rw [sleep_stack_exact]
  refine .cons (.asyncFinalizer _ fun _ _ => ⟨rfl, fun w'' _ cause typed _ => ?_⟩)
    (.cons (.answer _ fun _ _ _ hex => TypedProg.pure hex) (.nil _))
  exact cancel_typed w'' cause (cleanExit_of_never_fits w'' _ cause rfl typed.1) typed.2

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
  · exact TypedProg.unguard (natErr_exitOk w _ 7 rfl)
  · intro w' _ ex hpost
    cases ex with
    | success v => exact Bool.noConfusion hpost.1
    | failure c =>
      refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) () trivial ?_
      intro w'' _ _ _
      exact TypedProg.pure (exitOk_nat w'' _ 0 rfl)
  · intro w' _ ex hex miss
    cases ex with
    | success v => exact hex
    | failure c => exact Bool.noConfusion miss

/-- The continuation a guard node carries. -/
def guardK : RProgram → Option ExitV → RProgram
  | .vis (.inr (.guard_ _)) k => k
  | _ => fun _ => .pure (.success .unit)

theorem natCatch_eq : natCatch = .vis (.inr (.guard_ .onFailure)) (guardK natCatch) := rfl

/-- The frame the evaluator saves for that catch's guard is accepted from the guard's middle type
to `nat`, at every later world (`TypedProg.guard_frame`, row 135). -/
theorem natCatch_frame (root : NativeEff) (w : W) :
    ∃ mid : EffTy, TypedProg root w mid (guardK natCatch none) ∧
      Contracts.FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w mid (EffTy.pure .nat)
        (.resume .onFailure fun ex => guardK natCatch (some ex)) := by
  have h := natCatch_typed root w
  rw [natCatch_eq] at h
  exact TypedProg.guard_frame h

/-- An `onSuccess` guard that turns a Nat into a Bool: the miss arm passes a clean failure. -/
def natToBool : RProgram :=
  (guardR .onSuccess (.pure (.success (.nat 1)))).bind (seqR fun _ => .pure (.success (.bool true)))

theorem natToBool_typed (root : NativeEff) (w : W) :
    TypedProg root w (EffTy.pure .bool) natToBool := by
  refine TypedProg.guard (EffTy.pure .nat) ?_ ?_ ?_
  · exact TypedProg.unguard (exitOk_nat w _ 1 rfl)
  · intro w' _ ex hpost
    cases ex with
    | success v => exact TypedProg.pure ⟨trivial, trivial⟩
    | failure c => exact Bool.noConfusion hpost.1
  · intro w' _ ex hex miss
    cases ex with
    | success v => exact Bool.noConfusion miss
    | failure c => exact strongExit_of_clean w' _ c (cleanExit_of_never_fits w' _ c rfl hex.1) hex.2

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
  obtain ⟨mid, body, _, skip⟩ := TypedProg.guard_inv_of_ne h (fun h => nomatch h)
  have inner := unguard_payload_inv root w mid _ _ body
  have failed := fitsExit_failure_cause (skip w (leHost_refl w) _ inner rfl).1
  obtain ⟨v, _, hv⟩ := failed (.fail (.tag 7) .empty) (List.mem_singleton_self _)
  exact hv

/-- A top-level `unguard` payload outside the current type is refused. -/
theorem unguard_payload_rejected (root : NativeEff) (w : W) (k : ExitV → RProgram) :
    ¬ TypedProg root w (EffTy.pure .unit) (.vis (.inr (.unguard (.success (.nat 1)))) k) :=
  fun h => (unguard_payload_inv root w _ _ k h).1

#print axioms cancel_typed
#print axioms cancel_interrupt_typed
#print axioms sleep_stack_accepted
#print axioms natCatch_typed
#print axioms natCatch_frame
#print axioms natToBool_typed
#print axioms guard_rejects_wrong_arm
#print axioms leakyGuard_rejected
#print axioms unguard_payload_rejected
end Test.Program.TypedControl
