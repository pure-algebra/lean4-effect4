import Effect4.Laws.Program.Typed.Residual
/-!
E4-SCHED-CE-010/011/012: slice 5's frozen hook contract refuses a reachable sleep stack.

CE-010: the async hook quantifies over causes without an incoming StrongExit premise.
CE-011: the existing guard_ post is True and admits a failure reply to an onSuccess arm.
CE-012: ControlAdmitted requires continuations for all store replies, without the post,
so a Nat reply to sleepCancel's Unit row makes a generated unguard payload ill-typed.

The exact candidate clause is local. Production Contracts, Admission and Residual stay
unchanged until an owner ruling. The type check, parked stack and timer completion are
finite controls; the refusal theorems quantify over every world and interpreter root.
-/
set_option autoImplicit false
namespace Test.Counterexamples.AsyncHookContract
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects
abbrev W := Effect4.Program.Typed.World

/-- The exact frozen asyncFinalizer clause in the slice 5 brief §3.3, kept local
because its universal cause quantifier rejects an admitted source case. -/
def ReviewedAsync (root : NativeEff) (w : W) (tin tout : EffTy) (name : EffName) : Prop :=
  tin = tout ∧ ∀ cause, cause.hasInterrupts = true →
    TypedProg root w tout ((interpR root).cancelThenFail name cause)

def poisonedCause : CauseV := ⟨[.fail (.tag 42) .empty, .interrupt (some Api.root) .empty]⟩
#guard poisonedCause.hasInterrupts

theorem does_not_fit (w : W) : ¬ StrongExit w (EffTy.pure .unit) (.failure poisonedCause) :=
  fun h => Bool.noConfusion h.1

theorem cancellation_cannot_type (root : NativeEff) (w : W) (name : EffName) :
    ¬ TypedProg root w (EffTy.pure .unit) ((interpR root).cancelThenFail name poisonedCause) := by
  intro h
  obtain ⟨cert, _pre, next⟩ := Typed.inr_inv h.1
  have leaf := next w (leHost_refl w) (some (.success .unit)) trivial
  have exit : StrongExit w (EffTy.pure .unit) (.failure poisonedCause) :=
    Typed.pure_inv (o := hostOrder) (Ψ := Ψ_S.sum (Ψ_F root))
      (Q := fun w' ex => StrongExit w' (EffTy.pure .unit) ex) (w := w) (a := .failure poisonedCause) leaf
  exact does_not_fit w exit

theorem frozen_hook_rejects_unit (root : NativeEff) (w : W) (tin : EffTy) (name : EffName) :
    ¬ ReviewedAsync root w tin (EffTy.pure .unit) name := by
  intro h
  exact cancellation_cannot_type root w name (h.2 poisonedCause rfl)

/-- Even a clean incoming cause fails: guard_'s True post admits a failure answer to
an onSuccess guard, although the real frame cannot deliver that answer. -/
theorem clean_cancellation_cannot_type (root : NativeEff) (w : W) (name : EffName)
    (cause : CauseV) :
    ¬ TypedProg root w (EffTy.pure .unit) ((interpR root).cancelThenFail name cause) := by
  intro h
  obtain ⟨cert, _pre, next⟩ := Typed.inr_inv h.1
  have leaf := next w (leHost_refl w) (some (.failure poisonedCause)) trivial
  have exit : StrongExit w (EffTy.pure .unit) (.failure poisonedCause) :=
    Typed.pure_inv (o := hostOrder) (Ψ := Ψ_S.sum (Ψ_F root))
      (Q := fun w' ex => StrongExit w' (EffTy.pure .unit) ex) (w := w)
      (a := .failure poisonedCause) leaf
  exact does_not_fit w exit

#guard GuardKind.onSuccess.hasExitArm (.failure poisonedCause) == false

/-- A recorded interrupt is a valid input at the intended Unit/never type. -/
theorem clean_input_fits (w : W) :
    StrongExit w (EffTy.pure .unit) (.failure (Cause.interrupt (some Api.root))) := by
  refine ⟨rfl, (fun _ h => nomatch h), fun c h => ?_⟩
  cases h
  intro r hr
  simp only [Cause.interrupt, List.mem_singleton] at hr
  subst hr
  trivial

/-- Adding only the incoming-exit premise cannot repair the guard post. -/
theorem clean_cancellation_still_rejected (root : NativeEff) (w : W) (name : EffName) :
    ¬ TypedProg root w (EffTy.pure .unit)
      ((interpR root).cancelThenFail name (Cause.interrupt (some Api.root))) :=
  clean_cancellation_cannot_type root w name _

/-- The protocol currently admits the wrong arm used by CE-011. -/
theorem guard_admits_wrong_arm (root : NativeEff) (w : W) :
    (Ψ_F root).post w (.guard_ .onSuccess) () (some (.failure poisonedCause)) := trivial

/-- The store protocol excludes CE-012's challenge, but ControlAdmitted ignores that post. -/
theorem store_rejects_wrong_answer (w : W) :
    ¬ Ψ_S.post w (.sleepCancel Api.root 0) () (.nat 42) := by
  intro h
  cases h

def sleeping : NativeEff := .perform .sleep (.lit (.nat 1))
#guard typeOf nativeSignature sleeping = some (EffTy.pure .unit)
def parked : RState := (replayR sleeping 20 [.evaluate Api.root]).machine
def atSleep : Bool := match parked.fiber? Api.root with
  | some f => f.parked == .withGuard 0 && match f.frame.stack with
    | .asyncFinalizer (.withWaiter (.store .cancelSleep) id token) :: .answer _ :: [] =>
      id == Api.root && token == 0
    | _ => false
  | none => false
#guard atSleep

def sleepStack : List ScopeFrame :=
  match parked.fiber? Api.root with
  | some f => f.frame.stack
  | none => []
def sleepCancel : EffName := .withWaiter (.store .cancelSleep) Api.root 0

theorem sleep_stack_exact :
    sleepStack = [.asyncFinalizer sleepCancel, .answer Effects.Program.pure] := rfl

/-- Control admission quantifies over every store answer independently of the protocol.
The sleep cancellation can therefore be challenged with a Nat answer to its Unit row. -/
theorem control_cancellation_cannot_type (root : NativeEff) (w : W) (cause : CauseV) :
    ¬ ControlAdmitted root w (EffTy.pure .unit) ((interpR root).cancelThenFail sleepCancel cause) := by
  intro h
  cases h with
  | other _ _ _ _ _ _ _ _ next =>
    have body := next w (leHost_refl w) none
    cases body with
    | vis_inl _ _ _ _ nextStore =>
      have marker := nextStore w (leHost_refl w) (.nat 42)
      have fit := unguard_payload_inv root w (EffTy.pure .unit) (.success (.nat 42)) _ marker
      exact Bool.noConfusion fit.1

/-- The cancellation success branch returns the incoming cause at the hook's output type. -/
theorem cancellation_exit (root : NativeEff) (w : W) (name : EffName) (ty : EffTy)
    (cause : CauseV) (h : TypedProg root w ty ((interpR root).cancelThenFail name cause)) :
    StrongExit w ty (.failure cause) := by
  obtain ⟨cert, _pre, next⟩ := Typed.inr_inv h.1
  have leaf := next w (leHost_refl w) (some (.success .unit)) trivial
  exact Typed.pure_inv (o := hostOrder) (Ψ := Ψ_S.sum (Ψ_F root))
    (Q := fun w' ex => StrongExit w' ty ex) (w := w) (a := .failure cause) leaf

/-- The two arrows required at this exact reachable stack cannot compose, whatever
intermediate types are chosen. The tail answer is the identity, as sleep_stack_exact checks. -/
def ReviewedSleepStack (w : W) : Prop :=
  ∃ tin middle, ReviewedAsync sleeping w tin middle sleepCancel ∧
    ∀ ex, StrongExit w middle ex → TypedProg sleeping w (EffTy.pure .unit) (.pure ex)

theorem sleep_stack_rejected (w : W) : ¬ ReviewedSleepStack w := by
  rintro ⟨tin, middle, hook, answer⟩
  have ex := cancellation_exit sleeping w sleepCancel middle poisonedCause (hook.2 poisonedCause rfl)
  have leaf := answer (.failure poisonedCause) ex
  exact does_not_fit w (Typed.pure_inv (o := hostOrder) (Ψ := Ψ_S.sum (Ψ_F sleeping))
    (Q := fun w' ex => StrongExit w' (EffTy.pure .unit) ex) (w := w)
    (a := .failure poisonedCause) leaf.1)

-- The same source completes normally when its timer fires.
#guard (((replayR sleeping 40 [.evaluate Api.root, .advance (ClockMillis.ofNat 1)]).machine.fiber? Api.root).bind RunFiber.exit) == some (.success .unit)

#print axioms cancellation_cannot_type
#print axioms frozen_hook_rejects_unit
#print axioms clean_cancellation_cannot_type
#print axioms sleep_stack_exact
#print axioms cancellation_exit
#print axioms sleep_stack_rejected
#print axioms control_cancellation_cannot_type
#print axioms clean_input_fits
#print axioms clean_cancellation_still_rejected
#print axioms guard_admits_wrong_arm
#print axioms store_rejects_wrong_answer
end Test.Counterexamples.AsyncHookContract
