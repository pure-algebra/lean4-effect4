import Effect4.Laws.Program.Typed.Residual
/-!
E4-SCHED-CE-010/011/012: slice 5's frozen hook contract refused a reachable sleep stack.

CE-010: the async hook quantified over causes without an incoming `StrongExit` premise.
CE-011: the M3a `guard_` post was `True` and admitted a failure reply to an `onSuccess` arm.
CE-012: M3a's `ControlAdmitted` required continuations for all store replies, without the
post, so a Nat reply to sleepCancel's Unit row made a generated unguard payload ill-typed.

Ruled 2026-09-23 (`docs/research/2026-09-23-foundations-slice5-contract-ruling.md`). CE-010's
refuted object is the old clause, kept local as `ReviewedAsync`; it is refuted against the
landed judgment. CE-011 and CE-012 refute the M3a judgment, kept local as `ReviewedTypedProg`:
the old guard row (on the landed certificate carrier; the old post ignores the certificate)
and the old `ControlAdmitted`. Their repaired counterparts are positive controls in
`Test/Program/TypedControl.lean`. The type check, parked stack and timer completion are
finite controls; the refusal theorems quantify over every world and interpreter root.
-/
set_option autoImplicit false
namespace Test.Counterexamples.AsyncHookContract
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects
abbrev W := Effect4.Program.Typed.World

def poisonedCause : CauseV := ⟨[.fail (.tag 42) .empty, .interrupt (some Api.root) .empty]⟩
#guard poisonedCause.hasInterrupts
#guard GuardKind.onSuccess.hasExitArm (.failure poisonedCause) == false

theorem does_not_fit (w : W) : ¬ StrongExit w (EffTy.pure .unit) (.failure poisonedCause) :=
  fun h => Bool.noConfusion h.1

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

/-! ## CE-010 against the landed judgment -/

/-- The frozen asyncFinalizer clause of the slice 5 brief §3.3 before the ruling. -/
def ReviewedAsync (root : NativeEff) (w : W) (tin tout : EffTy) (name : EffName) : Prop :=
  tin = tout ∧ ∀ cause, cause.hasInterrupts = true →
    TypedProg root w tout ((interpR root).cancelThenFail name cause)

/-- A typed sleep cancellation returns its incoming cause at the hook's output type: the
body's store answer is Unit, so the guard's success arm must run. -/
theorem cancellation_exit (root : NativeEff) (w : W) (ty : EffTy) (cause : CauseV)
    (h : TypedProg root w ty ((interpR root).cancelThenFail sleepCancel cause)) :
    StrongExit w ty (.failure cause) := by
  obtain ⟨mid, body, run, _⟩ := TypedProg.guard_inv h
  obtain ⟨_, _, next⟩ := TypedProg.store_inv body
  have unit : StrongExit w mid (.success .unit) :=
    unguard_payload_inv root w mid _ _ (next w (leHost_refl w) .unit rfl)
  exact TypedProg.pure_inv (run w (leHost_refl w) (.success .unit) ⟨rfl, unit⟩)

theorem cancellation_cannot_type (root : NativeEff) (w : W) :
    ¬ TypedProg root w (EffTy.pure .unit)
      ((interpR root).cancelThenFail sleepCancel poisonedCause) :=
  fun h => does_not_fit w (cancellation_exit root w _ _ h)

theorem frozen_hook_rejects_unit (root : NativeEff) (w : W) (tin : EffTy) :
    ¬ ReviewedAsync root w tin (EffTy.pure .unit) sleepCancel :=
  fun h => cancellation_cannot_type root w (h.2 poisonedCause rfl)

/-- The two arrows required at the exact reachable stack cannot compose under the old clause,
whatever intermediate types are chosen. The tail answer is the identity (`sleep_stack_exact`). -/
def ReviewedSleepStack (w : W) : Prop :=
  ∃ tin middle, ReviewedAsync sleeping w tin middle sleepCancel ∧
    ∀ ex, StrongExit w middle ex → TypedProg sleeping w (EffTy.pure .unit) (.pure ex)

theorem sleep_stack_rejected (w : W) : ¬ ReviewedSleepStack w := by
  rintro ⟨tin, middle, hook, answer⟩
  have ex := cancellation_exit sleeping w middle poisonedCause (hook.2 poisonedCause rfl)
  exact does_not_fit w (TypedProg.pure_inv (answer (.failure poisonedCause) ex))

/-! ## CE-011 and CE-012 against the M3a judgment -/

/-- The M3a guard row: every answer admitted, whatever the arm. -/
def reviewedFiberPost (w' : W) (op : FiberOp) (cert : FiberCert op) (ans : op.answer) : Prop :=
  match op, cert, ans with
  | .guard_ _, _, _ => True
  | op, cert, ans => fiberPost w' op cert ans

def ReviewedΨ_F (root : NativeEff) : Protocol W FiberSig where
  Cert := FiberCert
  pre := fiberPre root
  post := reviewedFiberPost

/-- M3a's control admission: continuations for every answer, independent of the protocol. -/
inductive ReviewedControlAdmitted (root : NativeEff) : W → EffTy → RProgram → Prop
  | pure (w : W) (ty : EffTy) (ex : ExitV) :
      ReviewedControlAdmitted root w ty (.pure ex)
  | vis_inl (w : W) (ty : EffTy) (op : SyncOp) (k : Val → RProgram) :
      (∀ w', w.leHost w' → ∀ ans, ReviewedControlAdmitted root w' ty (k ans)) →
      ReviewedControlAdmitted root w ty (.vis (.inl op) k)
  | unguard (w : W) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram) :
      StrongExit w ty ex →
      (∀ w', w.leHost w' → ReviewedControlAdmitted root w' ty (k ex)) →
      ReviewedControlAdmitted root w ty (.vis (.inr (.unguard ex)) k)
  | finishFinalizer (w : W) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram) :
      StrongExit w ty ex →
      (∀ w', w.leHost w' → ReviewedControlAdmitted root w' ty (k ex)) →
      ReviewedControlAdmitted root w ty (.vis (.inr (.finishFinalizer ex)) k)
  | scoped (w : W) (ty : EffTy) (body : Point) (bty : EffTy) (k : ExitV → RProgram) :
      PointTyped root w body bty →
      (∀ w', w.leHost w' → ∀ ans, ReviewedControlAdmitted root w' ty (k ans)) →
      ReviewedControlAdmitted root w ty (.vis (.inr (.scoped body)) k)
  | scopeExit (w : W) (ty : EffTy) (prev : Ctx) (sc : Nat) (ex : ExitV) (k : ExitV → RProgram) :
      StrongExit w ty ex →
      (∀ w', w.leHost w' → ∀ ans, ReviewedControlAdmitted root w' ty (k ans)) →
      ReviewedControlAdmitted root w ty (.vis (.inr (.scopeExit prev sc ex)) k)
  | other (w : W) (ty : EffTy) (op : FiberOp) (k : op.answer → RProgram) :
      (∀ ex, op ≠ .unguard ex) →
      (∀ ex, op ≠ .finishFinalizer ex) →
      (∀ pt, op ≠ .scoped pt) →
      (∀ prev sc ex, op ≠ .scopeExit prev sc ex) →
      (∀ w', w.leHost w' → ∀ ans, ReviewedControlAdmitted root w' ty (k ans)) →
      ReviewedControlAdmitted root w ty (.vis (.inr op) k)

theorem reviewed_unguard_payload_inv (root : NativeEff) (w : W) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : ReviewedControlAdmitted root w ty (.vis (.inr (.unguard ex)) k)) :
    StrongExit w ty ex := by
  cases h with
  | unguard _ _ _ _ hex _ => exact hex
  | other _ _ _ _ hne _ _ _ _ => exact False.elim (hne ex rfl)

/-- The M3a program judgment: the protocol judgment and control admission, each choosing
its own certificates. -/
def ReviewedTypedProg (root : NativeEff) (w : W) (ty : EffTy) (p : RProgram) : Prop :=
  Typed hostOrder (Ψ_S.sum (ReviewedΨ_F root)) w (fun w' ex => StrongExit w' ty ex) p ∧
  ReviewedControlAdmitted root w ty p

/-- The M3a guard row admits the wrong arm used by CE-011. -/
theorem guard_admits_wrong_arm (root : NativeEff) (w : W) :
    (ReviewedΨ_F root).post w (.guard_ .onSuccess) (EffTy.pure .unit)
      (some (.failure poisonedCause)) := trivial

/-- Under the M3a guard row even a clean incoming cause fails: the protocol demands a typed
continuation for a failure answer to an onSuccess guard, which the frame never delivers. -/
theorem clean_cancellation_cannot_type (root : NativeEff) (w : W) (name : EffName)
    (cause : CauseV) :
    ¬ ReviewedTypedProg root w (EffTy.pure .unit) ((interpR root).cancelThenFail name cause) := by
  intro h
  obtain ⟨cert, _pre, next⟩ := Typed.inr_inv h.1
  have leaf := next w (leHost_refl w) (some (.failure poisonedCause)) trivial
  have exit : StrongExit w (EffTy.pure .unit) (.failure poisonedCause) :=
    Typed.pure_inv (o := hostOrder) (Ψ := Ψ_S.sum (ReviewedΨ_F root))
      (Q := fun w' ex => StrongExit w' (EffTy.pure .unit) ex) (w := w)
      (a := .failure poisonedCause) leaf
  exact does_not_fit w exit

/-- A recorded interrupt is a valid input at the intended Unit/never type. -/
theorem clean_input_fits (w : W) :
    StrongExit w (EffTy.pure .unit) (.failure (Cause.interrupt (some Api.root))) :=
  strongExit_of_clean w _ _ rfl

/-- Adding only the incoming-exit premise could not repair the M3a guard row. -/
theorem clean_cancellation_still_rejected (root : NativeEff) (w : W) (name : EffName) :
    ¬ ReviewedTypedProg root w (EffTy.pure .unit)
      ((interpR root).cancelThenFail name (Cause.interrupt (some Api.root))) :=
  clean_cancellation_cannot_type root w name _

/-- The store protocol excludes CE-012's challenge, but M3a's control admission ignored it. -/
theorem store_rejects_wrong_answer (w : W) :
    ¬ Ψ_S.post w (.sleepCancel Api.root 0) () (.nat 42) := by
  intro h
  cases h

/-- M3a control admission quantified over every store answer independently of the protocol.
The sleep cancellation could therefore be challenged with a Nat answer to its Unit row. -/
theorem control_cancellation_cannot_type (root : NativeEff) (w : W) (cause : CauseV) :
    ¬ ReviewedControlAdmitted root w (EffTy.pure .unit)
      ((interpR root).cancelThenFail sleepCancel cause) := by
  intro h
  cases h with
  | other _ _ _ _ _ _ _ _ next =>
    have body := next w (leHost_refl w) none
    cases body with
    | vis_inl _ _ _ _ nextStore =>
      have marker := nextStore w (leHost_refl w) (.nat 42)
      have fit := reviewed_unguard_payload_inv root w (EffTy.pure .unit) (.success (.nat 42)) _ marker
      exact Bool.noConfusion fit.1

-- The same source completes normally when its timer fires.
#guard (((replayR sleeping 40 [.evaluate Api.root, .advance (ClockMillis.ofNat 1)]).machine.fiber? Api.root).bind RunFiber.exit) == some (.success .unit)

#print axioms cancellation_exit
#print axioms cancellation_cannot_type
#print axioms frozen_hook_rejects_unit
#print axioms sleep_stack_exact
#print axioms sleep_stack_rejected
#print axioms guard_admits_wrong_arm
#print axioms clean_cancellation_cannot_type
#print axioms clean_input_fits
#print axioms clean_cancellation_still_rejected
#print axioms store_rejects_wrong_answer
#print axioms control_cancellation_cannot_type
end Test.Counterexamples.AsyncHookContract
