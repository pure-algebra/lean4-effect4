import Effect4.Laws.Program.Typed.Residual

/-! FR-08 ruling probe: the walk premise that makes `popR` type-preserving, the amended
frame contract that admits error-removing catches, and the lemma that makes preempted
skips harmless under the premise. Elaboration and the two finite controls only. -/
set_option autoImplicit false
namespace Probe.SkipsClean
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects Effect4.Program.Typed Effect4.Program.Typed.Contracts
abbrev TWorld := Effect4.Program.Typed.World

/-- A failure carrying no `Fail` reason (interrupts and defects only); every success. -/
def cleanExit : ExitV → Bool
  | .success _ => true
  | .failure c => c.reasons.all fun r => r.tag != .fail

/-- Every preempted skip of a resume arm along the actual `popR` walk carries a clean exit.
Mirrors `popR`'s recursion; interpreter-free because each arm that consults the interpreter
ends the walk. -/
def skipsClean (ex : ExitV) : List ScopeFrame → RSaved → Bool
  | [], _ => true
  | slot :: rest, frame =>
    let frame := { frame with stack := rest }
    let failing := match ex with | .failure _ => true | _ => false
    match slot with
    | .restoreMask flag | .finalizerMask flag =>
      let frame := { frame with interruptible := flag }
      match frame.interruptedCause with
      | some _ => if flag && !failing then true else skipsClean ex rest frame
      | none => skipsClean ex rest frame
    | .resume kind _ =>
      let frame := match kind with
        | .onExit false => { frame with interruptible := false }
        | _ => frame
      if kind.hasExitArm ex then
        if failing && frame.interruptible && frame.interruptedCause.isSome then
          cleanExit ex && skipsClean ex rest frame
        else true
      else skipsClean ex rest frame
    | .answer next =>
      match next ex with
      | .pure ex' => skipsClean ex' rest frame
      | .vis (.inr (.unguard ex')) _ => skipsClean ex' rest frame
      | _ => true
    | .asyncFinalizer _ =>
      match ex with
      | .failure _ => true
      | .success _ =>
        if frame.interruptible && frame.interruptedCause.isSome then true
        else skipsClean ex rest frame
    | .iter _ | .loop _ _ =>
      match ex with
      | .failure _ => skipsClean ex rest frame
      | .success _ => true

/-- A clean failure fits every effect type: the error column constrains `Fail` only. -/
theorem strongExit_of_clean (w : TWorld) (ty : EffTy) (c : CauseV)
    (h : cleanExit (.failure c) = true) : StrongExit w ty (.failure c) := by
  have hall : ∀ r ∈ c.reasons, r.tag ≠ .fail := by
    intro r hr
    have := List.all_eq_true.mp h r hr
    exact bne_iff_ne.mp this
  refine ⟨?_, (fun _ heq => nomatch heq), fun c' heq => ?_⟩
  · change causeAdmits _ ty.error c = true
    unfold causeAdmits
    rw [List.all_eq_true]
    intro r hr
    have hne := hall r hr
    cases r with
    | fail e ann => exact absurd rfl hne
    | die _ _ => rfl
    | interrupt _ _ => rfl
  · cases heq
    intro r hr
    have hne := hall r hr
    cases r with
    | fail e ann => exact absurd rfl hne
    | die _ _ => trivial
    | interrupt _ _ => trivial

/-- The amended frame contract: strong exits in, guard-miss-only skipping. -/
inductive FrameAccepts' (TypedProg : TWorld → EffTy → RProgram → Prop) (hooks : FrameProtocols)
    (w : TWorld) : EffTy → EffTy → ScopeFrame → Prop
  | resume {tin tout : EffTy} (kind : GuardKind) (next : ExitV → RProgram)
      (run : ∀ ex, StrongExit w tin ex → kind.hasExitArm ex = true → TypedProg w tout (next ex))
      (skip : ∀ ex, StrongExit w tin ex → kind.hasExitArm ex = false → StrongExit w tout ex) :
      FrameAccepts' TypedProg hooks w tin tout (.resume kind next)
  | answer {tin tout : EffTy} (next : ExitV → RProgram)
      (run : ∀ ex, StrongExit w tin ex → TypedProg w tout (next ex)) :
      FrameAccepts' TypedProg hooks w tin tout (.answer next)
  | restoreMask (ty : EffTy) (flag : Bool) : FrameAccepts' TypedProg hooks w ty ty (.restoreMask flag)
  | asyncFinalizer {tin tout : EffTy} (name : EffName)
      (protocol : hooks.asyncFinalizer w tin tout name) :
      FrameAccepts' TypedProg hooks w tin tout (.asyncFinalizer name)
  | finalizerMask (ty : EffTy) (flag : Bool) : FrameAccepts' TypedProg hooks w ty ty (.finalizerMask flag)
  | iter {tin tout : EffTy} (name : EffName) (protocol : hooks.iterator w tin tout name) :
      FrameAccepts' TypedProg hooks w tin tout (.iter name)
  | loop {tin tout : EffTy} (name : EffName) (cursor : Val)
      (protocol : hooks.loop w tin tout name cursor) :
      FrameAccepts' TypedProg hooks w tin tout (.loop name cursor)

inductive StackAccepts' (TypedProg : TWorld → EffTy → RProgram → Prop) (hooks : FrameProtocols)
    (w : TWorld) : EffTy → EffTy → List ScopeFrame → Prop
  | nil (ty : EffTy) : StackAccepts' TypedProg hooks w ty ty []
  | cons {tin middle tout : EffTy} {frame : ScopeFrame} {rest : List ScopeFrame}
      (head : FrameAccepts' TypedProg hooks w tin middle frame)
      (tail : StackAccepts' TypedProg hooks w middle tout rest) :
      StackAccepts' TypedProg hooks w tin tout (frame :: rest)

/-- The slice 5 statement, with the walk premise. Elaboration only here. -/
def PopRTyped (root : NativeEff) (hooks : FrameProtocols) : Prop :=
  ∀ (interp : RInterp) (w : TWorld) (tin tout : EffTy) (ex : ExitV)
    (stack : List ScopeFrame) (frame : RSaved),
    StackAccepts' (TypedProg root) hooks w tin tout stack →
    StrongExit w tin ex →
    InterruptProvenance frame →
    skipsClean ex stack frame = true →
    match popR interp ex stack frame with
    | (frame', none) => ∃ middle, TypedProg root w middle frame'.current ∧
        StackAccepts' (TypedProg root) hooks w middle tout frame'.stack ∧
        InterruptProvenance frame'
    | (_, some ex') => StrongExit w tout ex'

/-! ## The E4-SCHED-CE-006 state: accepted by the amended contract, excluded by the walk. -/

def beforeCatch : EffTy := ⟨.nat, .nat, Effect4.Machine.Env.Requirement.empty⟩
def afterCatch : EffTy := EffTy.pure .nat
def failure : ExitV := .failure (Cause.fail (.tag 42))
def recovery (_ex : ExitV) : RProgram := .pure (.success (.nat 0))
def masked : RSaved :=
  ⟨.pure failure, [.restoreMask true, .resume .onFailure recovery], false,
    some (Cause.interrupt (some ⟨1⟩)), false⟩

theorem strongValue_nat (w : TWorld) (k : Nat) : StrongValue w .nat (Val.nat k) := by
  refine ⟨rfl, trivial, fun h mem => ?_⟩
  cases mem

theorem recovery_typed (root : NativeEff) (w : TWorld) (ex : ExitV) :
    TypedProg root w afterCatch (recovery ex) := by
  refine ⟨Typed.pure ?_, ControlAdmitted.pure _ _ _⟩
  refine ⟨rfl, fun v heq => ?_, fun _ heq => nomatch heq⟩
  injection heq with heq
  subst heq
  exact strongValue_nat w 0

/-- Guard-miss-only skipping admits the ordinary Nat-removing catch. -/
theorem catch_skip (w : TWorld) (ex : ExitV) (typed : StrongExit w beforeCatch ex)
    (miss : GuardKind.onFailure.hasExitArm ex = false) : StrongExit w afterCatch ex := by
  cases ex with
  | success value => exact ⟨typed.1, ⟨typed.2.1, fun _ heq => nomatch heq⟩⟩
  | failure cause => cases miss

theorem masked_stack_accepted (root : NativeEff) (hooks : FrameProtocols) (w : TWorld) :
    StackAccepts' (TypedProg root) hooks w beforeCatch afterCatch masked.stack :=
  .cons (.restoreMask _ _)
    (.cons (.resume _ _ (fun ex _ _ => recovery_typed root w ex) (catch_skip w))
      (.nil _))

/-- The walk is not clean: its one preempted skip carries `Fail 42`. -/
theorem masked_walk_not_clean : skipsClean failure masked.stack masked = false := rfl

/-- The same stack with an interrupt-only failure is clean, and that failure fits afterCatch. -/
def interruptOnly : ExitV := .failure (Cause.interrupt (some ⟨1⟩))
theorem interrupt_walk_clean : skipsClean interruptOnly masked.stack masked = true := rfl
theorem interrupt_fits_after (w : TWorld) : StrongExit w afterCatch interruptOnly :=
  strongExit_of_clean w afterCatch _ rfl

#print axioms strongExit_of_clean
#print axioms masked_stack_accepted
#print axioms masked_walk_not_clean
#print axioms interrupt_fits_after
end Probe.SkipsClean
