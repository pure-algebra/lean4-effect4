import Effect4.Laws.Program.Typed.World

/-!
Typed saved-stack interfaces (foundations plan D3–D5). These are judgments over the existing
reference proof carrier, not new stored program syntax. `TypedProg` and the named-frame
protocols are parameters until M3a. No evaluator preservation or world transport is asserted.
-/
set_option autoImplicit false
namespace Effect4.Program.Typed.Contracts
open Effect4 Effect4.Machine Effect4.Program.Sched Effect4.Program.Denote

/-- The exit observation at an effect type. Interruption is admitted separately from the
error column by the existing cause judgment. -/
def ExitFits (w : World) (ty : EffTy) (ex : ExitV) : Prop :=
  CompletionOk w (ty.answer, ty.error) (.ofExit ex)

/-- Named continuations need M3a's interpreter protocols. Keeping these requirements as
parameters avoids assuming meanings for names from their spelling alone. Each is an arrow
from the incoming exit type to the type expected by the remaining stack. -/
structure FrameProtocols where
  asyncFinalizer : World → EffTy → EffTy → EffName → Prop
  iterator : World → EffTy → EffTy → EffName → Prop
  loop : World → EffTy → EffTy → EffName → Val → Prop

section
variable (TypedProg : World → EffTy → RProgram → Prop) (hooks : FrameProtocols)

/-- Seven arms of `ScopeFrame` as typed arrows. `resume` also accounts for skipped arms and
interrupting failures; masks pass the exit type through. Named hooks retain their protocol
premise, including the cursor for a loop. Connection to `popR` is a later obligation. -/
inductive FrameAccepts (w : World) : EffTy → EffTy → ScopeFrame → Prop
  | resume {tin tout : EffTy} (kind : GuardKind) (next : ExitV → RProgram)
      (run : ∀ ex, ExitFits w tin ex → kind.hasExitArm ex = true → TypedProg w tout (next ex))
      (skip : ∀ ex, ExitFits w tin ex →
        (kind.hasExitArm ex = false ∨ ∃ cause, ex = .failure cause) → ExitFits w tout ex) :
      FrameAccepts w tin tout (.resume kind next)
  | answer {tin tout : EffTy} (next : ExitV → RProgram)
      (run : ∀ ex, ExitFits w tin ex → TypedProg w tout (next ex)) :
      FrameAccepts w tin tout (.answer next)
  | restoreMask (ty : EffTy) (flag : Bool) : FrameAccepts w ty ty (.restoreMask flag)
  | asyncFinalizer {tin tout : EffTy} (name : EffName)
      (protocol : hooks.asyncFinalizer w tin tout name) :
      FrameAccepts w tin tout (.asyncFinalizer name)
  | finalizerMask (ty : EffTy) (flag : Bool) : FrameAccepts w ty ty (.finalizerMask flag)
  | iter {tin tout : EffTy} (name : EffName) (protocol : hooks.iterator w tin tout name) :
      FrameAccepts w tin tout (.iter name)
  | loop {tin tout : EffTy} (name : EffName) (cursor : Val)
      (protocol : hooks.loop w tin tout name cursor) : FrameAccepts w tin tout (.loop name cursor)

/-- A stack composes arrows through a shared middle type, not one type at every frame. -/
inductive StackAccepts (w : World) : EffTy → EffTy → List ScopeFrame → Prop
  | nil (ty : EffTy) : StackAccepts w ty ty []
  | cons {tin middle tout : EffTy} {frame : ScopeFrame} {rest : List ScopeFrame}
      (head : FrameAccepts TypedProg hooks w tin middle frame)
      (tail : StackAccepts w middle tout rest) : StackAccepts w tin tout (frame :: rest)

/-- Structural scheduler provenance: recorded reasons are interrupts, not typed failures;
a deferred interrupt has a recorded cause. Proving that reachable scheduler states satisfy
this contract belongs to M3b/M4 (`Machine.interruptRecord`, rc.112 internal/effect.ts:575–594).
This does not assert that an arbitrary record has a reachable history. -/
structure InterruptProvenance (x : RSaved) : Prop where
  recorded : ∀ cause, x.interruptedCause = some cause →
    ∀ reason ∈ cause.reasons, reason.tag = .interrupt
  deferred : x.deferredInterrupt = true → x.interruptedCause.isSome = true

/-- Current code and stack meet at the same existentially chosen intermediate type. -/
def SavedOk (w : World) (final : EffTy) (x : RSaved) : Prop :=
  ∃ tin, TypedProg w tin x.current ∧ StackAccepts TypedProg hooks w tin final x.stack ∧
    InterruptProvenance x

/-- A resume reads the target's own token declaration, not the fiber's final type. Active
parking supplies the lookup in the future machine relation; absent/stale tokens impose no
code premise here. In particular, this conditional alone has no world-weakening theorem. -/
def ResumeOk (w : World) (target : FiberId) (token : Nat) (code : RProgram) : Prop :=
  ∀ ty, w.Θ target token = some ty → TypedProg w ty code

end

/-- M3a supplies the checker environment at a root/path. Its parameter receives the entire
capture, including environment, context, fuel and tape, so none of those correlations is
lost by this interface. -/
def CaptureOk (EnvironmentAt : World → Nat → List Nat → Capture → Prop)
    (w : World) (capture : Capture) : Prop :=
  EnvironmentAt w capture.root capture.path capture

namespace Example
/-- A finite relation used solely to witness the interface's changing middle type. -/
def Programs (_w : World) (ty : EffTy) (code : RProgram) : Prop :=
  (ty = EffTy.pure .bool ∧ code = .pure (.success (.bool true))) ∨
  (ty = EffTy.pure .unit ∧ code = .pure (.success .unit))

/-- Nat → Bool → Unit uses two answer frames, with a middle distinct from both ends.
This is a kernel-checked interface example, not an evaluator theorem. -/
theorem changing_middle (w : World) (hooks : FrameProtocols) :
    StackAccepts Programs hooks w (EffTy.pure .nat) (EffTy.pure .unit)
      [.answer (fun _ => .pure (.success (.bool true))),
       .answer (fun _ => .pure (.success .unit))] :=
  .cons (.answer _ (fun _ _ => Or.inl ⟨rfl, rfl⟩))
    (.cons (.answer _ (fun _ _ => Or.inr ⟨rfl, rfl⟩)) (.nil _))

theorem middle_differs : EffTy.pure .bool ≠ EffTy.pure .nat ∧
    EffTy.pure .bool ≠ EffTy.pure .unit := by
  constructor <;> intro h <;> cases h
end Example
end Effect4.Program.Typed.Contracts
