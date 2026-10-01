import Effect4.Laws.Program.Typed.Validity

/-!
Typed saved-stack interfaces (foundations plan D3–D5). These are judgments over the existing
reference proof carrier, not new stored program syntax. The program judgment, the exit
judgment and the named-frame protocols are parameters: this module imports only the world and
its host order, and `Typed/Residual.lean` instantiates them.

The frame judgment is Kripke-closed (decisions row 135, `E4-TYPED-CE-012`): every clause that
reads the world, a continuation's `run` and `skip` and the three hook premises, quantifies over
the later worlds of the host order (`World.leHost`), the shape `TypedProg`'s own continuations
and the vocabulary's `continuation` source already have. A one-world frame clause holds
vacuously where no exit fits yet and fails once an allocation makes one fit
(`Test/Program/FramesNotKripke.lean`). Closed, a saved stack transports along world growth with
no premise on the judgments it is built from (`stackAccepts_mono`), and at the current world
each clause gives what the one-world clause gave. A stack composes frames as arrows through
shared middle types: the free category's composition, identity and decomposition
(`stackAccepts_append`, `stackAccepts_id`, `stackAccepts_split`, `stackAccepts_push`).
-/
set_option autoImplicit false
namespace Effect4.Program.Typed.Contracts
open Effect4 Effect4.Machine Effect4.Program.Sched Effect4.Program.Denote

/-- Named continuations need M3a's interpreter protocols. Keeping these requirements as
parameters avoids assuming meanings for names from their spelling alone. Each is an arrow
from the incoming exit type to the type expected by the remaining stack. -/
structure FrameProtocols where
  asyncFinalizer : World → EffTy → EffTy → EffName → Prop
  iterator : World → EffTy → EffTy → EffName → Prop
  loop : World → EffTy → EffTy → EffName → Val → Prop

section
variable (TypedProg : World → EffTy → RProgram → Prop)
  (Exits : World → EffTy → ExitV → Prop) (hooks : FrameProtocols)

/-- Seven arms of `ScopeFrame` as typed arrows (slice 5 R3, ruled 2026-09-21), closed under
later worlds (row 135). `resume` types the running arm and the guard miss separately; a
preempted skip passes the sanitized exit, which carries no `Fail` and fits every type
(`strongExit_of_clean`; divergence `U-01`, `E4-SCHED-CE-008`). The former all-failures
disjunct stood in for preemption and rejected every error-removing catch. Masks pass the exit
type through; named hooks retain their protocol premise at every later world, including the
cursor for a loop. Connection to `popR` is `Typed/Stack.lean`'s `popR_typed`. -/
inductive FrameAccepts (w : World) : EffTy → EffTy → ScopeFrame → Prop
  | resume {tin tout : EffTy} (kind : GuardKind) (next : ExitV → RProgram)
      (run : ∀ w', w.leHost w' → ∀ ex, Exits w' tin ex → kind.hasExitArm ex = true →
        TypedProg w' tout (next ex))
      (skip : ∀ w', w.leHost w' → ∀ ex, Exits w' tin ex → kind.hasExitArm ex = false →
        Exits w' tout ex) :
      FrameAccepts w tin tout (.resume kind next)
  | answer {tin tout : EffTy} (next : ExitV → RProgram)
      (run : ∀ w', w.leHost w' → ∀ ex, Exits w' tin ex → TypedProg w' tout (next ex)) :
      FrameAccepts w tin tout (.answer next)
  | restoreMask (ty : EffTy) (flag : Bool) : FrameAccepts w ty ty (.restoreMask flag)
  | asyncFinalizer {tin tout : EffTy} (name : EffName)
      (protocol : ∀ w', w.leHost w' → hooks.asyncFinalizer w' tin tout name) :
      FrameAccepts w tin tout (.asyncFinalizer name)
  | finalizerMask (ty : EffTy) (flag : Bool) : FrameAccepts w ty ty (.finalizerMask flag)
  | iter {tin tout : EffTy} (name : EffName)
      (protocol : ∀ w', w.leHost w' → hooks.iterator w' tin tout name) :
      FrameAccepts w tin tout (.iter name)
  | loop {tin tout : EffTy} (name : EffName) (cursor : Val)
      (protocol : ∀ w', w.leHost w' → hooks.loop w' tin tout name cursor) :
      FrameAccepts w tin tout (.loop name cursor)

/-- A stack composes arrows through a shared middle type, not one type at every frame. -/
inductive StackAccepts (w : World) : EffTy → EffTy → List ScopeFrame → Prop
  | nil (ty : EffTy) : StackAccepts w ty ty []
  | cons {tin middle tout : EffTy} {frame : ScopeFrame} {rest : List ScopeFrame}
      (head : FrameAccepts TypedProg Exits hooks w tin middle frame)
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
  ∃ tin, TypedProg w tin x.current ∧ StackAccepts TypedProg Exits hooks w tin final x.stack ∧
    InterruptProvenance x

/-- A resume reads the target's own token declaration, not the fiber's final type. Active
parking supplies the lookup in the future machine relation; absent/stale tokens impose no
code premise here. In particular, this conditional alone has no world-weakening theorem: a
later world may declare a token this one leaves open (row 106's freshness bound is what keeps
it stable). -/
def ResumeOk (w : World) (target : FiberId) (token : Nat) (code : RProgram) : Prop :=
  ∀ ty, w.Θ target token = some ty → TypedProg w ty code

end

/-- M3a supplies the checker environment at a root/path. Its parameter receives the entire
capture, including environment, context, fuel and tape, so none of those correlations is
lost by this interface. -/
def CaptureOk (EnvironmentAt : World → Nat → List Nat → Capture → Prop)
    (w : World) (capture : Capture) : Prop :=
  EnvironmentAt w capture.root capture.path capture

/-! ## World growth

The closed judgment transports along the host order with no premise on the program judgment,
the exit judgment or the hooks: each world-reading clause is moved by composing the order. -/

section Laws
variable {TP : World → EffTy → RProgram → Prop} {Ex : World → EffTy → ExitV → Prop}
  {hooks : FrameProtocols}

/-- One frame transports along the host order. -/
theorem frameAccepts_mono {w w' : World} (ord : w.leHost w') {a b : EffTy} {f : ScopeFrame}
    (h : FrameAccepts TP Ex hooks w a b f) : FrameAccepts TP Ex hooks w' a b f := by
  cases h with
  | resume kind next run skip =>
    exact .resume kind next (fun w'' o ex hx hk => run w'' (leHost_trans _ _ _ ord o) ex hx hk)
      (fun w'' o ex hx hk => skip w'' (leHost_trans _ _ _ ord o) ex hx hk)
  | answer next run =>
    exact .answer next (fun w'' o ex hx => run w'' (leHost_trans _ _ _ ord o) ex hx)
  | restoreMask flag => exact .restoreMask _ flag
  | asyncFinalizer name protocol =>
    exact .asyncFinalizer name (fun w'' o => protocol w'' (leHost_trans _ _ _ ord o))
  | finalizerMask flag => exact .finalizerMask _ flag
  | iter name protocol => exact .iter name (fun w'' o => protocol w'' (leHost_trans _ _ _ ord o))
  | loop name cursor protocol =>
    exact .loop name cursor (fun w'' o => protocol w'' (leHost_trans _ _ _ ord o))

/-- **A saved stack transports along the host order** (row 135), with no premise on the
program judgment, the exit judgment or the hooks. -/
theorem stackAccepts_mono {w w' : World} (ord : w.leHost w') {a b : EffTy} {s : List ScopeFrame}
    (h : StackAccepts TP Ex hooks w a b s) : StackAccepts TP Ex hooks w' a b s := by
  induction h with
  | nil ty => exact .nil ty
  | cons head _ ih => exact .cons (frameAccepts_mono ord head) ih

/-- A saved frame transports along the host order once its program judgment does
(`Typed/Residual.lean` instantiates this with `typedProg_mono`). -/
theorem savedOk_mono (tp : ∀ {w w' : World} {ty : EffTy} {p : RProgram}, w.leHost w' →
      TP w ty p → TP w' ty p)
    {w w' : World} (ord : w.leHost w') {final : EffTy} {x : RSaved}
    (h : SavedOk TP Ex hooks w final x) : SavedOk TP Ex hooks w' final x := by
  obtain ⟨tin, code, stack, provenance⟩ := h
  exact ⟨tin, tp ord code, stackAccepts_mono ord stack, provenance⟩

/-! ## The frame category

Frames are arrows `tin → tout`, a stack a composable path; the middle types are existential
(decisions row 48), so `StackAccepts` is the free category's image in relations. The walk and
the push sites (`pushR`, the `onExit` mask push, the `iter`/`loop` re-push) move frame groups
with these laws instead of re-deriving middles. -/

/-- Composition: a stack `a → b` followed by a stack `b → c` is a stack `a → c`. -/
theorem stackAccepts_append {w : World} {a b c : EffTy} {s₁ s₂ : List ScopeFrame}
    (h₁ : StackAccepts TP Ex hooks w a b s₁) (h₂ : StackAccepts TP Ex hooks w b c s₂) :
    StackAccepts TP Ex hooks w a c (s₁ ++ s₂) := by
  induction h₁ with
  | nil ty => exact h₂
  | cons head _ ih => exact .cons head (ih h₂)

/-- Decomposition: a stack over `s₁ ++ s₂` factors through a middle type. -/
theorem stackAccepts_split {w : World} :
    ∀ (s₁ s₂ : List ScopeFrame) {a c : EffTy}, StackAccepts TP Ex hooks w a c (s₁ ++ s₂) →
      ∃ b, StackAccepts TP Ex hooks w a b s₁ ∧ StackAccepts TP Ex hooks w b c s₂
  | [], _, a, _, h => ⟨a, .nil a, h⟩
  | f :: s₁, s₂, _, _, h => by
    rw [List.cons_append] at h
    cases h with
    | cons head tail =>
      obtain ⟨b, h₁, h₂⟩ := stackAccepts_split s₁ s₂ tail
      exact ⟨b, .cons head h₁, h₂⟩

/-- The identity: the empty stack at every type. -/
theorem stackAccepts_id {w : World} (a : EffTy) : StackAccepts TP Ex hooks w a a [] := .nil a

/-- Pushing one frame on top composes it before the old stack. -/
theorem stackAccepts_push {w : World} {a b c : EffTy} {f : ScopeFrame} {s : List ScopeFrame}
    (hf : FrameAccepts TP Ex hooks w a b f) (hs : StackAccepts TP Ex hooks w b c s) :
    StackAccepts TP Ex hooks w a c (f :: s) := .cons hf hs

end Laws

end Effect4.Program.Typed.Contracts
