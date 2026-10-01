import Effect4.Laws.Program.Typed.Stack

/-!
# Formal pass, seat PROOFS — positive probe: typed continuations compose; where the exit
# judgment composes with them

Base `efd67af1`. Reading aid for `note.md` §2 (Harper's typed stacks, the K machine) and §3
(gaps on row 117). No tracked file is changed.

1. `StackAccepts` (`Typed/Contracts.lean:65`) is a typed path: frames are arrows `tin → tout`
   (`FrameAccepts`), a stack is a composable list of them. `stackAccepts_append` and
   `stackAccepts_split` are the two laws of the free category on the frame-typing graph
   (composition is list append; the identity is `nil`; associativity is that of `++`). They
   hold for every program judgment, exit judgment and hook protocol, so M6's proofs may push
   and pop frame groups (`pushR`, the `onExit` mask push, `iter`/`loop` re-push) without
   re-deriving middles.
2. The exit judgment part one (row 107 as ruled: `NoShapeDefect` excludes `badName` and
   `notImplemented`, ignores the type) composes along every frame along which `FitsExit`
   composes (`exitOk1_transport`, `exitOk1_stack`).
3. Part two (`missingService` excluded when nothing is required) composes along a frame when
   the frame does not empty the requirement row (`exitOk2_transport`), and *not* in general
   (`exitOk2_transport_refuted`, the audit's `AuditH2` loop frame shape, restated). So the
   row-117 contract needs, at a discharging frame (scoped, a provision region), a fact the
   transport cannot supply: that the discharged services were present (a coeffect-style
   context invariant), since `Defect.missingService` names no key.
-/

set_option autoImplicit false

namespace FormalPass.Proofs.FrameCategory
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
open Effect4.Program.Typed.Contracts
abbrev W := Effect4.Program.Typed.World

/-! ## 1. Typed stacks form a category -/

section Stacks
variable {TP : W → EffTy → RProgram → Prop} {Ex : W → EffTy → ExitV → Prop}
  {hooks : FrameProtocols} {w : W}

/-- Composition: a stack `a → b` followed by a stack `b → c` is a stack `a → c`. -/
theorem stackAccepts_append {a b c : EffTy} {s₁ s₂ : List ScopeFrame}
    (h₁ : StackAccepts TP Ex hooks w a b s₁) (h₂ : StackAccepts TP Ex hooks w b c s₂) :
    StackAccepts TP Ex hooks w a c (s₁ ++ s₂) := by
  revert h₂
  induction h₁ with
  | nil ty => exact fun h₂ => h₂
  | cons head _ ih => exact fun h₂ => .cons head (ih h₂)

/-- Decomposition: a stack over `s₁ ++ s₂` factors through a middle type. -/
theorem stackAccepts_split : ∀ (s₁ s₂ : List ScopeFrame) {a c : EffTy},
    StackAccepts TP Ex hooks w a c (s₁ ++ s₂) →
    ∃ b, StackAccepts TP Ex hooks w a b s₁ ∧ StackAccepts TP Ex hooks w b c s₂
  | [], _, a, _, h => ⟨a, .nil a, h⟩
  | f :: s₁, s₂, _, _, h => by
    rw [List.cons_append] at h
    cases h with
    | cons head tail =>
      obtain ⟨b, h₁, h₂⟩ := stackAccepts_split s₁ s₂ tail
      exact ⟨b, .cons head h₁, h₂⟩

/-- The identity: the empty stack at every type. -/
theorem stackAccepts_id (a : EffTy) : StackAccepts TP Ex hooks w a a [] := .nil a

/-- Pushing one frame on top composes it before the old stack. -/
theorem stackAccepts_push {a b c : EffTy} {f : ScopeFrame} {s : List ScopeFrame}
    (hf : FrameAccepts TP Ex hooks w a b f) (hs : StackAccepts TP Ex hooks w b c s) :
    StackAccepts TP Ex hooks w a c (f :: s) := .cons hf hs

end Stacks

/-! ## 2. The exit judgment, part one and part two

The definitions restate row 107 as ruled (part one) and the audit's part-two condition
(`docs/research/2026-09-30-codex-review-model-probe/probes/SavedFrameTransport.lean`). They
are probe-local; production has neither yet at `efd67af1`. -/

def forbidden1 : Reason Err Defect FiberId Ann → Bool
  | .die defect _ => defect == .badName || defect == .notImplemented
  | _ => false

def forbidden2 (ty : EffTy) : Reason Err Defect FiberId Ann → Bool
  | .die defect _ => defect == .badName || defect == .notImplemented ||
      (defect == .missingService && ty.requires == Env.Requirement.empty)
  | _ => false

def NoShapeDefect1 : ExitV → Prop
  | .success _ => True
  | .failure c => c.reasons.any forbidden1 = false

def NoShapeDefect2 (ty : EffTy) : ExitV → Prop
  | .success _ => True
  | .failure c => c.reasons.any (forbidden2 ty) = false

def ExitOk1 (w : W) (ty : EffTy) (ex : ExitV) : Prop := FitsExit w ty ex ∧ NoShapeDefect1 ex
def ExitOk2 (w : W) (ty : EffTy) (ex : ExitV) : Prop := FitsExit w ty ex ∧ NoShapeDefect2 ty ex

/-- Part one is type-independent in its defect clause, so it composes wherever `FitsExit` does. -/
theorem exitOk1_transport {w : W} {tin tout : EffTy} {ex : ExitV}
    (fits : FitsExit w tin ex → FitsExit w tout ex) (h : ExitOk1 w tin ex) : ExitOk1 w tout ex :=
  ⟨fits h.1, h.2⟩

/-- When the requirement row does not become empty, every reason forbidden at the outer type
was already forbidden at the inner type. -/
theorem forbidden2_mono {tin tout : EffTy}
    (req : tout.requires = Env.Requirement.empty → tin.requires = Env.Requirement.empty)
    (r : Reason Err Defect FiberId Ann) (h : forbidden2 tout r = true) : forbidden2 tin r = true := by
  cases r with
  | fail e ann => exact Bool.noConfusion h
  | interrupt who ann => exact Bool.noConfusion h
  | die defect ann =>
    simp only [forbidden2, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h ⊢
    rcases h with (h | h) | ⟨hd, hr⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨hd, req hr⟩

/-- Part two composes along a frame that does not empty the requirement row. -/
theorem exitOk2_transport {w : W} {tin tout : EffTy} {ex : ExitV}
    (fits : FitsExit w tin ex → FitsExit w tout ex)
    (req : tout.requires = Env.Requirement.empty → tin.requires = Env.Requirement.empty)
    (h : ExitOk2 w tin ex) : ExitOk2 w tout ex := by
  refine ⟨fits h.1, ?_⟩
  cases ex with
  | success v => trivial
  | failure c =>
    have hin : c.reasons.any (forbidden2 tin) = false := h.2
    change c.reasons.any (forbidden2 tout) = false
    rw [List.any_eq_false] at hin ⊢
    intro r hr hout
    exact hin r hr (forbidden2_mono req r hout)

/-! ## 3. The red control: without the requirement condition, part two does not compose -/

def requiredTy : EffTy := ⟨.never, .never, Env.Requirement.single nativeScopeKey⟩
def closedTy : EffTy := EffTy.pure .unit
def missing : CauseV := Cause.die .missingService

theorem same_error : requiredTy.error = closedTy.error := rfl

/-- The error-column transport the loop and iterator protocols carry today (`errors :
tin.error = tout.error`, `Typed/Residual.lean:277,293`) does not transport part two. -/
theorem exitOk2_transport_refuted (w : W) :
    ¬ (∀ (tin tout : EffTy) (ex : ExitV), tin.error = tout.error →
        ExitOk2 w tin ex → ExitOk2 w tout ex) := by
  intro transport
  have inside : ExitOk2 w requiredTy (.failure missing) :=
    ⟨fitsExit_of_clean w requiredTy missing rfl, rfl⟩
  have outside : missing.reasons.any (forbidden2 closedTy) = false :=
    (transport requiredTy closedTy (.failure missing) same_error inside).2
  have hit : missing.reasons.any (forbidden2 closedTy) = true := by decide
  rw [hit] at outside
  exact Bool.noConfusion outside

/-- And the requirement condition is exactly what that frame violates. -/
theorem requirement_condition_fails :
    ¬ (closedTy.requires = Env.Requirement.empty → requiredTy.requires = Env.Requirement.empty) := by
  intro h
  exact absurd (h rfl) (by decide)

end FormalPass.Proofs.FrameCategory

open FormalPass.Proofs.FrameCategory in
#print axioms stackAccepts_append
open FormalPass.Proofs.FrameCategory in
#print axioms stackAccepts_split
open FormalPass.Proofs.FrameCategory in
#print axioms stackAccepts_id
open FormalPass.Proofs.FrameCategory in
#print axioms stackAccepts_push
open FormalPass.Proofs.FrameCategory in
#print axioms exitOk1_transport
open FormalPass.Proofs.FrameCategory in
#print axioms forbidden2_mono
open FormalPass.Proofs.FrameCategory in
#print axioms exitOk2_transport
open FormalPass.Proofs.FrameCategory in
#print axioms exitOk2_transport_refuted
open FormalPass.Proofs.FrameCategory in
#print axioms requirement_condition_fails
