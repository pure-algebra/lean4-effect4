import Effect4.Laws.Effects.Protocol
import Effects.Algebra.Universal

/-!
# Pedigree seat probe (2026-09-30): "extension is additive" at the free monad and the protocol

Research probe, outside every root. Generic over the signature: it imports the tree's layer-0
protocol module (`src/Effect4/Laws/Effects/Protocol.lean`) and, through it, the pinned `Effects`
algebra (`Effects.Algebra.Sum`).

What it checks, each against the note's requirement R2:

1. **Coproduct injections are conservative for protocol typing.** The tree proves the left lift
   (`Typed.inl`) and the two inversions. This adds the converse of the left lift
   (`inl_reflect`, so `inl_iff`) and both directions at the right injection (`inr_lift`,
   `inr_reflect`, `inr_iff`).
2. **A world extension is a projection, and typing transfers along it in two directions under
   two different conditions.** Preservation (`typed_pull_of_typed`) needs only a monotone
   projection. Reflection (`typed_of_typed_pull`) needs the back condition as well (a
   p-morphism of preorders). Without it reflection fails (`reflection_needs_back`, a red
   control). On one world, typing is antitone in the order (`typed_antitone`): a finer order
   keeps every derivation, and widening the order loses one (`order_widening_loses_typing`,
   a red control).
3. **A signature morphism (operations forward, answers backward) transports typing under a
   protocol refinement** (`typed_along`), its program map is a monad morphism (`along_bind`),
   it meets interpretation by restricting the handler (`interpret_along`), and the coproduct
   injection is its instance (`along_inl`). A richer protocol whose promise about an old
   operation is weaker breaks old typing (`post_refinement_needed`, a red control).

Rerun receipts for the existing theorems these build on are at the foot.
-/

set_option autoImplicit false

namespace Research.Pedigree

open Effects
open Effect4.Laws.Effects

universe u u' v w w'

/-! ## 1. The coproduct injections -/

section Coproduct

variable {W : Type w} {S T : Signature.{u, v}} {A : Type v}

/-- Reflection along the left injection: an injected program typed for the sum protocol is
typed for the left protocol, at the same world and result predicate. -/
theorem inl_reflect {o : WorldOrder W} {Ψ₁ : Protocol W S} {Ψ₂ : Protocol W T}
    {Q : W → A → Prop} (p : Program S A) :
    ∀ (w : W), Typed o (Ψ₁.sum Ψ₂) w Q (Program.inl p) → Typed o Ψ₁ w Q p := by
  induction p with
  | pure a =>
    intro w h
    exact Typed.pure (Typed.pure_inv h)
  | vis op k ih =>
    intro w h
    obtain ⟨cert, hpre, hk⟩ := Typed.inl_inv h
    exact Typed.vis cert hpre (fun w' hle ans hpost => ih ans w' (hk w' hle ans hpost))

/-- The left injection is conservative for protocol typing: lifted (`Typed.inl`, in the tree)
and reflected (`inl_reflect`). -/
theorem inl_iff {o : WorldOrder W} {Ψ₁ : Protocol W S} {Ψ₂ : Protocol W T}
    {Q : W → A → Prop} (p : Program S A) (w : W) :
    Typed o (Ψ₁.sum Ψ₂) w Q (Program.inl p) ↔ Typed o Ψ₁ w Q p :=
  ⟨inl_reflect p w, Typed.inl⟩

/-- The right lift, the mirror of the tree's `Typed.inl`, which the tree does not state. -/
theorem inr_lift {o : WorldOrder W} {Ψ₁ : Protocol W S} {Ψ₂ : Protocol W T}
    {Q : W → A → Prop} {p : Program T A} {w : W}
    (h : Typed o Ψ₂ w Q p) : Typed o (Ψ₁.sum Ψ₂) w Q (Program.inr p) := by
  induction h with
  | pure hq => exact Typed.pure hq
  | vis cert hp _ ih =>
    exact Typed.vis (Ψ := Ψ₁.sum Ψ₂) (op := Sum.inr _) cert hp
      (fun w' hle ans hpost => ih w' hle ans hpost)

/-- Reflection along the right injection. -/
theorem inr_reflect {o : WorldOrder W} {Ψ₁ : Protocol W S} {Ψ₂ : Protocol W T}
    {Q : W → A → Prop} (p : Program T A) :
    ∀ (w : W), Typed o (Ψ₁.sum Ψ₂) w Q (Program.inr p) → Typed o Ψ₂ w Q p := by
  induction p with
  | pure a =>
    intro w h
    exact Typed.pure (Typed.pure_inv h)
  | vis op k ih =>
    intro w h
    obtain ⟨cert, hpre, hk⟩ := Typed.inr_inv h
    exact Typed.vis cert hpre (fun w' hle ans hpost => ih ans w' (hk w' hle ans hpost))

theorem inr_iff {o : WorldOrder W} {Ψ₁ : Protocol W S} {Ψ₂ : Protocol W T}
    {Q : W → A → Prop} (p : Program T A) (w : W) :
    Typed o (Ψ₁.sum Ψ₂) w Q (Program.inr p) ↔ Typed o Ψ₂ w Q p :=
  ⟨inr_reflect p w, inr_lift⟩

end Coproduct

/-! ## 2. World extensions as projections -/

section Projection

variable {W : Type w} {W' : Type w'} {S : Signature.{u, v}} {A : Type v}

/-- An old protocol read in a richer world through a projection onto the old world. The old
operations read only the projected part: the frame condition of an additive extension. -/
def pull (Ψ : Protocol W S) (π : W' → W) : Protocol W' S where
  Cert := Ψ.Cert
  pre w op c := Ψ.pre (π w) op c
  post w op c a := Ψ.post (π w) op c a

/-- Preservation: an old derivation at the projected world is a derivation in the richer world
for the pulled-back protocol. Only monotonicity of the projection is used. -/
theorem typed_pull_of_typed {o : WorldOrder W} {o' : WorldOrder W'} {Ψ : Protocol W S}
    (π : W' → W) (mono : ∀ (a b : W'), o'.le a b → o.le (π a) (π b))
    {Q : W → A → Prop} {p : Program S A} {x : W} (h : Typed o Ψ x Q p) :
    ∀ (w : W'), π w = x → Typed o' (pull Ψ π) w (fun y a => Q (π y) a) p := by
  induction h with
  | pure hq =>
    intro w hw
    subst hw
    exact Typed.pure hq
  | vis cert hpre _ ih =>
    intro w hw
    subst hw
    exact Typed.vis cert hpre
      (fun w' hle ans hpost => ih (π w') (mono w w' hle) ans hpost w' rfl)

/-- Reflection: a richer-world derivation of an old program is an old derivation at the
projected world, when every old later world of the projection is the projection of a richer
later world (the back condition). -/
theorem typed_of_typed_pull {o : WorldOrder W} {o' : WorldOrder W'} {Ψ : Protocol W S}
    (π : W' → W) (back : ∀ (a : W') (y : W), o.le (π a) y → ∃ b, o'.le a b ∧ π b = y)
    {Q' : W' → A → Prop} {Q : W → A → Prop} (hQ : ∀ y a, Q' y a → Q (π y) a)
    {p : Program S A} {w : W'} (h : Typed o' (pull Ψ π) w Q' p) : Typed o Ψ (π w) Q p := by
  induction h with
  | pure hq => exact Typed.pure (hQ _ _ hq)
  | @vis w₀ _ op _ cert hpre _ ih =>
    exact Typed.vis cert hpre (fun y hle ans hpost => by
      obtain ⟨b, hb, hby⟩ := back w₀ y hle
      subst hby
      exact ih b hb ans hpost hQ)

/-! ### Reflection fails without the back condition -/

/-- The old world: naturals ordered by `≤`. -/
def natLe : WorldOrder Nat := ⟨fun a b => a ≤ b, Nat.le_refl, Nat.le_trans⟩

/-- The richer world: the same carrier, ordered discretely; the identity is monotone into
`natLe` and has no back condition. -/
def natEq : WorldOrder Nat := ⟨fun a b => a = b, fun _ => rfl, fun h₁ h₂ => h₁.trans h₂⟩

/-- One operation with a unit answer. -/
def One : Signature.{0, 0} := ⟨Unit, fun _ => Unit⟩

/-- Every call allowed, every answer allowed. -/
def openProtocol : Protocol Nat One := Protocol.plain (fun _ _ => True) (fun _ _ _ => True)

/-- One call, then return. -/
abbrev oneStep : Program One Unit := Program.vis () (fun _ => Program.pure ())

/-- A result predicate that holds only at world `0`. -/
def atZero : Nat → Unit → Prop := fun y _ => y = 0

theorem natEq_le_natLe : ∀ (a b : Nat), natEq.le a b → natLe.le (id a) (id b) := by
  intro a b h
  have heq : a = b := h
  subst heq
  exact Nat.le_refl a

/-- Typed in the richer world: the only later world of `0` is `0`. -/
theorem rich_typed : Typed natEq (pull openProtocol id) 0 (fun y a => atZero (id y) a) oneStep :=
  Typed.vis PUnit.unit trivial (fun w' hle _ _ => by
    have heq : 0 = w' := hle
    subst heq
    exact Typed.pure rfl)

/-- Untyped in the old world: `1` is a later world of `0`, where the result predicate fails. -/
theorem old_untyped : ¬ Typed natLe openProtocol (id 0) atZero oneStep := by
  intro h
  cases h with
  | vis cert _ hk =>
    have h1 := hk 1 (Nat.zero_le 1) () trivial
    have h2 := Typed.pure_inv h1
    have hz : (1 : Nat) = 0 := h2
    exact Nat.noConfusion hz

/-- The projection is monotone, the richer derivation exists, and the old one does not. So
`typed_of_typed_pull` cannot drop its back condition. -/
theorem reflection_needs_back :
    (∀ (a b : Nat), natEq.le a b → natLe.le (id a) (id b)) ∧
    Typed natEq (pull openProtocol id) 0 (fun y a => atZero (id y) a) oneStep ∧
    ¬ Typed natLe openProtocol (id 0) atZero oneStep :=
  ⟨natEq_le_natLe, rich_typed, old_untyped⟩

/-- On one world, typing is antitone in the order: a finer order (fewer later worlds) keeps
every derivation. -/
theorem typed_antitone {o o' : WorldOrder W} (sub : ∀ (a b : W), o'.le a b → o.le a b)
    {Ψ : Protocol W S} {Q : W → A → Prop} {p : Program S A} {w : W}
    (h : Typed o Ψ w Q p) : Typed o' Ψ w Q p := by
  induction h with
  | pure hq => exact Typed.pure hq
  | @vis w₀ _ op _ cert hpre _ ih =>
    exact Typed.vis cert hpre (fun w' hle ans hpost => ih w' (sub w₀ w' hle) ans hpost)

/-- Typed under the discrete order. -/
theorem discrete_typed : Typed natEq openProtocol 0 atZero oneStep :=
  Typed.vis PUnit.unit trivial (fun w' hle _ _ => by
    have heq : 0 = w' := hle
    subst heq
    exact Typed.pure rfl)

/-- Widening the order (more later worlds) loses typing: the discrete order is contained in
`≤`, the program is typed under the first and not under the second. -/
theorem order_widening_loses_typing :
    (∀ (a b : Nat), natEq.le a b → natLe.le a b) ∧
    Typed natEq openProtocol 0 atZero oneStep ∧ ¬ Typed natLe openProtocol 0 atZero oneStep :=
  ⟨natEq_le_natLe, discrete_typed, old_untyped⟩

end Projection

/-! ## 3. Signature morphisms -/

section Morphism

variable {S : Signature.{u, v}} {T : Signature.{u', v}} {A : Type v}

/-- A signature morphism: operations forward, answers backward (a container morphism). -/
structure SigMorph (S : Signature.{u, v}) (T : Signature.{u', v}) where
  op : S.Op → T.Op
  ans : (o : S.Op) → T.Answer (op o) → S.Answer o

/-- The program map a signature morphism induces. -/
def along (φ : SigMorph S T) : Program S A → Program T A
  | .pure a => .pure a
  | .vis o k => .vis (φ.op o) (fun b => along φ (k (φ.ans o b)))

/-- The program map is a monad morphism: it commutes with sequencing. -/
theorem along_bind {B : Type v} (φ : SigMorph S T) (p : Program S A) (f : A → Program S B) :
    along φ (p.bind f) = (along φ p).bind (fun a => along φ (f a)) := by
  induction p with
  | pure a => rfl
  | vis o k ih =>
    exact congrArg (Program.vis (φ.op o)) (funext fun b => ih (φ.ans o b))

/-- A handler for the larger signature, read along the morphism. -/
def restrict {M : Type v → Type w} [Functor M] (h : Handler T M) (φ : SigMorph S T) :
    Handler S M :=
  ⟨fun o => φ.ans o <$> h.handle (φ.op o)⟩

/-- Meaning is conservative along the morphism: interpreting the mapped program is
interpreting the old program with the restricted handler. -/
theorem interpret_along {M : Type v → Type w} [Monad M] [LawfulMonad M]
    (h : Handler T M) (φ : SigMorph S T) (p : Program S A) :
    interpret h (along φ p) = interpret (restrict h φ) p := by
  induction p with
  | pure a => rfl
  | vis o k ih =>
    show (h.handle (φ.op o) >>= fun b => interpret h (along φ (k (φ.ans o b)))) =
      ((φ.ans o <$> h.handle (φ.op o)) >>= fun a => interpret (restrict h φ) (k a))
    rw [bind_map_left]
    exact bind_congr (fun b => ih (φ.ans o b))

/-- Typing is transported along the morphism when the larger protocol refines the old one:
its demand follows from the old demand, its promise implies the old promise. -/
theorem typed_along {W : Type w} {o : WorldOrder W} {Ψ : Protocol W S} {Ψ' : Protocol W T}
    (φ : SigMorph S T) (cert : (op : S.Op) → Ψ.Cert op → Ψ'.Cert (φ.op op))
    (hpre : ∀ w op c, Ψ.pre w op c → Ψ'.pre w (φ.op op) (cert op c))
    (hpost : ∀ w op c b, Ψ'.post w (φ.op op) (cert op c) b → Ψ.post w op c (φ.ans op b))
    {Q : W → A → Prop} {p : Program S A} {w : W} (h : Typed o Ψ w Q p) :
    Typed o Ψ' w Q (along φ p) := by
  induction h with
  | pure hq => exact Typed.pure hq
  | @vis w₀ _ op _ c hp _ ih =>
    exact Typed.vis (cert op c) (hpre w₀ op c hp)
      (fun w' hle b hb => ih w' hle (φ.ans op b) (hpost w' op c b hb))

end Morphism

section Instance

variable {S T : Signature.{u, v}} {A : Type v}

/-- The left coproduct injection as a signature morphism. -/
def inlMorph : SigMorph S (Signature.sum S T) := ⟨Sum.inl, fun _ b => b⟩

/-- Its program map is the package's `Program.inl`. -/
theorem along_inl (p : Program S A) : along (inlMorph (T := T)) p = Program.inl p := by
  induction p with
  | pure a => rfl
  | vis o k ih =>
    exact congrArg (Program.vis (signature := Signature.sum S T) (Sum.inl o)) (funext ih)

end Instance

/-! ### A richer protocol that promises less about an old operation breaks old typing -/

section PostRefinement

/-- One operation answering a boolean. -/
def Ask : Signature.{0, 0} := ⟨Unit, fun _ => Bool⟩

def idMorph : SigMorph Ask Ask := ⟨id, fun _ b => b⟩

def unitOrder : WorldOrder Unit := ⟨fun _ _ => True, fun _ => trivial, fun _ _ => trivial⟩

/-- The old protocol promises the answer `true`. -/
def onlyTrue : Protocol Unit Ask := Protocol.plain (fun _ _ => True) (fun _ _ b => b = true)

/-- The richer protocol promises nothing about the answer. -/
def anyAnswer : Protocol Unit Ask := Protocol.plain (fun _ _ => True) (fun _ _ _ => True)

/-- Ask, then return the answer. -/
abbrev askThen : Program Ask Bool := Program.vis () (fun b => Program.pure b)

def isTrue : Unit → Bool → Prop := fun _ b => b = true

theorem old_typed : Typed unitOrder onlyTrue () isTrue askThen :=
  Typed.vis PUnit.unit trivial (fun _ _ _ hb => Typed.pure hb)

theorem richer_untyped : ¬ Typed unitOrder anyAnswer () isTrue (along idMorph askThen) := by
  intro h
  cases h with
  | vis cert _ hk =>
    have h1 := hk () trivial false trivial
    have h2 := Typed.pure_inv h1
    have hz : false = true := h2
    exact Bool.noConfusion hz

/-- The post refinement premise of `typed_along` fails for this pair, and its conclusion fails
with it. -/
theorem post_refinement_needed :
    ¬ (∀ b, anyAnswer.post () () PUnit.unit b → onlyTrue.post () () PUnit.unit (idMorph.ans () b)) ∧
    Typed unitOrder onlyTrue () isTrue askThen ∧
    ¬ Typed unitOrder anyAnswer () isTrue (along idMorph askThen) := by
  refine ⟨fun h => ?_, old_typed, richer_untyped⟩
  have hz : false = true := h false trivial
  exact Bool.noConfusion hz

end PostRefinement

end Research.Pedigree

/-! ## Receipts -/

-- the new theorems
#print axioms Research.Pedigree.inl_reflect
#print axioms Research.Pedigree.inl_iff
#print axioms Research.Pedigree.inr_lift
#print axioms Research.Pedigree.inr_reflect
#print axioms Research.Pedigree.inr_iff
#print axioms Research.Pedigree.typed_pull_of_typed
#print axioms Research.Pedigree.typed_of_typed_pull
#print axioms Research.Pedigree.natEq_le_natLe
#print axioms Research.Pedigree.rich_typed
#print axioms Research.Pedigree.old_untyped
#print axioms Research.Pedigree.reflection_needs_back
#print axioms Research.Pedigree.typed_antitone
#print axioms Research.Pedigree.discrete_typed
#print axioms Research.Pedigree.order_widening_loses_typing
#print axioms Research.Pedigree.old_typed
#print axioms Research.Pedigree.richer_untyped
#print axioms Research.Pedigree.post_refinement_needed
#print axioms Research.Pedigree.along_bind
#print axioms Research.Pedigree.interpret_along
#print axioms Research.Pedigree.typed_along
#print axioms Research.Pedigree.along_inl

-- the existing theorems they build on, rerun here
#print axioms Effect4.Laws.Effects.Typed.inl
#print axioms Effect4.Laws.Effects.Typed.inl_inv
#print axioms Effect4.Laws.Effects.Typed.inr_inv
#print axioms Effect4.Laws.Effects.Typed.mono
#print axioms Effects.interpret_inl
#print axioms Effects.interpret_inr
#print axioms Effects.Program.inl_injective
#print axioms Effects.Program.inl_bind
#print axioms Effects.interpret_pinned

namespace Research.Pedigree.Collapse
open Effects
def S : Signature.{0,0} := ⟨Bool, fun _ => Unit⟩
def T : Signature.{0,0} := ⟨Unit, fun _ => Unit⟩
def phi : Research.Pedigree.SigMorph S T := ⟨fun _ => (), fun _ b => b⟩
def p : Program S Unit := .vis false (fun _ => .pure ())
def q : Program S Unit := .vis true (fun _ => .pure ())
theorem same : Research.Pedigree.along phi p = Research.Pedigree.along phi q := rfl
theorem different : p ≠ q := by intro h; cases h
theorem not_injective : ¬ Function.Injective (@Research.Pedigree.along S T Unit phi) :=
  fun h => different (h same)
#print axioms same
#print axioms different
#print axioms not_injective
end Research.Pedigree.Collapse
