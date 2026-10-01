import Effect4.Laws.Effects.Protocol
import Effects.Algebra.Universal

/-!
# Pedigree verifier probe (2026-09-30): the C4 statement as one iff, and the two premises the
# seat's red controls do not cover

Research probe, outside every root. It does not import the seat's `Conservativity.lean` (not a
module on the load path); `pull` and the two transfer lemmas are restated here so the combined
statement is checked from the tree's own `Typed` (`src/Effect4/Laws/Effects/Protocol.lean:45`).

1. `c4_iff`: the seat's C4 as written in its note (§3.1), `Typed_Σ' w' Q' (ι* p) ↔ Typed_Σ (π w') Q p`,
   for the coproduct injection with a pulled-back old protocol and a monotone projection with the
   back condition. The seat proved the pieces separately; this checks they compose.
2. `mono_needed` (red control): preservation fails for a projection that is not monotone.
   The seat's `typed_pull_of_typed` uses monotonicity but has no control for it.
3. `pre_refinement_needed` (red control): transport along a morphism fails when the richer
   protocol demands more of an old operation. The seat's `typed_along` uses this premise but
   has a control only for the promise (`post_refinement_needed`).
-/

set_option autoImplicit false

namespace Research.PedigreeVerify

open Effects
open Effect4.Laws.Effects

universe u v w w'

section Combined

variable {W : Type w} {W' : Type w'} {S T : Signature.{u, v}} {A : Type v}

/-- An old protocol read through a projection of richer worlds (the seat's `pull`). -/
def pull (Ψ : Protocol W S) (π : W' → W) : Protocol W' S where
  Cert := Ψ.Cert
  pre w op c := Ψ.pre (π w) op c
  post w op c a := Ψ.post (π w) op c a

theorem pull_of {o : WorldOrder W} {o' : WorldOrder W'} {Ψ : Protocol W S}
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

theorem of_pull {o : WorldOrder W} {o' : WorldOrder W'} {Ψ : Protocol W S}
    (π : W' → W) (back : ∀ (a : W') (y : W), o.le (π a) y → ∃ b, o'.le a b ∧ π b = y)
    {Q' : W' → A → Prop} {Q : W → A → Prop} (hQ : ∀ y a, Q' y a → Q (π y) a)
    {p : Program S A} {w : W'}
    (h : Typed o' (pull Ψ π) w Q' p) : Typed o Ψ (π w) Q p := by
  induction h with
  | pure hq => exact Typed.pure (hQ _ _ hq)
  | @vis w₀ _ op _ cert hpre _ ih =>
    exact Typed.vis cert hpre (fun y hle ans hpost => by
      obtain ⟨b, hb, hby⟩ := back w₀ y hle
      subst hby
      exact ih b hb ans hpost hQ)

theorem inl_reflect' {o : WorldOrder W'} {Ψ₁ : Protocol W' S} {Ψ₂ : Protocol W' T}
    {Q : W' → A → Prop} (p : Program S A) :
    ∀ (w : W'), Typed o (Ψ₁.sum Ψ₂) w Q (Program.inl p) → Typed o Ψ₁ w Q p := by
  induction p with
  | pure a =>
    intro w h
    exact Typed.pure (Typed.pure_inv h)
  | vis op k ih =>
    intro w h
    obtain ⟨cert, hpre, hk⟩ := Typed.inl_inv h
    exact Typed.vis cert hpre (fun w' hle ans hpost => ih ans w' (hk w' hle ans hpost))

/-- **C4 as one statement.** An extension that adds a summand `T` with its own protocol `Ψn`,
reads the old protocol through `π`, and has a monotone `π` with the back condition, types an old
program exactly when the old world did. -/
theorem c4_iff {o : WorldOrder W} {o' : WorldOrder W'} {Ψ : Protocol W S} {Ψn : Protocol W' T}
    (π : W' → W) (mono : ∀ (a b : W'), o'.le a b → o.le (π a) (π b))
    (back : ∀ (a : W') (y : W), o.le (π a) y → ∃ b, o'.le a b ∧ π b = y)
    {Q : W → A → Prop} (p : Program S A) (w : W') :
    Typed o' ((pull Ψ π).sum Ψn) w (fun y a => Q (π y) a) (Program.inl p) ↔
      Typed o Ψ (π w) Q p :=
  ⟨fun h => of_pull π back (fun _ _ hq => hq) (inl_reflect' p w h),
   fun h => Typed.inl (pull_of π mono h w rfl)⟩

end Combined

/-! ## Red control: preservation needs a monotone projection -/

section MonoNeeded

/-- The old world: two points, ordered discretely. -/
def boolEq : WorldOrder Bool := ⟨fun a b => a = b, fun _ => rfl, fun h₁ h₂ => h₁.trans h₂⟩

/-- The richer world: the naturals under `≤`. -/
def natLe : WorldOrder Nat := ⟨fun a b => a ≤ b, Nat.le_refl, Nat.le_trans⟩

/-- A projection that is not monotone: `0 ≤ 1` but `false` and `true` are unrelated. -/
def flip : Nat → Bool
  | 0 => false
  | _ + 1 => true

def One : Signature.{0, 0} := ⟨Unit, fun _ => Unit⟩

def openBool : Protocol Bool One := Protocol.plain (fun _ _ => True) (fun _ _ _ => True)

abbrev oneStep : Program One Unit := Program.vis () (fun _ => Program.pure ())

def atFalse : Bool → Unit → Prop := fun y _ => y = false

theorem flip_not_mono : ¬ ∀ (a b : Nat), natLe.le a b → boolEq.le (flip a) (flip b) := by
  intro h
  have h01 : flip 0 = flip 1 := h 0 1 (Nat.zero_le 1)
  exact Bool.noConfusion h01

/-- Typed in the old world: the only later world of `false` is `false`. -/
theorem old_typed_at_false : Typed boolEq openBool false atFalse oneStep :=
  Typed.vis PUnit.unit trivial (fun w' hle _ _ => by
    have heq : false = w' := hle
    subst heq
    exact Typed.pure rfl)

/-- Untyped once pulled along `flip` at `0`: `1` is a later world and projects to `true`. -/
theorem pulled_untyped :
    ¬ Typed natLe (pull openBool flip) 0 (fun y a => atFalse (flip y) a) oneStep := by
  intro h
  cases h with
  | vis cert _ hk =>
    have h1 := hk 1 (Nat.zero_le 1) () trivial
    have h2 := Typed.pure_inv h1
    have hz : flip 1 = false := h2
    exact Bool.noConfusion hz

/-- The old derivation exists at `flip 0`, the projection is not monotone, and the pulled
derivation does not exist: `pull_of` cannot drop its monotonicity premise. -/
theorem mono_needed :
    (¬ ∀ (a b : Nat), natLe.le a b → boolEq.le (flip a) (flip b)) ∧
    Typed boolEq openBool (flip 0) atFalse oneStep ∧
    ¬ Typed natLe (pull openBool flip) 0 (fun y a => atFalse (flip y) a) oneStep :=
  ⟨flip_not_mono, old_typed_at_false, pulled_untyped⟩

end MonoNeeded

/-! ## Red control: transport along a morphism needs the demand refinement -/

section PreNeeded

def unitOrder : WorldOrder Unit := ⟨fun _ _ => True, fun _ => trivial, fun _ _ => trivial⟩

def Ask : Signature.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- The old protocol demands nothing. -/
def askFree : Protocol Unit Ask := Protocol.plain (fun _ _ => True) (fun _ _ _ => True)

/-- The richer protocol demands something no world satisfies. -/
def askNever : Protocol Unit Ask := Protocol.plain (fun _ _ => False) (fun _ _ _ => True)

abbrev askThen : Program Ask Bool := Program.vis () (fun b => Program.pure b)

def anyResult : Unit → Bool → Prop := fun _ _ => True

theorem free_typed : Typed unitOrder askFree () anyResult askThen :=
  Typed.vis PUnit.unit trivial (fun _ _ _ _ => Typed.pure trivial)

theorem never_untyped : ¬ Typed unitOrder askNever () anyResult askThen := by
  intro h
  cases h with
  | vis _ hpre _ => exact hpre

/-- The demand premise of a transport (`old pre → new pre`) fails for this pair, and the
transported typing fails with it (the morphism is the identity, so `along` is the identity). -/
theorem pre_refinement_needed :
    ¬ (∀ w op c, askFree.pre w op c → askNever.pre w op c) ∧
    Typed unitOrder askFree () anyResult askThen ∧
    ¬ Typed unitOrder askNever () anyResult askThen :=
  ⟨fun h => h () () PUnit.unit trivial, free_typed, never_untyped⟩

end PreNeeded

end Research.PedigreeVerify

#print axioms Research.PedigreeVerify.pull_of
#print axioms Research.PedigreeVerify.of_pull
#print axioms Research.PedigreeVerify.inl_reflect'
#print axioms Research.PedigreeVerify.c4_iff
#print axioms Research.PedigreeVerify.flip_not_mono
#print axioms Research.PedigreeVerify.old_typed_at_false
#print axioms Research.PedigreeVerify.pulled_untyped
#print axioms Research.PedigreeVerify.mono_needed
#print axioms Research.PedigreeVerify.free_typed
#print axioms Research.PedigreeVerify.never_untyped
#print axioms Research.PedigreeVerify.pre_refinement_needed
