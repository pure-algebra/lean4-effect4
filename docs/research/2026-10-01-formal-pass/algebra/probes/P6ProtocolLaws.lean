import Effect4.Laws.Program.Typed.Residual

/-!
# P6 — the protocol layer's missing laws, and the bind rule's side condition

Formal pass, seat ALGEBRA, 2026-10-01. Hazel's protocol logic (de Vilhena 2022, Def. 2.4-2.8,
rules Bind and Monotonicity, as `docs/research/2026-09-05-effects-papers-review.md` §1.3 reads
them) expects of a protocol-typed weakest precondition: weakening of the result (`Typed.widen`,
in the tree), sequencing (`Typed.bind`, in the tree), world weakening (`Typed.mono`, in the tree),
the coproduct lift on both sides (only `Typed.inl` is in the tree), and monotonicity in the
protocol order (absent from the tree; the pedigree seat's `typed_along` is a research probe).

Proved here: `Typed.inr` (the mirror), `Typed.refine` (monotonicity in the protocol order:
demands may weaken, promises may strengthen). Red control: the concrete judgment `TypedProg` is
not closed under bind, because a closing marker (`unguard`) carries an exit at the current type.
This is Hazel's own side condition: its Bind rule holds for neutral contexts only (Fig. 2.4;
papers review G8). M5's elaboration lemma therefore needs per-construct lemmas or a bind lemma
with a neutrality premise, not a general bind.
-/

set_option autoImplicit false

namespace FormalPass.Algebra.P6

open Effects
open Effect4.Laws.Effects

universe u v w

section Generic

variable {W : Type w} {S T : Signature.{u, v}} {A : Type v}

/-- **The right injection lifts typing**, the mirror of `Typed.inl`. -/
theorem Typed.inr {o : WorldOrder W} {Ψ₁ : Protocol W S} {Ψ₂ : Protocol W T}
    {Q : W → A → Prop} {p : Program T A} {w : W}
    (h : Typed o Ψ₂ w Q p) : Typed o (Ψ₁.sum Ψ₂) w Q p.inr := by
  induction h with
  | pure h => exact .pure h
  | vis cert hp _ ih =>
    exact .vis (Ψ := Ψ₁.sum Ψ₂) (op := .inr _) cert hp
      (fun w' hle ans hpost => ih w' hle ans hpost)

/-- The protocol order: a certificate map under which every demand of `Ψ` is a demand of `Ψ'`
and every promise of `Ψ'` is a promise of `Ψ`. -/
structure Refines (Ψ Ψ' : Protocol W S) where
  cert : ∀ op, Ψ.Cert op → Ψ'.Cert op
  pre : ∀ w op c, Ψ.pre w op c → Ψ'.pre w op (cert op c)
  post : ∀ w op c ans, Ψ'.post w op (cert op c) ans → Ψ.post w op c ans

/-- **Monotonicity in the protocol order** (Hazel's Monotonicity, protocol half). -/
theorem Typed.refine {o : WorldOrder W} {Ψ Ψ' : Protocol W S} (r : Refines Ψ Ψ')
    {Q : W → A → Prop} {p : Program S A} {w : W}
    (h : Typed o Ψ w Q p) : Typed o Ψ' w Q p := by
  induction h with
  | pure h => exact .pure h
  | vis cert hp _ ih =>
    exact .vis (r.cert _ cert) (r.pre _ _ _ hp)
      (fun w' hle ans hpost => ih w' hle ans (r.post _ _ _ _ hpost))

end Generic

section Concrete

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

/-- **Red control: `TypedProg` is not closed under bind.** A program whose last step closes a
scope at `nat` is typed at `nat`; every continuation into `unit` is typed; their sequence is
not typed at `unit`, because the closing marker's exit must fit the current type. -/
theorem typedProg_not_bind_closed (root : ProgramSource) (w : Typed.World) :
    ∃ (mid ty : EffTy) (p : RProgram) (k : ExitV → RProgram),
      TypedProg root w mid p ∧
      (∀ w', w.leHost w' → ∀ ex, FitsExit w' mid ex → TypedProg root w' ty (k ex)) ∧
      ¬ TypedProg root w ty (p.bind k) := by
  let ex0 : ExitV := .success (Val.nat 0)
  refine ⟨EffTy.pure .nat, EffTy.pure .unit, .vis (.inr (.unguard ex0)) Program.pure,
    fun _ => .pure (.success Val.unit), ?_, ?_, ?_⟩
  · refine .unguard ?_
    rw [fitsExit_success_iff]
    exact trivial
  · intro w' _ ex _
    refine .pure ?_
    rw [fitsExit_success_iff]
    exact trivial
  · intro h
    change TypedProg root w (EffTy.pure .unit) (.vis (.inr (.unguard ex0)) _) at h
    cases h with
    | fiber _ notUnguard _ _ _ _ _ => exact notUnguard ex0 rfl
    | unguard payload =>
      rw [fitsExit_success_iff] at payload
      exact payload

end Concrete

end FormalPass.Algebra.P6

#print axioms FormalPass.Algebra.P6.Typed.inr
#print axioms FormalPass.Algebra.P6.Typed.refine
#print axioms FormalPass.Algebra.P6.typedProg_not_bind_closed
