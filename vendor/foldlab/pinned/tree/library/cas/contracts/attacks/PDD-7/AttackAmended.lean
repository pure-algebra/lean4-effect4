import Cas.Backend.SumAlgebra

/-!
# PDD-7 — the breaker's re-run against the amended castle

## Subject

```
AMENDED    e1ceb205  PDD-7: module fixes for both holes, and eight
                     results adopted from the record
  packet   ac3a0ece  PDD-7: packet amendments for the breaker's two holes
ORIGINAL   d714ef14  the castle this record's `Attack.lean` was written
                     against; that file is UNEDITED and stays the record
                     against it
ATTACK     contracts/attacks/PDD-7/AttackAmended.lean   (this file)
BRANCH     attack/opus-cc-mac/pdd-7
```

## What this file IS

The mechanical half of the re-run row appended to `RESULTS.md`. Three
jobs, and nothing else:

- **§A — the closures, checked rather than read.** `Prog.inl_unique`'s
  proof term is printed, so "now a corollary of `inl_unique_one_target`"
  is verified structurally instead of taken from a docstring. HOLE-2's
  adversary is checked to be in the castle's own `Adversary` namespace
  with its two refutations, which is what makes the boundary
  build-enforced.
- **§B — the eight adopted results, re-elaborated.** Each of this
  breaker's original statements is inhabited BY the castle's adopted
  declaration. If a statement had been weakened in adoption, the
  `example` would not elaborate.
- **§C — the fresh probe.** One finding: the HOLE-1 correction is
  applied to ONE of the three categoricity rows. `Prog.inr_unique` and
  the newly adopted ADQ-L30 both still state only the ∀-quantified form
  whose proof consumes one instance. The missing halves are supplied
  here so folding them in is a copy rather than a derivation.

## What this file is NOT

NOT part of any Lake target, and it must not become one. It adds
nothing to `Cas`, moves no bytes, touches no ledger. `Attack.lean`
beside it is unedited; deleting or amending that file would destroy the
record against `d714ef14`.

## How to elaborate it

From `library/cas`:

```
lake env lean contracts/attacks/PDD-7/AttackAmended.lean
```

Expected: elaborates clean, no `sorry`. `Attack.lean` also still
elaborates clean against `e1ceb205` — verified, and expected: its
theorems are about the law set as it stood, and extending a law set
cannot falsify a theorem about the old one. That is the same correction
PDD-1's breaker had to make to its own predicted close condition.
-/

namespace PDD7Amended
open Cas Cas.Lang

universe u v

theorem handlerExt {S : Sig} {M : Type → Type v} {h g : Handler S M}
    (hyp : ∀ op, h.handle op = g.handle op) : h = g := by
  cases h; cases g; exact congrArg Handler.mk (funext hyp)

/-! ## §A — the closures, checked

### HOLE-1: is `Prog.inl_unique` REALLY a corollary now?

Printed, not read off the prose. The proof term must mention
`inl_unique_one_target`; a cosmetic fix that kept the old `rwa` block
and merely reordered the docstrings would show here. -/

#print Cas.Lang.Prog.inl_unique
#print Cas.Lang.inl_unique_one_target
#print Cas.Lang.syntactic_hyp_iff

/-- The narrowed law is primary in the strong sense: the ∀-quantified
form factors through it, at the single instance. Re-derived here so the
factoring is this record's claim too, not only the castle's. -/
theorem inl_unique_factors_through_one_target {S T : Sig}
    (ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A)
    (hι : ∀ (M : Type → Type) [Monad M] [LawfulMonad M]
            (h : Handler S M) (g : Handler T M) {A : Type} (p : Prog S A),
            interpret (h.sum g) (ι p) = interpret h p)
    {A : Type} (p : Prog S A) : ι p = Prog.inl p :=
  inl_unique_one_target ι
    (fun {_} q => hι (Prog (S ⊕ₛ T)) (inlHandler S T) (inrHandler S T) q) p

/-! ### HOLE-2: the adversary is inside the castle now

`badHandleLlm` living in `Cas.Lang.Adversary` is what makes L31's
boundary build-enforced: relaxing the claim back means deleting a
theorem, which is a red build rather than a prose edit. -/

example (oracle : String → String) {A : Type u} (p : Prog CasSig A) :
    Adversary.badHandleLlm oracle (liftCas p) = p :=
  Adversary.badHandleLlm_liftCas oracle p

example :
    Adversary.badHandleLlm Adversary.wildOracle (infer "x")
      ≠ interpret (idHandler.sum (llmOracleHandler Adversary.wildOracle)) (infer "x") :=
  Adversary.badHandleLlm_not_interpret

/-! ## §B — the eight adopted results, re-elaborated

Each `example` states what THIS record proved and discharges it with the
castle's adopted declaration. Elaboration is the check that nothing was
weakened on the way in. -/

/-- 1. `syntactic_hyp_iff`. -/
example {S T : Sig} (ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A)
    {A : Type} (p : Prog S A) :
    (interpret ((inlHandler S T).sum (inrHandler S T)) (ι p)
        = interpret (inlHandler S T) p)
      ↔ ι p = Prog.inl p :=
  syntactic_hyp_iff ι p

/-- 2. `inl_unique_one_target`. -/
example {S T : Sig} (ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A)
    (hι : ∀ {A : Type} (p : Prog S A),
        interpret ((inlHandler S T).sum (inrHandler S T)) (ι p)
          = interpret (inlHandler S T) p)
    {A : Type} (p : Prog S A) : ι p = Prog.inl p :=
  inl_unique_one_target ι hι p

/-- 3. `doubleInl_interpret_inl_Id`. -/
example {S T : Sig} (h : Handler S Id) (g : Handler T Id)
    {A : Type} (p : Prog S A) :
    interpret (h.sum g) (Adversary.doubleInl (T := T) p) = interpret h p :=
  Adversary.doubleInl_interpret_inl_Id h g p

/-- 4. `narrowing_to_Id_fails`. -/
example :
    ¬ (∀ (S T : Sig) (ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A),
        (∀ (h : Handler S Id) (g : Handler T Id) {A : Type} (p : Prog S A),
           interpret (h.sum g) (ι p) = interpret h p) →
        ∀ {A : Type} (p : Prog S A), ι p = Prog.inl p) :=
  Adversary.narrowing_to_Id_fails

/-- 5. `dup` with `dup_bind`, `dup_injective`, `doubleInl_factors` — and
the two derived laws that were the point of the factorization. -/
example {S T : Sig} {A : Type u} (p : Prog S A) :
    Adversary.doubleInl (T := T) p = Prog.inl (Adversary.dup p) :=
  Adversary.doubleInl_factors p

example {S : Sig} {A B : Type u} (p : Prog S A) (f : A → Prog S B) :
    Adversary.dup (p.bind f) = (Adversary.dup p).bind (fun a => Adversary.dup (f a)) :=
  Adversary.dup_bind p f

example {S : Sig} {A : Type u} (p q : Prog S A) :
    Adversary.dup p = Adversary.dup q → p = q :=
  Adversary.dup_injective p q

example {S T : Sig} {A B : Type u} (p : Prog S A) (f : A → Prog S B) :
    Adversary.doubleInl (T := T) (p.bind f)
      = (Adversary.doubleInl (T := T) p).bind
          (fun a => Adversary.doubleInl (T := T) (f a)) :=
  Adversary.doubleInl_bind' p f

example {S T : Sig} {A : Type u} (p q : Prog S A) :
    Adversary.doubleInl (T := T) p = Adversary.doubleInl (T := T) q → p = q :=
  Adversary.doubleInl_injective' p q

/-- 6. `llmOracleHandler_unique` (ADQ-L30). -/
example (oracle : String → String) (g : Handler LlmSig (Prog CasSig))
    (hg : ∀ (A : Type) (p : Prog AgentSig A),
        p.handleLlm oracle = interpret (idHandler.sum g) p) :
    g = llmOracleHandler oracle :=
  llmOracleHandler_unique oracle g hg

/-- 7. `handleLlm_bind` (L32). -/
example (oracle : String → String) {A B : Type}
    (p : Prog AgentSig A) (f : A → Prog AgentSig B) :
    (p.bind f).handleLlm oracle
      = (p.handleLlm oracle).bind (fun a => (f a).handleLlm oracle) :=
  handleLlm_bind oracle p f

/-! 8. `badHandleLlm` with its two refutations — discharged in §A. -/

/-! ## §C — the fresh probe: the correction reached one of three rows

HOLE-1 was not a fact about `Prog.inl`. It was a fact about a PROOF
SHAPE: a categoricity whose hypothesis is universally quantified while
its proof consumes one instance, at which the hypothesis is equivalent
to the conclusion. The fix pass corrected the row where the breaker
pointed and left the same shape standing in the two rows it did not.

`ADQ-SUM` is exempt and provably so — `Handler.sum_unique`'s premises
are already pointwise-minimal (`Attack.lean` §2, `sum_unique_iff` is an
equivalence). The other two are not.

Nothing below is false in the castle, and no adversary is admitted.
This is a CONSISTENCY finding: the amended packet says the ADQ block is
"now complete across all three definitions the slice touches", and it is
— but only one of the three carries the corrected form. -/

/-! ### C1 — the `inr` mirror the fix pass did not write -/

theorem syntactic_hyp_iff_inr {S T : Sig}
    (ι : {A : Type} → Prog T A → Prog (S ⊕ₛ T) A) {A : Type} (q : Prog T A) :
    (interpret ((inlHandler S T).sum (inrHandler S T)) (ι q)
        = interpret (inrHandler S T) q)
      ↔ ι q = Prog.inr q := by
  rw [sum_inlHandler_inrHandler, interpret_id, interpret_inrHandler]

theorem inr_unique_one_target {S T : Sig}
    (ι : {A : Type} → Prog T A → Prog (S ⊕ₛ T) A)
    (hι : ∀ {A : Type} (q : Prog T A),
        interpret ((inlHandler S T).sum (inrHandler S T)) (ι q)
          = interpret (inrHandler S T) q)
    {A : Type} (q : Prog T A) : ι q = Prog.inr q :=
  (syntactic_hyp_iff_inr ι q).mp (hι q)

/-- `Prog.inr_unique` is the corollary, by the same two lines as on the
left. The castle still proves it by the original one-shot `rwa`. -/
theorem inr_unique_is_corollary {S T : Sig}
    (ι : {A : Type} → Prog T A → Prog (S ⊕ₛ T) A)
    (hι : ∀ (M : Type → Type) [Monad M] [LawfulMonad M]
            (h : Handler S M) (g : Handler T M) {A : Type} (q : Prog T A),
            interpret (h.sum g) (ι q) = interpret g q)
    {A : Type} (q : Prog T A) : ι q = Prog.inr q :=
  inr_unique_one_target ι
    (fun {_} r => hι (Prog (S ⊕ₛ T)) (inlHandler S T) (inrHandler S T) r) q

/-! ### C2 — ADQ-L30 has the identical shape, in the row just adopted

`llmOracleHandler_unique`'s hypothesis ranges over every `A : Type` and
every `p : Prog AgentSig A`. Its proof consumes, per operation, exactly
one: `A := String`, `p := .vis (.inr (.infer q)) .pure`. At that
instance the hypothesis is EQUIVALENT to the conclusion pointwise —
the same statement `syntactic_hyp_iff` makes on the left, and the reason
is the same (`Prog.bind_pure_right` playing the role `interpret_id`
plays there).

This one is partly on this breaker: the record supplied
`llmOracleHandler_unique` in the ∀-form and did not narrow it. -/

theorem l30_hyp_iff (oracle : String → String)
    (g : Handler LlmSig (Prog CasSig)) (q : String) :
    ((Prog.vis (S := AgentSig) (Sum.inr (LlmE.infer q)) Prog.pure).handleLlm oracle
        = interpret (idHandler.sum g)
            (Prog.vis (S := AgentSig) (Sum.inr (LlmE.infer q)) Prog.pure))
      ↔ g.handle (LlmE.infer q) = (llmOracleHandler oracle).handle (LlmE.infer q) := by
  show (Prog.pure (oracle q) = (g.handle (LlmE.infer q)).bind Prog.pure)
    ↔ (g.handle (LlmE.infer q) = Prog.pure (oracle q))
  rw [Prog.bind_pure_right]
  exact eq_comm

/-- **ADQ-L30, the real statement.** The oracle summand is forced by the
hypothesis at SINGLE-OPERATION programs alone. Strictly stronger than
the shipped row. -/
theorem llmOracleHandler_unique_one_program (oracle : String → String)
    (g : Handler LlmSig (Prog CasSig))
    (hg : ∀ q : String,
        (Prog.vis (S := AgentSig) (Sum.inr (LlmE.infer q)) Prog.pure).handleLlm oracle
          = interpret (idHandler.sum g)
              (Prog.vis (S := AgentSig) (Sum.inr (LlmE.infer q)) Prog.pure)) :
    g = llmOracleHandler oracle :=
  handlerExt fun op =>
    match op with
    | LlmE.infer q => (l30_hyp_iff oracle g q).mp (hg q)

/-- …and the shipped ADQ-L30 row is its corollary. -/
theorem llmOracleHandler_unique_is_corollary (oracle : String → String)
    (g : Handler LlmSig (Prog CasSig))
    (hg : ∀ (A : Type) (p : Prog AgentSig A),
        p.handleLlm oracle = interpret (idHandler.sum g) p) :
    g = llmOracleHandler oracle :=
  llmOracleHandler_unique_one_program oracle g (fun _q => hg String _)

/-! ## §D — failed attempts on the re-run

1. **Break either closure.** FAILED. HOLE-1's fix is structural, not
   cosmetic: §A's `#print` shows `Prog.inl_unique` reduced to an
   application of `inl_unique_one_target`, and every withdrawn claim is
   gone from both the packet row and the docstring. HOLE-2's fix is
   build-enforced: the adversary is a castle declaration now.
2. **Find a statement weakened in adoption.** FAILED — all eight §B
   examples elaborate, so each adopted declaration is at least as strong
   as the record's original.
3. **Find the `Prog.inr_unique` asymmetry hiding an unsoundness.**
   FAILED, and it does not: `inr_unique_is_corollary` proves the
   restructure goes through on the right exactly as on the left. The
   finding is consistency, not correctness.
4. **Find a fourth categoricity row with the same shape.** FAILED —
   there is no fourth. `Handler.sum_unique` is the only other one and
   `sum_unique_iff` already proved its premises minimal.
5. **Close `ObsEq H (liftCas p) (doubleInl p)`** — still NOT ATTEMPTED
   to completion, for the same reason as the first pass, and now
   correctly marked OPEN on both sides by the amended packet rather
   than gestured at.
-/

#print axioms inl_unique_factors_through_one_target
#print axioms syntactic_hyp_iff_inr
#print axioms inr_unique_one_target
#print axioms inr_unique_is_corollary
#print axioms l30_hyp_iff
#print axioms llmOracleHandler_unique_one_program
#print axioms llmOracleHandler_unique_is_corollary

end PDD7Amended
