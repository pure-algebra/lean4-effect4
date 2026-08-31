import Cas.Backend.Universal

/-!
# PDD-8 — the breaker's RE-RUN against the amended castle

WHAT THIS FILE IS. The second pass, against the fix pass. `Attack.lean`
beside it is UNEDITED and stays the record against `6ce34fff`/`8a241313`;
this file is the record against `d74e6ee0`.

```
BREAKER    independent; did not build this castle
SUBJECT    d74e6ee0  PDD-8: the fix pass — six holes closed
PACKET     de720d7b  PDD-8: packet amendments — seven ledger rows
FIRST PASS 6e6fa80a  attack/opus-cc-mac/pdd-8
```

WHAT A CLEAN RE-ELABORATION OF `Attack.lean` DOES AND DOES NOT PROVE.
It re-elaborates clean against `d74e6ee0` — verified. That is expected
and is NOT evidence of closure: every theorem in it was proved against
the ORIGINAL law set, and an amended set that EXTENDS the original
cannot falsify a theorem about the original. Two of its theorems are
now also IN the castle (`one_type_can_be_enough`,
`interpret_pinned_is_vacuous_over_collapse` among them), which is
adoption, not refutation. The closure evidence is in this file.

THIS FILE MUST NOT ENTER ANY LAKE LIBRARY TARGET. Same fence as
`Attack.lean`: under `contracts/attacks/`, outside every `srcDir`,
`globs` and `sources` the package declares; hand-elaborated with
`lake env lean contracts/attacks/PDD-8/AttackAmended.lean` from
`library/cas`, never by `lake build`.

NO `sorry`, no `native_decide`, no `ofReduceBool`.

Verdict per hole: the **Re-run** section of `RESULTS.md` beside this file.
-/

namespace Cas.Lang.AttackAmendedPDD8

open Cas Cas.Lang

/-! ## 1. HOLE-1 — statement fidelity of the two adopted theorems

The fix pass restated the breaker's §4b at the three equations rather
than at `[LawfulMonad M]`. That is a strengthening, but a strengthening
is only a closure if the ORIGINAL statement is still recoverable — a
"generalization" that quietly drops a conclusion closes nothing. Both
are recovered below by instantiation, which is the check: if the
castle's theorem did not carry the breaker's statement, these would not
elaborate. -/

/-- The breaker's `Attack.lean` §4b, VERBATIM at its original
hypotheses, recovered from the castle's amended `prog_is_initial_in_S_models`.
Nothing was lost in the restatement. -/
theorem breaker_4b_recovered {S : Sig} {M : Type → Type} [Monad M]
    [LawfulMonad M] (h : Handler S M) :
    ∃ φ : (A : Type) → Prog S A → M A,
      (IsMorphE S φ ∧ ∀ op : S.Op, φ _ (Prog.op op) = h.handle op)
        ∧ ∀ ψ : (A : Type) → Prog S A → M A, IsMorphE S ψ →
            (∀ op : S.Op, ψ _ (Prog.op op) = h.handle op) → ψ = φ :=
  prog_is_initial_in_S_models leftUnit_of_lawful bindAssoc_of_lawful
    rightUnit_of_lawful h

/-- The freeness theorem at the FIRST DRAFT's exact signature, recovered
from `prog_is_free`. The conclusion is unchanged; only the hypothesis
moved, and it moved down. -/
theorem prog_is_free_recovered {S : Sig} {M : Type → Type} [Monad M]
    [LawfulMonad M] (φ : {A : Type} → Prog S A → M A)
    (hφ : IsMonadMorphism S φ) :
    ∃ h : Handler S M,
      (∀ (A : Type) (p : Prog S A), φ p = interpret h p)
        ∧ ∀ g : Handler S M,
            (∀ (A : Type) (p : Prog S A), φ p = interpret g p) → g = h :=
  prog_is_free rightUnit_of_lawful φ hφ

/-! ## 2. The `*_of_lawful` bridges — spot-checked, and the weakening
shown STRICTLY proper as a bundle

The three bridges (`leftUnit_of_lawful`, `rightUnit_of_lawful`,
`bindAssoc_of_lawful`) would be worthless in two ways the castle does
not rule out: if they were circular, or if the three equations TOGETHER
were equivalent to `LawfulMonad`, in which case the whole amendment
would be a re-spelling. The castle exhibits `RUnit` (right unit only)
and `Ct` (left unit + associativity) separately. Neither shows the
BUNDLE is proper.

`Ct` does, and the castle already has two thirds of it. -/

/-- The third equation for `Ct`, which the castle does not state:
`x >>= pure = x`, because the counter adds zero. -/
theorem ct_rightUnit : RightUnit Ct := fun _x => Prod.ext rfl (Nat.add_zero _)

/-- **The bundle is strictly weaker than `LawfulMonad`.** `Ct` satisfies
ALL THREE equations and has no `LawfulMonad` instance. So the amendment
is not a re-spelling: every theorem restated at the equations reaches at
least one target the `[LawfulMonad M]` version could not be applied to,
and the three bridges are genuinely one-directional. -/
theorem three_equations_do_not_imply_lawful :
    LeftUnit Ct ∧ RightUnit Ct ∧ BindAssoc Ct ∧ ¬ Nonempty (LawfulMonad Ct) :=
  ⟨ct_leftUnit, ct_rightUnit, ct_bindAssoc, ct_not_lawful⟩

def OneSig : Sig := ⟨Unit, fun _ => Unit⟩

/-- **HOLE-6's closure, cashed.** The amended pin companion covers the
pin's ACTUAL quantifier: here it is instantiated at `Ct`, a target with
no `LawfulMonad` instance, which the first draft's
`[LawfulMonad M]`-bearing companion could not reach at all. The pin's
hypothesis class is inhabited there. -/
theorem pin_inhabited_at_ct :
    (∀ h : Handler OneSig Ct,
        IsMonadMorphism OneSig (fun {_A} (p : Prog OneSig _A) => interpret h p))
      ∧ ∀ (h : Handler OneSig Ct) (op : OneSig.Op),
          interpret h (Prog.op op) = h.handle op :=
  interpret_inhabits_the_pin ct_leftUnit ct_bindAssoc ct_rightUnit

/-! ## 3. The `through_assoc` correction — is TWO equations MINIMAL?

The coordinator's correction is accepted and the breaker's first-pass
sentence was wrong: HOLE-3 said three declarations "spend one equation",
which is right for L17 and `through_id_left` and WRONG for
`through_assoc`, whose proof runs through `interpret_bind` and spends the
left unit AND associativity. `through_assoc_holds_over_collapse`
(`Attack.lean` §7 F3) shows only that `[LawfulMonad M]` is not NECESSARY
— in `Collapse` everything interprets to `true`, so the conclusion holds
for a reason outside any equation. It never identified which equations
suffice. `through_assoc_over_ct` is the right witness and the castle has
it.

What NOBODY has shown is that two is MINIMAL: that neither equation can
be dropped. A hypothesis set is minimal when no proper subset suffices,
so two witnesses are owed — one target satisfying `BindAssoc` alone
where the theorem FAILS, and one satisfying `LeftUnit` alone where it
FAILS. Both are constructed here. Without them the two-equation
statement is exactly the surplus HOLE-3 objected to, one equation
smaller. -/

/-! ### 3a. The apparatus -/

def P1 : Prog OneSig Unit := Prog.op ()
def P2 : Prog OneSig Unit := .vis () fun _ => .vis () fun _ => .pure ()

/-- Signature-level identity service: perform the operation. -/
def tPass : Handler OneSig (Prog OneSig) := ⟨fun _ => P1⟩

/-- A service that performs TWO lower operations per upper operation —
enough depth for associativity to bite. -/
def tTwice : Handler OneSig (Prog OneSig) := ⟨fun _ => P2⟩

/-! ### 3b. Dropping `LeftUnit`: `BindAssoc` alone does not suffice

`Shift` is the writer monad whose `pure` costs ONE. Associativity holds
(addition is associative); the left unit fails at every point, because
`pure` always adds. -/

def Shift (A : Type) : Type := Nat × A

instance : Monad Shift where
  pure a := (1, a)
  bind x f := (x.1 + (f x.2).1, (f x.2).2)

theorem shift_bindAssoc : BindAssoc Shift := by
  intro A B C x f g
  show ((x.1 + (f x.2).1) + (g (f x.2).2).1, (g (f x.2).2).2)
     = (x.1 + ((f x.2).1 + (g (f x.2).2).1), (g (f x.2).2).2)
  rw [Nat.add_assoc]

theorem shift_not_leftUnit : ¬ LeftUnit Shift := by
  intro lu
  have h := lu () (fun _ => ((0 : Nat), ()))
  exact absurd (congrArg Prod.fst h) (by decide)

theorem shift_not_lawful : ¬ Nonempty (LawfulMonad Shift) := by
  rintro ⟨_⟩
  exact shift_not_leftUnit leftUnit_of_lawful

def hShift : Handler OneSig Shift := ⟨fun _ => ((1 : Nat), ())⟩

/-- **MINIMALITY WITNESS 1.** `through_assoc` is FALSE over a target with
`BindAssoc` and no `LeftUnit`. So `{BindAssoc}` alone does not prove the
theorem, and `lu` cannot be dropped from the castle's statement.

The two composites disagree at the single operation: interpreting the
service through the identity gives `2`, and collapsing the tower first
gives `3`, because the collapsed handler pays `pure`'s surcharge a
second time. -/
theorem through_assoc_fails_over_shift :
    (tPass.through tPass).through hShift ≠ tPass.through (tPass.through hShift) := by
  intro hEq
  have hn : (2 : Nat) = 3 := congrArg (fun x => (Handler.handle x ()).1) hEq
  exact absurd hn (by decide)

/-! ### 3c. Dropping `BindAssoc`: `LeftUnit` alone does not suffice

`Skew` costs nothing for `pure` and nothing for a zero-cost step — so it
has BOTH units — but combines two non-zero costs non-associatively. -/

def skew (n m : Nat) : Nat :=
  if n = 0 then m else if m = 0 then n else n + 2 * m

def Skew (A : Type) : Type := Nat × A

instance : Monad Skew where
  pure a := (0, a)
  bind x f := (skew x.1 (f x.2).1, (f x.2).2)

theorem skew_leftUnit : LeftUnit Skew := by
  intro A B a f
  show (skew 0 (f a).1, (f a).2) = f a
  simp only [skew]
  exact Prod.ext rfl rfl

theorem skew_rightUnit : RightUnit Skew := by
  intro A x
  show (skew x.1 0, x.2) = x
  cases x with
  | mk n a => cases n <;> simp [skew]

def skOne : Skew Unit := ((1 : Nat), ())

theorem skew_not_bindAssoc : ¬ BindAssoc Skew := by
  intro ba
  have h := ba skOne (fun _ => skOne) (fun _ => skOne)
  exact absurd (congrArg Prod.fst h) (by decide)

theorem skew_not_lawful : ¬ Nonempty (LawfulMonad Skew) := by
  rintro ⟨_⟩
  exact skew_not_bindAssoc bindAssoc_of_lawful

def hSkew : Handler OneSig Skew := ⟨fun _ => ((1 : Nat), ())⟩

/-- **MINIMALITY WITNESS 2.** `through_assoc` is FALSE over a target with
BOTH units and no `BindAssoc`. So `{LeftUnit}` — indeed
`{LeftUnit, RightUnit}` — does not prove the theorem, and `ba` cannot be
dropped either.

Four operations bracketed one way cost `15`; the same four with the
lower stratum collapsed first cost `9`. -/
theorem through_assoc_fails_over_skew :
    (tTwice.through tTwice).through hSkew
      ≠ tTwice.through (tTwice.through hSkew) := by
  intro hEq
  have hn : (15 : Nat) = 9 := congrArg (fun x => (Handler.handle x ()).1) hEq
  exact absurd hn (by decide)

/-- **The minimality result.** Neither equation in the castle's amended
`through_assoc` can be dropped: each has a target satisfying the other
(and, for `ba`, both units) where the theorem is FALSE. The two-equation
statement is MINIMAL, and the coordinator's correction to the breaker's
first-pass sentence is confirmed with witnesses on both sides. -/
theorem through_assoc_two_equations_are_minimal :
    (BindAssoc Shift ∧ ¬ LeftUnit Shift
      ∧ (tPass.through tPass).through hShift
          ≠ tPass.through (tPass.through hShift))
    ∧ (LeftUnit Skew ∧ RightUnit Skew ∧ ¬ BindAssoc Skew
      ∧ (tTwice.through tTwice).through hSkew
          ≠ tTwice.through (tTwice.through hSkew)) :=
  ⟨⟨shift_bindAssoc, shift_not_leftUnit, through_assoc_fails_over_shift⟩,
   ⟨skew_leftUnit, skew_rightUnit, skew_not_bindAssoc,
    through_assoc_fails_over_skew⟩⟩

/-! ### 3d. And the same question for the ONE-equation statements

`handler_eq_of_interpret_op_eq` and `through_id_left` carry `RightUnit`
alone. Minimality there is the empty check — drop the only hypothesis
and `uniqueness_needs_lawful` is already the castle's own falsifier
(`Collapse` has no `RightUnit`, and uniqueness fails). Recorded as
closed by the castle's existing witness, not re-proved. -/

/-! ## 4. FRESH PROBE — alias fidelity

The fix pass kept two names as aliases "so the packet's `LAW UP` row and
any reader who followed the old prose still resolve". The probe: do the
aliases carry the OLD theorems, or only the old NAMES? Both aliases
changed signature — `[LawfulMonad M]` became an equation ARGUMENT — so a
reader who resolves the old name does not get the old call.

Answer: the aliases are strict GENERALIZATIONS, and the old signatures
are recoverable by supplying the bridge. Nothing was weakened; but the
name resolves and the old APPLICATION does not, so "still resolve" is
true of the name and not of the call site. Verified rather than assumed,
because an alias that changed its conclusion would be the worst kind of
silent regression. -/

/-- `existsUnique_handler` at its pre-amendment signature. -/
theorem existsUnique_handler_old_call {S : Sig} {M : Type → Type} [Monad M]
    [LawfulMonad M] (φ : {A : Type} → Prog S A → M A)
    (hφ : IsMonadMorphism S φ) :
    ∃ h : Handler S M,
      (∀ (A : Type) (p : Prog S A), φ p = interpret h p)
        ∧ ∀ g : Handler S M,
            (∀ (A : Type) (p : Prog S A), φ p = interpret g p) → g = h :=
  existsUnique_handler rightUnit_of_lawful φ hφ

/-- `interpret_satisfies_the_property` at its pre-amendment signature. -/
theorem interpret_satisfies_the_property_old_call {S : Sig} {M : Type → Type}
    [Monad M] [LawfulMonad M] :
    (∀ h : Handler S M,
        IsMonadMorphism S (fun {_A} (p : Prog S _A) => interpret h p))
      ∧ ∀ (h : Handler S M) (op : S.Op),
          interpret h (Prog.op op) = h.handle op :=
  interpret_satisfies_the_property leftUnit_of_lawful bindAssoc_of_lawful
    rightUnit_of_lawful

/-- And the alias really is the same theorem as the name it points at,
not a lookalike. -/
theorem aliases_are_the_theorems_they_alias {S : Sig} {M : Type → Type}
    [Monad M] (runit : RightUnit M) (φ : {A : Type} → Prog S A → M A)
    (hφ : IsMonadMorphism S φ) :
    existsUnique_handler runit φ hφ = prog_is_free runit φ hφ := rfl

/-! ## 5. The first pass's own counter-witness, re-checked

`prog_is_not_initial_among_monads` (`Attack.lean` §4a) is what forced
HOLE-1. It must STILL be true against the amended castle — a "fix" that
made it false would mean the fix broke something. It re-elaborates
unedited, and the fact it names is restated here against the amended
vocabulary: freeness landed, initiality-among-monads is still FALSE, and
the castle now says so in its own §6b docstring. -/

def hIncA : Handler OneSig (StateT Nat Id) := ⟨fun _ => fun s => ((), s + 1)⟩
def hNopA : Handler OneSig (StateT Nat Id) := ⟨fun _ => fun s => ((), s)⟩

/-- Still two distinct monad morphisms out of `Prog OneSig`. Freeness is
the right word; initiality among monads remains false. -/
theorem still_not_initial_among_monads :
    IsMonadMorphism OneSig
        (fun {_A} (p : Prog OneSig _A) => interpret hIncA p)
      ∧ IsMonadMorphism OneSig
        (fun {_A} (p : Prog OneSig _A) => interpret hNopA p)
      ∧ interpret hIncA (Prog.op ()) ≠ interpret hNopA (Prog.op ()) := by
  refine ⟨interpret_isMonadMorphism hIncA, interpret_isMonadMorphism hNopA, ?_⟩
  intro h
  have h0 : (((), 1) : Unit × Nat) = ((), 0) := congrFun h 0
  exact absurd (congrArg Prod.snd h0) (by decide)

/-! ## 6. This file's axiom census -/

#print axioms breaker_4b_recovered
#print axioms prog_is_free_recovered
#print axioms three_equations_do_not_imply_lawful
#print axioms pin_inhabited_at_ct
#print axioms through_assoc_two_equations_are_minimal
#print axioms existsUnique_handler_old_call
#print axioms aliases_are_the_theorems_they_alias
#print axioms still_not_initial_among_monads

end Cas.Lang.AttackAmendedPDD8
