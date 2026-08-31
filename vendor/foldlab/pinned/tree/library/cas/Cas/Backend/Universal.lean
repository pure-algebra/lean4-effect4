import Cas.Lang.Representation
import Cas.Lang.Wp

/-!
# PDD-8 — interpretation's universal property, and the tower's monoid

The theorem module for `library/cas/contracts/PDD-8.contract.md`. It
states and proves the facts that license EFFECTS-BACKEND R10's word "IS"
in "a semantics IS a handler", and the three that make the service
tower's composition a monoid. It adds no definition to the language,
edits no existing file, and emits no bytes.

## The claim, in one line

`interpret` is a BIJECTION `Handler S M ≃ Mor(Prog S, M)` — every
handler induces a monad morphism, every monad morphism comes from one,
and from exactly one. That is FREENESS: `Prog S` is the free monad on
`S`. The INITIALITY that is also true lives one category over, in
`S`-models, and is proved separately (§6c) rather than glossed off the
freeness statement.

## Where this file lives, and why

The statements are about `Cas/Lang/Handler.lean`, `Cas/Lang/Interp.lean`
and `Cas/Lang/Tower.lean`, so `Cas/Lang/` is where they belong. They are
here instead for a mechanical reason that is written down rather than
discovered: the ticket's fence forbids editing any existing file, the
`Cas` library's glob is its root module alone, and `Cas.Backend.+` is
the only glob in `lakefile.toml` that picks a new module up without a
lakefile edit. So `lake --wfail build` kernel-checks every theorem
below, and — because `Walk.libraryImports` (`tools/Walk.lean:45-55`)
names the `Cas.Backend.*` leaves one by one and does not name this one —
the surface, obligation and law ledgers do not move. Same device, same
reason, as `Cas/Backend/Canon.lean` (PDD-1) and the `CasWp` library
(PDD-2). Promoting this module into `Cas/Lang/` and into that walk is a
promotion, and a promotion is a ruling — and the promotion argument is
now stronger than the packet's: with this file DELETED, every byte gate
stays green (breaker NOTE-2). A theorem no ledger knows about is a
theorem the estate cannot be said to hold.

`Cas.Lang.Wp` is imported for §7's shape witnesses alone — so `wp` and
`wlp` can be placed against the property in the same environment that
holds it. Nothing here depends on a `Wp` theorem.

## Prior art, cited

Two sources, both re-elaborated rather than trusted.

**The review's exhibits**
(`.staging/algebraic-review/handlers-semantics-exhibits.lean` §3–§5)
carry sketches for `Handler.ext`, uniqueness, existence and the two
tower laws. Every sketch survives as written. One strengthening was
found and taken: the existence sketch declares `[LawfulMonad M]` and
never uses it, so `interpret_of_isMonadMorphism` is stated at a bare
`Monad`.

**The independent breaker's record**
(`library/cas/contracts/attacks/PDD-8/Attack.lean`, branch
`attack/opus-cc-mac/pdd-8`, commit `6e6fa80a`) supplied proved repairs
for six of the seven holes it found against commits `6ce34fff` and
`8a241313`. Adopted here, with the breaker's own proofs where they were
given, each credited at its declaration:

```
prog_is_initial_in_S_models            §4b   HOLE-1
uniqueness_from_right_unit             §3c   HOLE-3
through_id_left_from_right_unit        §3c   HOLE-3
RUnit, runit_right_unit, runit_not_lawful    §3c   HOLE-3
Ct, ct_not_lawful                      §2b   HOLE-3
collapse_not_lawful                    §3c   HOLE-3
one_type_can_be_enough                 §3d   HOLE-4
RunM, runAsMap, stepAsMap              §5b   HOLE-5
run3_load_once_eq_twice                §5c   HOLE-5
run_has_no_composition_law             §5c   HOLE-5
interpret_pinned_is_vacuous_over_collapse    §7 F1   HOLE-6
pinned_needs_op_agreement              §7 F2  HOLE-6
pinned_needs_the_morphism_law          §7 F2  HOLE-6
runPShape, wpShape, wlpShape           §6    HOLE-7
phiDrifts_pure_law, phiDrifts_read_off §3b   NOTE-4
bigProg                                §7 F4 NOTE-5
```

## What this module does NOT claim

- **Not initiality among monads.** `Prog S` is NOT initial in
  monads-and-monad-morphisms — it admits two distinct morphisms into
  `StateT Nat Id` (breaker §4a). The initiality that holds is in
  `S`-MODELS and is §6c. The two are inter-derivable and differ in
  quantifier order: freeness fixes a morphism and produces a unique
  handler; initiality fixes a handler and produces a unique morphism.
- **Nothing about `EFFECTS-BACKEND.md:263`'s word.** That line glosses
  INITIAL as `eq_of_forall_interpret`, which is neither freeness nor
  initiality but faithfulness of the syntactic semantics. Three readings
  of one word now exist and binding it is an OPERATOR RULING, owed and
  recorded in the packet. `Lang.lean:21`'s "free monad" is the one
  citation this module discharges cleanly.
- **Nothing about WHICH handler is right.** The property is about form,
  not content: `replayHandler` (`Handler.lean:279`) is a handler, hence
  a semantics by this theorem, and it is still the wrong one — the two
  kernel-checked witnesses in the review (THE-ALGEBRA §3.4c) stand.
- **Nothing about `Prog.handleLlm`.** L18 is a CONDITIONAL, and its
  `bind_law` hypothesis is exactly the judgment `Interp.lean:19,181-183`
  asserts and nothing proves. That is PDD-7's L30/L32.
- **Nothing about a bottom.** The tower is a monoid at one signature and
  a category across signatures; there is still no `Handler ByteSig M`
  (THE-ALGEBRA L37).
- **Nothing about programs above `Type`.** `Handler S M` fixes
  `M : Type → Type v`, so `interpret` exists only at `A : Type`, while
  `Prog S A` is polymorphic in `A : Type u`. `bigProg` (§7) is a program
  no handler can interpret — not "not yet", but not at the shipped
  `Handler`. R10's "a semantics IS a handler" is not merely unproved
  there; such programs have NO handler semantics at all.
- **No soundness word attaches to any host code.** No TypeScript is a
  subject here; nothing moves a generated byte.
-/

namespace Cas.Lang

universe v

/-! ## 1. Handler extensionality (L16)

A handler is one field, so equality of handlers is agreement per
operation. Stated once, generally, because every uniqueness argument
below ends here. -/

/-- **L16.** Handlers agreeing on every operation are equal. -/
theorem Handler.ext {S : Sig} {M : Type → Type v} {h g : Handler S M}
    (e : ∀ op, h.handle op = g.handle op) : h = g := by
  cases h; cases g; exact congrArg Handler.mk (funext e)

/-! ## 2. The unfolding law (L12)

`interpret` on a `vis` node — the equation the estate restates locally
wherever it needs it and states nowhere in general. It is `rfl`; the
point is that it has a name. -/

/-- **L12.** Interpreting an operation node: the handler's meaning for
the operation, then interpretation of the continuation at its answer. -/
theorem interpret_vis {S : Sig} {M : Type → Type v} {A : Type} [Monad M]
    (h : Handler S M) (op : S.Op) (k : S.Ans op → Prog S A) :
    interpret h (.vis op k) = h.handle op >>= fun a => interpret h (k a) :=
  rfl

/-! ## 3. The equations the proofs spend

AMENDED, breaker hand (HOLE-3). The first draft of this module demanded
`[LawfulMonad M]` on four declarations. `LawfulMonad` bundles the three
monad equations with `LawfulApplicative` and `LawfulFunctor`, and none
of the four proofs touches a functor or applicative law. By the standard
this module applied to the review's `[LawfulMonad M]` on L18 — drop what
the proof does not use — the surplus had to go.

The three equations are named here so each theorem below can carry
exactly the one it spends. `LawfulMonad` implies all three
(`leftUnit_of_lawful` and friends), so nothing downstream is harder to
use; and the weakening is REAL, not cosmetic, because targets exist that
satisfy some and not `LawfulMonad` — `RUnit` and `Ct` at the end of this
section, both the breaker's. -/

/-- `pure a >>= f = f a`. -/
abbrev LeftUnit (M : Type → Type v) [Monad M] : Prop :=
  ∀ {A B : Type} (a : A) (f : A → M B), (pure a : M A) >>= f = f a

/-- `x >>= pure = x`. The ONE equation `interpret_op` spends, and
therefore the whole of what uniqueness and the tower's left unit need. -/
abbrev RightUnit (M : Type → Type v) [Monad M] : Prop :=
  ∀ {A : Type} (x : M A), x >>= (fun a => (pure a : M A)) = x

/-- `(x >>= f) >>= g = x >>= fun a => f a >>= g`. -/
abbrev BindAssoc (M : Type → Type v) [Monad M] : Prop :=
  ∀ {A B C : Type} (x : M A) (f : A → M B) (g : B → M C),
    (x >>= f) >>= g = x >>= fun a => f a >>= g

theorem leftUnit_of_lawful {M : Type → Type v} [Monad M] [LawfulMonad M] :
    LeftUnit M := fun a f => pure_bind a f

theorem rightUnit_of_lawful {M : Type → Type v} [Monad M] [LawfulMonad M] :
    RightUnit M := fun x => bind_pure x

theorem bindAssoc_of_lawful {M : Type → Type v} [Monad M] [LawfulMonad M] :
    BindAssoc M := fun x f g => bind_assoc x f g

/-- The operation law at the equation it spends. `interpret_op`
(`Representation.lean:115`) is stated at `[LawfulMonad M]`; its proof
uses `x >>= pure = x` and nothing else. -/
theorem interpret_op_of_rightUnit {S : Sig} {M : Type → Type v} [Monad M]
    (runit : RightUnit M) (h : Handler S M) (op : S.Op) :
    interpret h (Prog.op op) = h.handle op :=
  runit _

/-- The monad-morphism law at the equations it spends. `interpret_bind`
(`Handler.lean:53`) is stated at `[LawfulMonad M]`; its proof uses the
left unit and associativity. -/
theorem interpret_bind_of_equations {S : Sig} {M : Type → Type v}
    {A B : Type} [Monad M] (lu : LeftUnit M) (ba : BindAssoc M)
    (h : Handler S M) (p : Prog S A) (f : A → Prog S B) :
    interpret h (p.bind f) = interpret h p >>= fun a => interpret h (f a) := by
  induction p with
  | pure a =>
    show interpret h (f a) = (pure a : M A) >>= fun x => interpret h (f x)
    exact (lu a (fun x => interpret h (f x))).symm
  | vis op k ih =>
    show h.handle op >>= (fun r => interpret h ((k r).bind f))
       = (h.handle op >>= fun r => interpret h (k r)) >>= fun a => interpret h (f a)
    rw [ba]
    exact bind_congr fun r => ih r

/-- The tower's collapse at the equations it spends — `interpret_through`
(`Tower.lean:71`) re-proved without `[LawfulMonad M]`. -/
theorem interpret_through_of_equations {S T : Sig} {M : Type → Type v}
    {A : Type} [Monad M] (lu : LeftUnit M) (ba : BindAssoc M)
    (t : Handler S (Prog T)) (h : Handler T M) (p : Prog S A) :
    interpret h (interpret t p) = interpret (t.through h) p := by
  induction p with
  | pure a => rfl
  | vis op k ih =>
    calc interpret h (interpret t (.vis op k))
        = interpret h ((t.handle op).bind fun a => interpret t (k a)) := rfl
      _ = interpret h (t.handle op) >>=
            fun a => interpret h (interpret t (k a)) :=
          interpret_bind_of_equations lu ba h (t.handle op) _
      _ = interpret h (t.handle op) >>=
            fun a => interpret (t.through h) (k a) := bind_congr fun a => ih a
      _ = interpret (t.through h) (.vis op k) := rfl

/-! ### The weakening is real — two targets that are not `LawfulMonad`

Breaker's, adopted verbatim in substance (`Attack.lean` §2b and §3c).
Without these the drop would be a cosmetic re-spelling of
`LawfulMonad`; with them it is a strictly larger class of targets, and
the surplus the first draft carried was real surplus. -/

/-- The counting monad with a POISONED `map`: impeccable `pure`/`bind`,
`id_map` false. Breaker `Attack.lean` §2b. -/
def Ct (A : Type) : Type := A × Nat

instance : Monad Ct where
  pure a := (a, 0)
  bind x f := ((f x.1).1, x.2 + (f x.1).2)
  map f x := (f x.1, x.2 + 1)

private def ctZero : Ct Nat := (0, 0)

/-- `Ct` has no `LawfulMonad` instance to be had. Breaker's proof. -/
theorem ct_not_lawful : ¬ Nonempty (LawfulMonad Ct) := by
  rintro ⟨_⟩
  have h : id <$> ctZero = ctZero := LawfulFunctor.id_map _
  exact absurd (congrArg Prod.snd h) (by decide)

theorem ct_leftUnit : LeftUnit Ct := fun a f => by
  show ((f a).1, 0 + (f a).2) = f a
  exact Prod.ext rfl (Nat.zero_add _)

theorem ct_bindAssoc : BindAssoc Ct := fun x f g => by
  show ((g (f x.1).1).1, (x.2 + (f x.1).2) + (g (f x.1).1).2)
     = ((g (f x.1).1).1, x.2 + ((f x.1).2 + (g (f x.1).1).2))
  rw [Nat.add_assoc]

/-- The counting monad whose `bind` charges a surcharge: it has the
RIGHT UNIT and fails `pure_bind`. Breaker `Attack.lean` §3c. -/
def RUnit (A : Type) : Type := Nat × A

instance : Monad RUnit where
  pure a := (0, a)
  bind x f := (if (f x.2).1 = 0 then x.1 else x.1 + (f x.2).1 + 1, (f x.2).2)

theorem runit_rightUnit : RightUnit RUnit := fun _ => rfl

private def ruOne : RUnit Nat := (1, 0)

/-- `RUnit` is NOT lawful: `pure_bind` fails at the surcharge.
Breaker's proof. -/
theorem runit_not_lawful : ¬ Nonempty (LawfulMonad RUnit) := by
  rintro ⟨_⟩
  have h : (pure 0 >>= fun _ => ruOne) = ruOne := LawfulMonad.pure_bind 0 _
  have hn : (2 : Nat) = 1 := congrArg Prod.fst h
  exact absurd hn (by decide)

/-! ## 4. Monad morphisms out of `Prog S`, and L13

Statement apparatus, proof stratum only: a name for the property
`interpret_pure` and `interpret_bind` jointly assert. The estate has
the two halves in two files (`Representation.lean:110`,
`Handler.lean:53`) and no declaration naming their conjunction, which
is exactly THE-ALGEBRA L13's complaint. `IsMonadMorphism` is that name,
and it is also the HYPOTHESIS class the existence theorem needs, so it
is one definition serving both. -/

/-- A monad morphism out of `Prog S`: a family of maps `Prog S A → M A`
respecting `pure` and `bind`. The polymorphism is load-bearing — the
`bind_law` at `A := S.Ans op` is what makes an operation's answer type
available to the induction. -/
structure IsMonadMorphism (S : Sig) {M : Type → Type v} [Monad M]
    (φ : {A : Type} → Prog S A → M A) : Prop where
  /-- A finished program means `pure`. -/
  pure_law : ∀ {A : Type} (a : A), φ (Prog.pure a) = pure a
  /-- Sequencing is preserved. -/
  bind_law : ∀ {A B : Type} (p : Prog S A) (f : A → Prog S B),
    φ (p.bind f) = φ p >>= fun a => φ (f a)

/-- **L13.** "`interpret h` is a monad morphism", as ONE statement, for
every handler into every lawful target. The two halves are the estate's
own `interpret_pure` and `interpret_bind`; this declaration is the
conjunction it did not have. -/
theorem interpret_isMonadMorphism {S : Sig} {M : Type → Type v}
    [Monad M] [LawfulMonad M] (h : Handler S M) :
    IsMonadMorphism S (fun {_A} (p : Prog S _A) => interpret h p) where
  pure_law a := interpret_pure h a
  bind_law p f := interpret_bind h p f

/-- L13 at the equations it spends, for targets with no `LawfulMonad`
instance. Kept beside the lawful form rather than replacing it: the
lawful form is the estate-facing statement and reuses main's
`interpret_bind` directly. -/
theorem interpret_isMonadMorphism_of_equations {S : Sig} {M : Type → Type v}
    [Monad M] (lu : LeftUnit M) (ba : BindAssoc M) (h : Handler S M) :
    IsMonadMorphism S (fun {_A} (p : Prog S _A) => interpret h p) where
  pure_law a := interpret_pure h a
  bind_law p f := interpret_bind_of_equations lu ba h p f

/-! ## 5. Uniqueness (L17)

Two handlers whose interpretations agree are equal. AMENDED, breaker
hand (HOLE-3): stated at `RightUnit M`, the one equation the proof
spends, not at `[LawfulMonad M]`. Over `RUnit` this theorem is true and
the first draft's statement could not even be TYPED — there is no
`LawfulMonad RUnit` instance to supply. -/

/-- **L17, sharp form.** Agreement on one-operation programs already
forces handler equality. Breaker's `uniqueness_from_right_unit`
(`Attack.lean` §3c), adopted. -/
theorem handler_eq_of_interpret_op_eq {S : Sig} {M : Type → Type v}
    [Monad M] (runit : RightUnit M) {h g : Handler S M}
    (e : ∀ op : S.Op, interpret h (Prog.op op) = interpret g (Prog.op op)) :
    h = g :=
  Handler.ext fun op => by
    have := e op
    rwa [interpret_op_of_rightUnit runit h op,
      interpret_op_of_rightUnit runit g op] at this

/-- **L17, as ticketed.** `interpret h = interpret g → h = g`. The
antecedent is spelled at every answer type, because `interpret h` is not
one function: `A` is implicit. -/
theorem handler_eq_of_interpret_eq {S : Sig} {M : Type → Type v}
    [Monad M] (runit : RightUnit M) {h g : Handler S M}
    (e : ∀ (A : Type) (p : Prog S A), interpret h p = interpret g p) :
    h = g :=
  handler_eq_of_interpret_op_eq runit fun op => e _ (Prog.op op)

/-! ### The falsifiers L17 survives, and what they do and do not show -/

/-- The target of `uniqueness_needs_lawful`: `Bool` as a constant
functor, with the degenerate — and deliberately UNLAWFUL — monad
structure that answers `true` to everything. -/
private abbrev Collapse : Type → Type := fun _ => Bool

private instance : Monad Collapse where
  pure _ := true
  bind _ _ := true

/-- A one-operation signature, the smallest carrier that distinguishes
two handlers. -/
private def OneSig : Sig := ⟨Unit, fun _ => Unit⟩

private def hTrue : Handler OneSig Collapse := ⟨fun _ => true⟩
private def hFalse : Handler OneSig Collapse := ⟨fun _ => false⟩

private def cFalse : Collapse Unit := false

/-- WHICH axiom `Collapse` violates, named rather than left as "not
lawful": `LawfulMonad.pure_bind`. AMENDED, breaker hand (HOLE-3) — the
first draft asserted unlawfulness without exhibiting the failing law. -/
theorem collapse_not_lawful : ¬ Nonempty (LawfulMonad Collapse) := by
  rintro ⟨_⟩
  have h : (pure () >>= fun _ => cFalse) = cFalse := LawfulMonad.pure_bind () _
  have hb : (true : Bool) = false := h
  exact Bool.noConfusion hb

private theorem collapse_interpret {A : Type} (h : Handler OneSig Collapse)
    (p : Prog OneSig A) : interpret h p = true := by
  induction p with
  | pure a => rfl
  | vis op k ih => rfl

/-- **FALSIFIER: uniqueness needs SOMETHING.** Drop every equation and
uniqueness is FALSE — in the collapsing target every program interprets
to `true` under every handler, so two visibly different handlers have
equal interpretations at every type.

What this shows, exactly: not that `LawfulMonad` is the right
hypothesis. `Collapse` fails `pure_bind` and also fails `RightUnit`, so
it separates "no hypothesis" from "some hypothesis" and says nothing
about which. `l17_holds_over_runit` below is the other side. -/
theorem uniqueness_needs_lawful :
    (∀ (A : Type) (p : Prog OneSig A), interpret hTrue p = interpret hFalse p)
      ∧ hTrue ≠ hFalse := by
  refine ⟨fun _ p => by rw [collapse_interpret, collapse_interpret], ?_⟩
  intro h
  exact Bool.noConfusion (congrArg (fun x => Handler.handle x ()) h)

/-- **The sufficiency side.** Uniqueness holds over `RUnit`, which has
the right unit and no `LawfulMonad` instance — so the amended hypothesis
is not merely smaller on paper, it reaches targets the first draft's
statement could not be written down at. Breaker
`l17_holds_where_the_castle_cannot_state_it` (`Attack.lean` §3c). -/
theorem l17_holds_over_runit {h g : Handler OneSig RUnit}
    (e : ∀ op : OneSig.Op,
      interpret h (Prog.op op) = interpret g (Prog.op op)) : h = g :=
  handler_eq_of_interpret_op_eq runit_rightUnit e

/-- **FALSIFIER for reading L17 at a BADLY CHOSEN answer type.**
`Prog S Empty` is uninhabited whenever every operation's answer type is
inhabited: a program must eventually `pure`, and there is nothing to
`pure`. So agreement "for all `p : Prog S Empty`" is vacuous and forces
nothing.

AMENDED, breaker hand (HOLE-4). The first draft's headline was "one
answer type proves nothing", which is FALSE — see
`one_type_can_be_enough` immediately below. The true statement, and the
one this theorem has always proved, is that there EXISTS an answer type
at which agreement is vacuous. The general-`S` motive for quantifying
over `A` is different and also true: answer types vary with the
operation. -/
theorem single_type_agreement_is_not_enough :
    (∀ p : Prog OneSig Empty, interpret hTrue p = interpret hFalse p)
      ∧ hTrue ≠ hFalse := by
  refine ⟨fun p => (?_ : False).elim, ?_⟩
  · induction p with
    | pure a => exact a.elim
    | vis op k ih => exact ih ()
  · intro h
    exact Bool.noConfusion (congrArg (fun x => Handler.handle x ()) h)

/-- **The counter-witness that forced the amendment above.** At `OneSig`
— the signature the falsifier itself is built on — agreement at the
SINGLE answer type `Unit` forces handler equality outright, because
`Prog.op op : Prog OneSig Unit`. Breaker `one_type_can_be_enough`
(`Attack.lean` §3d), adopted. -/
theorem one_type_can_be_enough {M : Type → Type v} [Monad M]
    (runit : RightUnit M) {h g : Handler OneSig M}
    (e : ∀ p : Prog OneSig Unit, interpret h p = interpret g p) : h = g :=
  Handler.ext fun op =>
    calc h.handle op = interpret h (Prog.op op) :=
          (interpret_op_of_rightUnit runit h op).symm
      _ = interpret g (Prog.op op) := e (Prog.op op)
      _ = g.handle op := interpret_op_of_rightUnit runit g op

/-! ## 6. Existence, freeness, and initiality

The deep one: every monad morphism out of `Prog S` IS `interpret h`, for
the handler read off its own action on single operations. §6a is that
theorem; §6b packages it with L17 as FREENESS; §6c is the INITIALITY
that is a different theorem in a different category, and that the first
draft of this module wrongly glossed off §6b. -/

/-! ### 6a. Existence (L18) -/

/-- **L18.** Every monad morphism out of `Prog S` is an interpretation,
and the handler is recovered from the morphism's action on single
operations.

Stated at a bare `Monad M`: the review's exhibit (§4) declares
`[LawfulMonad M]` and never uses it. The drop is real and self-limiting
— `Ct` above is a target with no `LawfulMonad` instance where L18
applies, and the breaker's `Shift` (`Attack.lean` §2c) is one where the
hypothesis is uninhabitable, so "bare `Monad`" is a proper subclass on
both sides and must not be read as "every monad". -/
theorem interpret_of_isMonadMorphism {S : Sig} {M : Type → Type v} {A : Type}
    [Monad M] (φ : {A : Type} → Prog S A → M A) (hφ : IsMonadMorphism S φ)
    (p : Prog S A) :
    φ p = interpret (M := M) ⟨fun op => φ (Prog.op op)⟩ p := by
  induction p with
  | pure a => exact hφ.pure_law a
  | vis op k ih =>
    have hv : φ (Prog.vis op k) = φ (Prog.op op) >>= fun r => φ (k r) :=
      hφ.bind_law (Prog.op op) k
    rw [hv]
    exact bind_congr fun r => ih r

/-- **L18, existence form.** "A semantics IS a handler", as the estate's
prose says it: for every monad morphism out of `Prog S` there is a
handler inducing it. -/
theorem exists_handler_of_isMonadMorphism {S : Sig} {M : Type → Type v}
    [Monad M] (φ : {A : Type} → Prog S A → M A) (hφ : IsMonadMorphism S φ) :
    ∃ h : Handler S M, ∀ (A : Type) (p : Prog S A), φ p = interpret h p :=
  ⟨⟨fun op => φ (Prog.op op)⟩, fun _ p => interpret_of_isMonadMorphism φ hφ p⟩

/-! ### 6b. FREENESS — L16 + L17 + L18 -/

/-- **The free-monad property.** Every monad morphism out of `Prog S` is
induced by exactly ONE handler — `interpret` is a bijection
`Handler S M ≃ Mor(Prog S, M)`. This is what `Lang.lean:21`'s "free
monad of continuations over a signature" names, and it is discharged.

AMENDED, breaker hand (HOLE-1). The first draft called this theorem
"`Prog S` is initial" and it is not: `Prog S` admits two distinct monad
morphisms into `StateT Nat Id` (breaker §4a), so it is not initial in
monads-and-monad-morphisms, the only category this file's vocabulary
names. Freeness is the correct word for the statement below, and the
initiality that IS true is §6c. -/
theorem prog_is_free {S : Sig} {M : Type → Type v} [Monad M]
    (runit : RightUnit M) (φ : {A : Type} → Prog S A → M A)
    (hφ : IsMonadMorphism S φ) :
    ∃ h : Handler S M,
      (∀ (A : Type) (p : Prog S A), φ p = interpret h p)
        ∧ ∀ g : Handler S M,
            (∀ (A : Type) (p : Prog S A), φ p = interpret g p) → g = h := by
  refine ⟨⟨fun op => φ (Prog.op op)⟩,
    fun _ p => interpret_of_isMonadMorphism φ hφ p, ?_⟩
  intro g hg
  refine handler_eq_of_interpret_eq runit (fun A p => ?_)
  rw [← hg A p]
  exact interpret_of_isMonadMorphism φ hφ p

/-- The name the first draft used, kept as an alias so the packet's
`LAW UP` row and any reader who followed the old prose still resolve —
and pointing at the corrected word. -/
theorem existsUnique_handler {S : Sig} {M : Type → Type v} [Monad M]
    (runit : RightUnit M) (φ : {A : Type} → Prog S A → M A)
    (hφ : IsMonadMorphism S φ) :
    ∃ h : Handler S M,
      (∀ (A : Type) (p : Prog S A), φ p = interpret h p)
        ∧ ∀ g : Handler S M,
            (∀ (A : Type) (p : Prog S A), φ p = interpret g p) → g = h :=
  prog_is_free runit φ hφ

/-! ### 6c. INITIALITY — the other quantifier order, in the other category

Breaker `prog_is_initial_in_S_models` (`Attack.lean` §4b), adopted with
its proof, restated at the equations rather than at `[LawfulMonad M]`
for consistency with §3.

The category: objects are `S`-MODELS `(M, h)` — a monad with a chosen
meaning for each operation — and morphisms are the monad morphisms that
respect the chosen meanings. `(Prog S, idHandler)` is initial there.
Freeness (§6b) fixes a MORPHISM and produces a unique HANDLER;
initiality fixes a HANDLER and produces a unique MORPHISM. -/

/-- The morphism predicate with an EXPLICIT type argument, so a morphism
can be bound by `∃` and compared by `funext`. Breaker's `IsMorphE`. -/
structure IsMorphE (S : Sig) {M : Type → Type v} [Monad M]
    (φ : (A : Type) → Prog S A → M A) : Prop where
  pure_law : ∀ (A : Type) (a : A), φ A (Prog.pure a) = pure a
  bind_law : ∀ (A B : Type) (p : Prog S A) (f : A → Prog S B),
    φ B (p.bind f) = φ A p >>= fun a => φ B (f a)

/-- The two predicates are one predicate, spelled at two binder
strengths. Stated so the file does not carry two unrelated notions of
morphism. -/
theorem isMonadMorphism_of_isMorphE {S : Sig} {M : Type → Type v} [Monad M]
    {φ : (A : Type) → Prog S A → M A} (hφ : IsMorphE S φ) :
    IsMonadMorphism S (fun {A} p => φ A p) :=
  ⟨fun a => hφ.pure_law _ a, fun p f => hφ.bind_law _ _ p f⟩

theorem isMorphE_of_isMonadMorphism {S : Sig} {M : Type → Type v} [Monad M]
    {φ : {A : Type} → Prog S A → M A} (hφ : IsMonadMorphism S φ) :
    IsMorphE S (fun A p => φ (A := A) p) :=
  ⟨fun _ a => hφ.pure_law a, fun _ _ p f => hφ.bind_law p f⟩

/-- **INITIALITY, in the category where it holds.** For every monad and
every handler there is EXACTLY ONE monad morphism out of `Prog S`
sending each operation to its handled meaning — and it is `interpret h`.
This is the theorem the word "initial" names; it was missing, and the
breaker supplied it. -/
theorem prog_is_initial_in_S_models {S : Sig} {M : Type → Type v} [Monad M]
    (lu : LeftUnit M) (ba : BindAssoc M) (runit : RightUnit M)
    (h : Handler S M) :
    ∃ φ : (A : Type) → Prog S A → M A,
      (IsMorphE S φ ∧ ∀ op : S.Op, φ _ (Prog.op op) = h.handle op)
        ∧ ∀ ψ : (A : Type) → Prog S A → M A, IsMorphE S ψ →
            (∀ op : S.Op, ψ _ (Prog.op op) = h.handle op) → ψ = φ := by
  refine ⟨fun _ p => interpret h p,
    ⟨⟨fun _ a => interpret_pure h a,
      fun _ _ p f => interpret_bind_of_equations lu ba h p f⟩,
      fun op => interpret_op_of_rightUnit runit h op⟩, ?_⟩
  intro ψ hψ hop
  have hm := isMonadMorphism_of_isMorphE hψ
  have hh : (⟨fun op => ψ _ (Prog.op op)⟩ : Handler S M) = h :=
    Handler.ext fun op => hop op
  funext A p
  have key :=
    interpret_of_isMonadMorphism (fun {A : Type} (p : Prog S A) => ψ A p) hm p
  rw [key, hh]

/-! ### 6d. The adequacy pin, and the exact extent of its class -/

/-- **The adequacy discharge.** The universal property does not merely
admit `interpret`; it PINS it. Any operator `I` that turns a handler
into a monad morphism agreeing with the handler on single operations IS
`interpret`, pointwise, at every handler, type and program. There is no
wrong-but-passing interpreter.

The honest scope, added on the breaker's HOLE-6: this is a statement
about a class that is EMPTY at some targets — see
`interpret_pinned_is_vacuous_over_collapse`. Where the class is
inhabited is exactly `interpret_inhabits_the_pin`. -/
theorem interpret_pinned {S : Sig} {M : Type → Type v} {A : Type} [Monad M]
    (I : Handler S M → {A : Type} → Prog S A → M A)
    (hmorph : ∀ h : Handler S M, IsMonadMorphism S (fun {_A} p => I h p))
    (hop : ∀ (h : Handler S M) (op : S.Op), I h (Prog.op op) = h.handle op)
    (h : Handler S M) (p : Prog S A) :
    I h p = interpret h p := by
  have key := interpret_of_isMonadMorphism (fun {_A} p => I h p) (hmorph h) p
  have hh : (⟨fun op => I h (Prog.op op)⟩ : Handler S M) = h :=
    Handler.ext fun op => hop h op
  rw [key, hh]

/-- **Which targets admit an `I`.** AMENDED, breaker hand (HOLE-6). The
first draft's anti-vacuity companion carried `[LawfulMonad M]` while the
pin carried `[Monad M]`, so it vouched for only part of the pin's own
quantifier. Restated at the three equations — strictly wider than
`LawfulMonad`, and exactly the condition that makes `interpret` itself
satisfy the pin's two hypotheses. -/
theorem interpret_inhabits_the_pin {S : Sig} {M : Type → Type v} [Monad M]
    (lu : LeftUnit M) (ba : BindAssoc M) (runit : RightUnit M) :
    (∀ h : Handler S M,
        IsMonadMorphism S (fun {_A} (p : Prog S _A) => interpret h p))
      ∧ ∀ (h : Handler S M) (op : S.Op),
          interpret h (Prog.op op) = h.handle op :=
  ⟨fun h => interpret_isMonadMorphism_of_equations lu ba h,
    fun h op => interpret_op_of_rightUnit runit h op⟩

/-- The name the first draft used, kept as an alias. -/
theorem interpret_satisfies_the_property {S : Sig} {M : Type → Type v} [Monad M]
    (lu : LeftUnit M) (ba : BindAssoc M) (runit : RightUnit M) :
    (∀ h : Handler S M,
        IsMonadMorphism S (fun {_A} (p : Prog S _A) => interpret h p))
      ∧ ∀ (h : Handler S M) (op : S.Op),
          interpret h (Prog.op op) = h.handle op :=
  interpret_inhabits_the_pin lu ba runit

/-- **The vacuity witness.** At `Collapse` — the target this module's
own F-LAWFUL falsifier uses — NOTHING satisfies the pin's hypotheses:
`bind_law` forces every `I h (Prog.op op)` to `true`, and
operation-agreement then demands `hFalse.handle () = true`. So "there is
no wrong-but-passing interpreter" is true there only because there is no
interpreter there at all. Breaker
`interpret_pinned_is_vacuous_over_collapse` (`Attack.lean` §7 F1). -/
theorem interpret_pinned_is_vacuous_over_collapse :
    ¬ ∃ I : Handler OneSig Collapse → {A : Type} → Prog OneSig A → Collapse A,
        (∀ h : Handler OneSig Collapse,
          IsMonadMorphism OneSig (fun {_A} (p : Prog OneSig _A) => I h p))
        ∧ (∀ (h : Handler OneSig Collapse) (op : OneSig.Op),
            I h (Prog.op op) = h.handle op) := by
  rintro ⟨I, hmorph, hop⟩
  have hb := (hmorph hFalse).bind_law (Prog.op ()) Prog.pure
  rw [Prog.bind_pure_right] at hb
  have hT : I hFalse (Prog.op ()) = true := hb
  have hF : I hFalse (Prog.op ()) = false := hop hFalse ()
  rw [hT] at hF
  exact Bool.noConfusion hF

/-! ### 6e. The falsifiers L18 and the pin survive -/

private abbrev St := StateT Nat Id

private def hInc : Handler OneSig St := ⟨fun _ => fun s => ((), s + 1)⟩
private def hNop : Handler OneSig St := ⟨fun _ => fun s => ((), s)⟩

/-- A semantics that changes its mind after one step: handle the FIRST
operation with `g`, everything after it with `h`. -/
private def phiDrifts (h g : Handler OneSig St) :
    {A : Type} → Prog OneSig A → St A
  | _, .pure a => pure a
  | _, .vis op k => g.handle op >>= fun r => interpret h (k r)

private def twoOps : Prog OneSig Unit :=
  .vis () fun _ => .vis () fun _ => .pure ()

/-- `phiDrifts` satisfies `pure_law`. ADDED on breaker NOTE-4: the first
draft asserted this in prose and did not state it. -/
theorem phiDrifts_pure_law {A : Type} (h g : Handler OneSig St) (a : A) :
    phiDrifts h g (Prog.pure a) = pure a := rfl

/-- L18 reads the SAME handler off `phiDrifts hInc hNop` that it reads
off `interpret hNop` — which is what makes the disagreement at `twoOps`
a refutation rather than a coincidence. ADDED on breaker NOTE-4. -/
theorem phiDrifts_read_off :
    (⟨fun op => phiDrifts hInc hNop (Prog.op op)⟩ : Handler OneSig St) = hNop :=
  Handler.ext fun _ => rfl

/-- **FALSIFIER for L18's `bind_law` hypothesis.** Keep `pure_law`, drop
`bind_law`, and L18 is FALSE. `phiDrifts hInc hNop` agrees with
`interpret hNop` on every single operation — so the handler L18 reads
off is the SAME one (`phiDrifts_read_off`) — and disagrees at a
two-operation program. Two maps, one induced handler, different values:
the conclusion cannot hold for both.

This is the shape of a realistic wrong implementation, not a pathology:
an interpreter that installs one semantics for the head operation and
another for the tail. -/
theorem bind_law_is_load_bearing :
    (phiDrifts hInc hNop (Prog.op ()) = interpret hNop (Prog.op ()))
      ∧ phiDrifts hInc hNop twoOps ≠ interpret hNop twoOps := by
  refine ⟨rfl, ?_⟩
  intro h
  have h0 : (((), 1) : Unit × Nat) = ((), 0) := congrFun h 0
  exact absurd (congrArg Prod.snd h0) (by decide)

private def IIgnores (_h : Handler OneSig St) :
    {A : Type} → Prog OneSig A → St A := fun p => interpret hNop p

/-- **FALSIFIER for the pin's operation-agreement hypothesis.** An
operator that is a morphism at every handler and IGNORES the handler.
Breaker `pinned_needs_op_agreement` (`Attack.lean` §7 F2). -/
theorem pinned_needs_op_agreement :
    (∀ h : Handler OneSig St,
      IsMonadMorphism OneSig (fun {_A} (p : Prog OneSig _A) => IIgnores h p))
      ∧ IIgnores hInc (Prog.op ()) ≠ interpret hInc (Prog.op ()) := by
  refine ⟨fun _ => interpret_isMonadMorphism hNop, ?_⟩
  intro h
  have h0 : (((), 0) : Unit × Nat) = ((), 1) := congrFun h 0
  exact absurd (congrArg Prod.snd h0) (by decide)

private def IDrifts (h : Handler OneSig St) :
    {A : Type} → Prog OneSig A → St A := fun p => phiDrifts hInc h p

/-- **FALSIFIER for the pin's morphism hypothesis.** An operator that
agrees with every handler on every single operation and is not
`interpret`. Breaker `pinned_needs_the_morphism_law` (`Attack.lean`
§7 F2). -/
theorem pinned_needs_the_morphism_law :
    (∀ (h : Handler OneSig St) (op : OneSig.Op),
      IDrifts h (Prog.op op) = h.handle op)
      ∧ IDrifts hNop twoOps ≠ interpret hNop twoOps :=
  ⟨fun _ _ => rfl, bind_law_is_load_bearing.2⟩

/-! ## 7. The tower is a monoid (L33–L35)

`Handler.through` (`Tower.lean:65`) composes a service implemented as a
program over a lower signature with that signature's handler.
`interpret_through` (L33, `Tower.lean:71`) is on main; §3 re-proves it at
weaker hypotheses and that version is what the laws below use. -/

/-- **L34.** `through` is associative — the composition law of a CATEGORY
whose objects are signatures. AMENDED, breaker hand (HOLE-3): stated at
the two equations `interpret_bind` spends, not at `[LawfulMonad M]`. -/
theorem through_assoc {S T U : Sig} {M : Type → Type v} [Monad M]
    (lu : LeftUnit M) (ba : BindAssoc M)
    (t : Handler S (Prog T)) (u : Handler T (Prog U)) (h : Handler U M) :
    (t.through u).through h = t.through (u.through h) :=
  Handler.ext fun op => by
    show interpret h (interpret u (t.handle op))
      = interpret (u.through h) (t.handle op)
    exact interpret_through_of_equations lu ba u h (t.handle op)

/-- The weakening is real for the tower too: associativity holds over
`Ct`, which has no `LawfulMonad` instance. -/
theorem through_assoc_over_ct {S T U : Sig}
    (t : Handler S (Prog T)) (u : Handler T (Prog U)) (h : Handler U Ct) :
    (t.through u).through h = t.through (u.through h) :=
  through_assoc ct_leftUnit ct_bindAssoc t u h

/-- **L35, right unit.** Reinterpreting through the syntactic identity
changes nothing. No hypothesis at all: the target is `Prog T`. -/
theorem through_id_right {S T : Sig} (t : Handler S (Prog T)) :
    t.through (idHandler (S := T)) = t :=
  Handler.ext fun op => interpret_id (t.handle op)

/-- **L35, left unit.** Implementing a service as "perform the operation
and answer it" and then handling it is the handler itself. AMENDED,
breaker hand (HOLE-3): the proof is the right-unit equation, once.
Breaker `through_id_left_from_right_unit` (`Attack.lean` §3c). -/
theorem through_id_left {S : Sig} {M : Type → Type v} [Monad M]
    (runit : RightUnit M) (h : Handler S M) :
    (idHandler (S := S)).through h = h :=
  Handler.ext fun _op => runit _

/-- And it holds over `RUnit`, where the first draft's statement could
not be typed. -/
theorem through_id_left_over_runit (h : Handler OneSig RUnit) :
    (idHandler (S := OneSig)).through h = h :=
  through_id_left runit_rightUnit h

/-- **The monoid, stated where it actually is one.** `through` is a
binary operation only on the ENDOMORPHISMS at one signature —
`Handler S (Prog S)` — and there it is associative with `idHandler` as a
two-sided unit.

Across signatures the same three facts are a CATEGORY, not a monoid, and
`through_assoc` above is stated in that generality. Neither statement
gives the tower a bottom: `ByteSig` still has no handler
(THE-ALGEBRA L37). -/
theorem through_monoid {S : Sig} (t u v : Handler S (Prog S)) :
    (t.through u).through v = t.through (u.through v)
      ∧ t.through (idHandler (S := S)) = t
      ∧ (idHandler (S := S)).through t = t :=
  ⟨through_assoc leftUnit_of_lawful bindAssoc_of_lawful t u v,
    through_id_right t, through_id_left rightUnit_of_lawful t⟩

/-! ## 8. The boundary — semantics the property does not reach

AMENDED THROUGHOUT, breaker hand (HOLE-5 and HOLE-7).

**The enumeration is the REVIEW's three, not the estate's all.**
THE-ALGEBRA §3.4 found three semantics outside the handler algebra R10
says every semantics is; two more live in this repository and are added
below. Nothing here claims the list is now complete either — it is the
semantics this lane could find.

**(a) `Prog.handleLlm`** (`Interp.lean:184`) is a map
`Prog AgentSig A → Prog CasSig A`, so it is of the right SHAPE. L18
reaches it CONDITIONALLY on `IsMonadMorphism AgentSig`, whose `bind_law`
is precisely the judgment `Interp.lean:19,181-183` asserts and nothing
on main proves. PDD-7 owns discharging it (L32) and computing the
handler (L30).

**(b) `step` / `run` / `stepRooted` / `runRooted`.** The first draft's
reason was "they are not maps `Prog S A → M A` at all". That reason is
FALSE and is withdrawn: `Status CasSig` is a `Type → Type`, so
`RunM := fun A => Word → Status CasSig A × Word` is one, both families
type-check against it, and it even carries a `Monad` instance — the
definitions below ARE the refutation, and they are the breaker's
(`Attack.lean` §5b). The continuation does not leave the shape; it lands
in `Status CasSig A`, indexed by the same `A`.

The REAL obstruction is compositional: at a fixed fuel there is NO
composition law at all (`run_has_no_composition_law`). The difference is
not cosmetic. "Wrong shape" would put the operational semantics outside
the universal property forever; "no composition law at fixed fuel" is a
fact about a fuel discipline — which is the right diagnosis, because
`runP` in (d) is a FUEL-FREE run that is still outside.

**(c) `replayHandler`** (`Handler.lean:279`) IS a handler, so by this
file's theorem it is a semantics — and it is still the wrong one. The
property constrains FORM, not content. The review's two kernel-checked
witnesses (THE-ALGEBRA §3.4c) are untouched, and Q4 stays owed.

**(d) `Cas.Lang.runP`** (`Defun.lean:293`), the direct interpreter of the
defunctionalized table — the semantics the emitter's gate actually
executes. Its domain is `PProg`, not `Prog S A`, so it is neither a
handler nor a map out of `Prog`; and (b)'s reason does not reach it,
because `runP_halts` proves it NEVER reports `.running`. A total
semantics of store programs, outside the property for a third reason.

**(e) `Cas.Lang.wp` / `Cas.Lang.wlp`** (`Wp.lean:150,154`, PDD-2's
castle, landed in this same wave). CONTRAVARIANT — postconditions to
preconditions — so it is not of the shape `Prog S A → M A` for any `M`,
and no reading of R10 reaches it. The first draft's claim-scope honoured
the WLP/WP distinction as a class and then did not place the estate's
own WLP/WP transformer against the property being scoped. -/

section Boundary

variable (H : Bytes → Addr32)

/-- The run codomain as a `Type → Type`: the shape objection, refuted by
construction. Breaker `Attack.lean` §5b. -/
def RunM (A : Type) : Type := Word → Status CasSig A × Word

/-- A monad structure on it, so `IsMonadMorphism` is even statable
there: `pure` halts, `bind` threads the word, fuel exhaustion refuses. -/
instance : Monad RunM where
  pure a := fun w => (.done a, w)
  bind m k := fun w =>
    match m w with
    | (.done a, w') => k a w'
    | (.running _, w') => (.refused (.failed "out of fuel"), w')
    | (.refused r, w') => (.refused r, w')

/-- `run H f` IS a map `Prog CasSig A → M A`, for `M := RunM`. -/
def runAsMap (fuel : Nat) : {A : Type} → Prog CasSig A → RunM A :=
  fun p => run H fuel p

/-- So is `step H`. -/
def stepAsMap : {A : Type} → Prog CasSig A → RunM A := fun p => step H p

private def loadOnce (a : Addr32) : Prog CasSig Unit :=
  .vis (CasE.load a) fun _ => .pure ()

private def loadTwice (a : Addr32) : Prog CasSig Unit :=
  .vis (CasE.load a) fun _ => .vis (CasE.load a) fun _ => .pure ()

/-- At fuel 3 one load and two loads are the SAME run, at every word:
both halt `done` where the address binds, both refuse identically where
it does not. Breaker `Attack.lean` §5c. -/
theorem run3_load_once_eq_twice (a : Addr32) :
    (fun w => run H 3 (loadOnce a) w) = (fun w => run H 3 (loadTwice a) w) := by
  funext w
  cases hf : Word.find w a <;> simp [loadOnce, loadTwice, run, step, hf]

/-- **THE BOUNDARY THEOREM.** No binary operation on run-results
reproduces the run of a bind: two programs with the SAME fixed-fuel run
have composites that differ. That kills EVERY candidate composition law
at once, for any monad structure whatsoever, because any `bind` is in
particular a function of its two arguments — so `run H 3` is not a monad
morphism out of `Prog CasSig` under any structure on its codomain, and
the obstruction is well-definedness rather than the choice of `bind`.

Breaker `run_has_no_composition_law` (`Attack.lean` §5c), adopted. It
replaces `run_composite_outruns_its_parts` as the law; that theorem is
kept below as the witness it always was. -/
theorem run_has_no_composition_law (a : Addr32) (n : Node) :
    ¬ ∃ comp : (Word → Status CasSig Unit × Word) →
        (Unit → Word → Status CasSig Unit × Word) →
        (Word → Status CasSig Unit × Word),
      ∀ (p : Prog CasSig Unit) (f : Unit → Prog CasSig Unit),
        (fun w => run H 3 (p.bind f) w)
          = comp (fun w => run H 3 p w) (fun u w => run H 3 (f u) w) := by
  rintro ⟨comp, hcomp⟩
  have h1 := hcomp (loadOnce a) (fun _ => loadOnce a)
  have h2 := hcomp (loadTwice a) (fun _ => loadOnce a)
  have hcc := congrArg
    (fun z => comp z (fun (_ : Unit) w => run H 3 (loadOnce a) w))
    (run3_load_once_eq_twice H a)
  have key := h1.trans (hcc.trans h2.symm)
  have hw := congrFun key [Binding.mk a n]
  simp [loadOnce, loadTwice, Prog.bind, run, step, Word.find] at hw

/-- The first draft's witness, RENAMED to what it proves (breaker
HOLE-5): at fuel 2 each half of a composite has DONE-halted while the
composite is still RUNNING. That is evidence for non-compositionality,
not the statement of it — the statement is
`run_has_no_composition_law` above. The old name
(`run_fixed_fuel_is_not_compositional`) promised the law and delivered
the witness. -/
theorem run_composite_outruns_its_parts (a : Addr32) (n : Node) :
    run H 2 (loadOnce a) [Binding.mk a n] = (.done (), [Binding.mk a n])
      ∧ run H 2 ((loadOnce a).bind fun _ => loadOnce a) [Binding.mk a n]
          = (.running (Prog.pure ()), [Binding.mk a n]) := by
  refine ⟨?_, ?_⟩
  · simp [loadOnce, run, step, Word.find]
  · simp [loadOnce, Prog.bind, run, step, Word.find]

end Boundary

/-! ### The fourth and fifth semantics, as shapes

Each definition type-checks against the shipped declaration, which is
the witness. Breaker `Attack.lean` §6. -/

/-- `runP`'s shape: `PProg` in, no `Prog`, no monad. -/
def runPShape :
    (Bytes → Addr32) → PProg → Word → Status CasSig Addr32 × Word := runP

/-- And it never reports `.running`, so (b)'s reason does not reach
it. `runP_halts` is already on main. -/
theorem runP_never_running (H : Bytes → Addr32) (p : PProg) (w : Word) :
    (runP H p w).1.isRunning = false := runP_halts H p w

/-- `wp`'s shape: postconditions to preconditions. Contravariant, so no
`M` and no morphism law can be written for it. -/
def wpShape : (Bytes → Addr32) → PProg → WPost → WPre := wp

/-- `wlp` likewise — the partial-correctness twin. -/
def wlpShape : (Bytes → Addr32) → PProg → WPost → WPre := wlp

/-- A program at `Type 1`. Nothing of the form `interpret h` accepts it,
for any handler over any `M : Type → Type v` — so R10's "a semantics IS
a handler" is not merely unproved for such programs; they have no
handler semantics at all. Breaker NOTE-5 (`Attack.lean` §7 F4). -/
def bigProg : Prog OneSig Type := .pure Nat

end Cas.Lang
