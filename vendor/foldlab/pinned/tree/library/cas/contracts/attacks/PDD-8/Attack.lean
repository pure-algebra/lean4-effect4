import Cas.Backend.Universal
import Cas.Lang.Wp

/-!
# PDD-8 — the adversarial record

WHAT THIS FILE IS. The independent breaker's attack against the PDD-8
contract packet (`library/cas/contracts/PDD-8.contract.md`, commit
`8f821ffa`) and its castle (`library/cas/Cas/Backend/Universal.lean`,
commits `6ce34fff` and `8a241313`). Every counter-witness, every
re-elaboration and every failed break attempt is here, whether it broke
something or not: a failed break is the packet's earned confidence, and
earned confidence is record too.

```
BREAKER    independent; did not build this castle
SUBJECT    8a241313  PDD-8: close the vacuity reading of the adequacy pin
CASTLE     6ce34fff  PDD-8: the universal property proved
PACKET     8f821ffa  PDD-8: the contract packet
```

IMPORTS. `Cas.Backend.Universal` (the castle) and `Cas.Lang.Wp` — the
latter only so §6's fourth-semantics witness can name `wp` and `runP`
in the same environment that holds the castle. Nothing imports this
file.

THIS FILE MUST NOT ENTER ANY LAKE LIBRARY TARGET. It is adversarial
apparatus, not library content. It sits under `contracts/attacks/`,
outside every `srcDir` and `globs` that `lakefile.toml` declares for
`Cas`, `CasWp`, `CasBackend`, `CasExamples` and `Gate`, so it is
outside `Walk.libraryImports` and moves no byte of any emitted surface.
It is elaborated by hand —
`lake env lean contracts/attacks/PDD-8/Attack.lean` from `library/cas`
— and never by `lake build`. Adding it to a target is a promotion, and
a promotion is a ruling.

NO `sorry`, no `native_decide`, no `ofReduceBool`.

Verdict, findings and the full failed-attempt list: `RESULTS.md` beside
this file.
-/

namespace Cas.Lang.AttackPDD8

open Cas Cas.Lang

/-! ## 1. The signature and the two monads the castle uses, re-declared

The castle's falsifier apparatus is `private`, so none of it is visible
here. Everything the attack needs is re-declared under this namespace —
which is itself a check: if a castle falsifier only works because of
something in its own file, the re-declaration will not reproduce it. -/

/-- The castle's `OneSig`, re-declared: one operation, answering `Unit`. -/
def OneSig : Sig := ⟨Unit, fun _ => Unit⟩

/-- A signature with two operations and a `Bool` answer — the smallest
carrier at which an interpretation can be NON-CONSTANT, which §2 needs
and `OneSig` cannot supply. -/
def BoolSig : Sig := ⟨Bool, fun _ => Bool⟩

/-- The castle's `Collapse`, re-declared: `Bool` as a constant functor
with the degenerate monad structure that answers `true` to everything. -/
def Collapse : Type → Type := fun _ => Bool

instance : Monad Collapse where
  pure _ := true
  bind _ _ := true

def hTrue : Handler OneSig Collapse := ⟨fun _ => true⟩
def hFalse : Handler OneSig Collapse := ⟨fun _ => false⟩

theorem collapse_interpret {S : Sig} {A : Type} (h : Handler S Collapse)
    (p : Prog S A) : interpret h p = true := by
  induction p with
  | pure a => rfl
  | vis op k ih => rfl

abbrev St := StateT Nat Id

def hInc : Handler OneSig St := ⟨fun _ => fun s => ((), s + 1)⟩
def hNop : Handler OneSig St := ⟨fun _ => fun s => ((), s)⟩

/-! ## 2. THE UNIVERSAL PROPERTY'S TEETH — is L18's bare `Monad` hollow?

The castle DROPPED the review exhibit's `[LawfulMonad M]` from L18 and
recorded the drop as "a strictly stronger theorem". A strictly stronger
theorem is worth nothing if the hypothesis it kept secretly re-imposes
what it dropped. Three questions, three answers.

### 2a. `IsMonadMorphism` DOES secretly encode lawfulness — on the image

`bind_law` instantiated at `Prog.pure` on either side derives the two
unit laws, and at a double bind derives associativity — all restricted
to values of the form `φ p`. So the hypothesis is SELF-LAWFULIZING:
over any `M`, a morphism out of `Prog S` drags the monad laws with it
onto its own image. This is the strongest form of the "hollow" charge
and it is TRUE as far as it goes. §2b and §2c say how far. -/

section ImageLaws

variable {S : Sig} {M : Type → Type} [Monad M]
  (φ : {A : Type} → Prog S A → M A)

/-- LEFT UNIT, on the image: `bind_law` at `p := Prog.pure a`. Nothing
about `M` is assumed. -/
theorem image_left_unit (hφ : IsMonadMorphism S φ) {A B : Type} (a : A)
    (f : A → Prog S B) :
    (pure a : M A) >>= (fun x => φ (f x)) = φ (f a) := by
  have h := hφ.bind_law (Prog.pure a) f
  rw [hφ.pure_law] at h
  exact h.symm

/-- RIGHT UNIT, on the image: `bind_law` at `f := Prog.pure`, using
`Prog.bind_pure_right`. -/
theorem image_right_unit (hφ : IsMonadMorphism S φ) {A : Type}
    (p : Prog S A) : φ p >>= (fun a => (pure a : M A)) = φ p := by
  have h := hφ.bind_law p Prog.pure
  rw [Prog.bind_pure_right] at h
  simp only [hφ.pure_law] at h
  exact h.symm

/-- ASSOCIATIVITY, on the image: `bind_law` twice against
`Prog.bind_assoc'`. -/
theorem image_assoc (hφ : IsMonadMorphism S φ) {A B C : Type}
    (p : Prog S A) (f : A → Prog S B) (g : B → Prog S C) :
    (φ p >>= fun a => φ (f a)) >>= (fun b => φ (g b))
      = φ p >>= fun a => (φ (f a) >>= fun b => φ (g b)) := by
  calc (φ p >>= fun a => φ (f a)) >>= (fun b => φ (g b))
      = φ (p.bind f) >>= (fun b => φ (g b)) := by rw [hφ.bind_law]
    _ = φ ((p.bind f).bind g) := (hφ.bind_law _ g).symm
    _ = φ (p.bind fun a => (f a).bind g) := by rw [Prog.bind_assoc']
    _ = φ p >>= (fun a => φ ((f a).bind g)) := hφ.bind_law _ _
    _ = φ p >>= fun a => (φ (f a) >>= fun b => φ (g b)) := by
          exact congrArg _ (funext fun a => hφ.bind_law (f a) g)

end ImageLaws

/-! ### 2b. The strengthening is NOT hollow — an unlawful monad WITH a
non-constant `IsMonadMorphism` out of `Prog S`

`IsMonadMorphism` mentions `pure` and `>>=` and NOTHING else, while
`LawfulMonad` also carries `LawfulApplicative`/`LawfulFunctor`. `Ct`
below is the Writer-over-`Nat` monad with a DELIBERATELY WRONG `map`:
its `pure`/`bind` are impeccable, its `map` bumps the counter, so
`id_map` fails and Lean has no `LawfulMonad Ct` instance to offer. The
castle's L18 applies to it. A `[LawfulMonad M]`-bearing L18 does not.
That is the strengthening, cashed at a concrete target where the
conclusion is a real equation between distinguishable values. -/

/-- The counting monad with a poisoned `map`. -/
def Ct (A : Type) : Type := A × Nat

instance : Monad Ct where
  pure a := (a, 0)
  bind x f := ((f x.1).1, x.2 + (f x.1).2)
  map f x := (f x.1, x.2 + 1)

def ctZero : Ct Nat := (0, 0)

/-- `Ct` is NOT lawful: `id_map` fails, because `map` counts. -/
theorem ct_not_lawful : ¬ Nonempty (LawfulMonad Ct) := by
  rintro ⟨_⟩
  have h : id <$> ctZero = ctZero := LawfulFunctor.id_map _
  exact absurd (congrArg Prod.snd h) (by decide)

/-- A handler into `Ct` that costs one tick per operation. -/
def hTick : Handler BoolSig Ct := ⟨fun b => (b, 1)⟩

/-- A second, distinguishable handler into `Ct`. -/
def hFlip : Handler BoolSig Ct := ⟨fun b => (!b, 1)⟩

/-- `interpret` into `Ct` respects `bind`, proved WITHOUT a
`LawfulMonad Ct` instance — there is none — by direct induction over
the concrete `bind`. -/
theorem ct_interpret_bind (h : Handler BoolSig Ct) {A B : Type}
    (p : Prog BoolSig A) (f : A → Prog BoolSig B) :
    interpret h (p.bind f)
      = interpret h p >>= fun a => interpret h (f a) := by
  induction p with
  | pure a =>
    simp only [interpret, Prog.bind, bind, pure, Nat.zero_add]
    exact Prod.ext rfl rfl
  | vis op k ih =>
    simp only [interpret, Prog.bind, bind, ih]
    exact Prod.ext rfl (by simp [Nat.add_assoc])

/-- **The witness.** `interpret hTick` is an `IsMonadMorphism` out of
`Prog BoolSig` into a monad with no `LawfulMonad` instance, and it is
non-constant: it separates the two one-operation programs and it
separates `hTick` from `hFlip`. So the class of targets L18 gained by
dropping `[LawfulMonad M]` is NON-EMPTY and NON-DEGENERATE. -/
theorem bare_monad_strengthening_is_real :
    IsMonadMorphism BoolSig (fun {_A} (p : Prog BoolSig _A) => interpret hTick p)
      ∧ interpret hTick (Prog.op true) ≠ interpret hTick (Prog.op false)
      ∧ interpret hTick (Prog.op true) ≠ interpret hFlip (Prog.op true) := by
  refine ⟨⟨fun a => rfl, fun p f => ct_interpret_bind hTick p f⟩, ?_, ?_⟩
  · intro h
    exact Bool.noConfusion (congrArg Prod.fst h)
  · intro h
    exact Bool.noConfusion (congrArg Prod.fst h)

/-! ### 2c. …and it is not free either — an unlawful monad where the
hypothesis is UNINHABITABLE

`Shift` is the Writer-over-`Nat` monad whose `pure` costs ONE instead of
zero. Nothing is a monad morphism out of `Prog S` into it: §2a's right
unit forces `n = n + 1`. So "bare `Monad`" does not mean "every monad";
the theorem's reach over unlawful targets is a proper subclass on both
sides, which is the honest reading of the drop and is not written down
anywhere in the packet. -/

def Shift (A : Type) : Type := Nat × A

instance : Monad Shift where
  pure a := (1, a)
  bind x f := (x.1 + (f x.2).1, (f x.2).2)

/-- **The counter-witness.** No monad morphism out of `Prog OneSig`
lands in `Shift`, for any signature with an inhabited answer type — the
image right-unit law of §2a is already contradictory. -/
theorem shift_admits_no_morphism
    (φ : {A : Type} → Prog OneSig A → Shift A) :
    ¬ IsMonadMorphism OneSig φ := by
  intro hφ
  have h := image_right_unit φ hφ (Prog.pure ())
  have : (φ (Prog.pure ())).1 + 1 = (φ (Prog.pure ())).1 := congrArg Prod.fst h
  omega

/-! ## 3. THE FALSIFIER TRIAD — re-elaborated, then attacked on scope

§3a re-proves all three castle falsifiers from re-declared apparatus:
none of them depends on anything private to the castle's file. §3b–§3d
attack what they actually establish. -/

/-! ### 3a. Re-elaboration -/

/-- Castle `uniqueness_needs_lawful`, re-proved here. -/
theorem re_uniqueness_needs_lawful :
    (∀ (A : Type) (p : Prog OneSig A), interpret hTrue p = interpret hFalse p)
      ∧ hTrue ≠ hFalse := by
  refine ⟨fun _ p => by rw [collapse_interpret, collapse_interpret], ?_⟩
  intro h
  exact Bool.noConfusion (congrArg (fun x => Handler.handle x ()) h)

/-- Castle `single_type_agreement_is_not_enough`, re-proved here. -/
theorem re_single_type_agreement_is_not_enough :
    (∀ p : Prog OneSig Empty, interpret hTrue p = interpret hFalse p)
      ∧ hTrue ≠ hFalse := by
  refine ⟨fun p => (?_ : False).elim, ?_⟩
  · induction p with
    | pure a => exact a.elim
    | vis op k ih => exact ih ()
  · intro h
    exact Bool.noConfusion (congrArg (fun x => Handler.handle x ()) h)

/-- Castle `phiDrifts`, re-declared. -/
def phiDrifts (h g : Handler OneSig St) :
    {A : Type} → Prog OneSig A → St A
  | _, .pure a => pure a
  | _, .vis op k => g.handle op >>= fun r => interpret h (k r)

def twoOps : Prog OneSig Unit :=
  .vis () fun _ => .vis () fun _ => .pure ()

/-- Castle `bind_law_is_load_bearing`, re-proved here. -/
theorem re_bind_law_is_load_bearing :
    (phiDrifts hInc hNop (Prog.op ()) = interpret hNop (Prog.op ()))
      ∧ phiDrifts hInc hNop twoOps ≠ interpret hNop twoOps := by
  refine ⟨rfl, ?_⟩
  intro h
  have h0 : (((), 1) : Unit × Nat) = ((), 0) := congrFun h 0
  exact absurd (congrArg Prod.snd h0) (by decide)

/-! ### 3b. The two halves F-BIND asserts in prose and does not state

The castle's docstring says `phiDrifts` "respects `pure` and nothing
else" and that L18 "would read off the SAME handler". Neither is in the
theorem. Both are true; both are one line; here they are, so the
falsifier's own premises are kernel-checked rather than narrated. -/

/-- `phiDrifts` satisfies `pure_law`. -/
theorem phiDrifts_pure_law (h g : Handler OneSig St) {A : Type} (a : A) :
    phiDrifts h g (Prog.pure a) = pure a := rfl

/-- L18 reads the SAME handler off `phiDrifts hInc hNop` that it reads
off `interpret hNop` — which is what makes the disagreement at `twoOps`
a refutation rather than a coincidence. -/
theorem phiDrifts_read_off :
    (⟨fun op => phiDrifts hInc hNop (Prog.op op)⟩ : Handler OneSig St)
      = hNop :=
  Handler.ext fun _ => rfl

/-! ### 3c. `uniqueness_needs_lawful`'s witness — WHICH axiom, and how
much of `LawfulMonad` L17 actually spends

The scope question the packet does not ask: `Collapse` fails
`LawfulMonad`, but L17's proof reaches for exactly ONE equation —
`x >>= pure = x`, through `interpret_op`. Everything else in
`LawfulMonad` is surplus. So F-LAWFUL establishes "not NO hypothesis",
not "THIS hypothesis": by the castle's own standard for L18 — drop what
the proof does not use — L17 is carrying three unused laws. -/

def cFalse : Collapse Unit := false

/-- The named axiom `Collapse` violates: `LawfulMonad.pure_bind`. -/
theorem collapse_not_lawful : ¬ Nonempty (LawfulMonad Collapse) := by
  rintro ⟨_⟩
  have h : (pure () >>= fun _ => cFalse) = cFalse := LawfulMonad.pure_bind () _
  have hb : (true : Bool) = false := h
  exact Bool.noConfusion hb

/-- **L17 under a strictly weaker hypothesis.** Uniqueness needs only
the right-unit equation at the handler's own answers; no other
`LawfulMonad` field appears. -/
theorem uniqueness_from_right_unit {S : Sig} {M : Type → Type} [Monad M]
    (runit : ∀ {A : Type} (x : M A), x >>= (fun a => (pure a : M A)) = x)
    {h g : Handler S M}
    (e : ∀ op : S.Op, interpret h (Prog.op op) = interpret g (Prog.op op)) :
    h = g :=
  Handler.ext fun op =>
    calc h.handle op = h.handle op >>= (fun a => pure a) := (runit _).symm
      _ = interpret h (Prog.op op) := rfl
      _ = interpret g (Prog.op op) := e op
      _ = g.handle op >>= (fun a => pure a) := rfl
      _ = g.handle op := runit _

/-- A monad with the right-unit equation and NOTHING else: the counting
monad whose `bind` charges a surcharge for a non-zero cost. -/
def RUnit (A : Type) : Type := Nat × A

instance : Monad RUnit where
  pure a := (0, a)
  bind x f := (if (f x.2).1 = 0 then x.1 else x.1 + (f x.2).1 + 1, (f x.2).2)

theorem runit_right_unit {A : Type} (x : RUnit A) :
    x >>= (fun a => (pure a : RUnit A)) = x := rfl

def ruOne : RUnit Nat := (1, 0)

/-- `RUnit` is NOT lawful: `pure_bind` fails at the surcharge. -/
theorem runit_not_lawful : ¬ Nonempty (LawfulMonad RUnit) := by
  rintro ⟨_⟩
  have h : (pure 0 >>= fun _ => ruOne) = ruOne := LawfulMonad.pure_bind 0 _
  have hn : (2 : Nat) = 1 := congrArg Prod.fst h
  exact absurd hn (by decide)

/-- **The payoff.** Uniqueness is TRUE over `RUnit`, and the castle's
L17 cannot even be STATED there — there is no `LawfulMonad RUnit`
instance to supply. The hypothesis is stronger than the proof. -/
theorem l17_holds_where_the_castle_cannot_state_it
    {h g : Handler OneSig RUnit}
    (e : ∀ op : OneSig.Op,
      interpret h (Prog.op op) = interpret g (Prog.op op)) : h = g :=
  uniqueness_from_right_unit runit_right_unit e

/-- The same for the tower's left unit: `through_id_left` spends only
the right-unit equation, and holds over `RUnit`, where the castle's
statement does not typecheck. -/
theorem through_id_left_from_right_unit {S : Sig} {M : Type → Type} [Monad M]
    (runit : ∀ {A : Type} (x : M A), x >>= (fun a => (pure a : M A)) = x)
    (h : Handler S M) : (idHandler (S := S)).through h = h :=
  Handler.ext fun _op => runit _

theorem through_id_left_over_runit (h : Handler OneSig RUnit) :
    (idHandler (S := OneSig)).through h = h :=
  through_id_left_from_right_unit runit_right_unit h

/-! ### 3d. F-ONETYPE's headline is FALSE at its own signature

The packet's line is "L17 read at ONE answer type proves nothing"
(F-ONETYPE). The witness proves something strictly weaker: at the
answer type `Empty` it proves nothing, because `Prog S Empty` is
uninhabited. At `Unit` — the answer type of `OneSig`'s only operation,
the very signature the falsifier is built on — a single answer type is
ENOUGH. -/

/-- **The counter-witness to F-ONETYPE as stated.** One answer type,
chosen well, forces handler equality outright. -/
theorem one_type_can_be_enough {M : Type → Type} [Monad M] [LawfulMonad M]
    {h g : Handler OneSig M}
    (e : ∀ p : Prog OneSig Unit, interpret h p = interpret g p) : h = g :=
  Handler.ext fun op =>
    calc h.handle op = interpret h (Prog.op op) := (interpret_op h op).symm
      _ = interpret g (Prog.op op) := e (Prog.op op)
      _ = g.handle op := interpret_op g op

/-! ## 4. INITIALITY'S SUBJECT — which category?

`existsUnique_handler`'s docstring reads "**`Prog S` is initial**: every
monad morphism out of it is induced by exactly ONE handler." The colon
glosses one claim with a different one. The theorem after the colon is a
HOM-SET BIJECTION `Handler S M ≃ Mor(Prog S, M)` — FREENESS. The word
before the colon, read in the category the file's own vocabulary names
(monads and monad morphisms — `IsMonadMorphism` is the only morphism
notion in the file), is FALSE, and §4a exhibits the two morphisms that
make it false. §4b states and proves the initiality that IS true, in the
category where it holds, so the finding comes with its repair. -/

/-! ### 4a. `Prog S` is NOT initial in monads-and-monad-morphisms -/

/-- **The counter-witness to the docstring's headline.** Two DISTINCT
monad morphisms out of `Prog OneSig` into one lawful target. An initial
object admits exactly one morphism to each object; `Prog OneSig` admits
at least two into `StateT Nat Id`. Freeness is not initiality, and the
theorem below the docstring is the former. -/
theorem prog_is_not_initial_among_monads :
    IsMonadMorphism OneSig (fun {_A} (p : Prog OneSig _A) => interpret hInc p)
      ∧ IsMonadMorphism OneSig (fun {_A} (p : Prog OneSig _A) => interpret hNop p)
      ∧ interpret hInc (Prog.op ()) ≠ interpret hNop (Prog.op ()) := by
  refine ⟨interpret_isMonadMorphism hInc, interpret_isMonadMorphism hNop, ?_⟩
  intro h
  have h0 : (((), 1) : Unit × Nat) = ((), 0) := congrFun h 0
  exact absurd (congrArg Prod.snd h0) (by decide)

/-! ### 4b. The initiality that IS true — and is not in the castle

The right category has objects `(M, h)` — a monad with a chosen meaning
for each operation — and morphisms the monad morphisms that respect the
chosen meanings. `Prog S` with `idHandler` is initial THERE: for every
object there is exactly ONE morphism to it. That statement quantifies
over MORPHISMS at a fixed handler; `existsUnique_handler` quantifies
over HANDLERS at a fixed morphism. They are inter-derivable, and only
one of them is in the castle. -/

/-- The morphism predicate with an EXPLICIT type argument, so a morphism
can be bound by `∃` and compared by `funext`. -/
structure IsMorphE (S : Sig) {M : Type → Type} [Monad M]
    (φ : (A : Type) → Prog S A → M A) : Prop where
  pure_law : ∀ (A : Type) (a : A), φ A (Prog.pure a) = pure a
  bind_law : ∀ (A B : Type) (p : Prog S A) (f : A → Prog S B),
    φ B (p.bind f) = φ A p >>= fun a => φ B (f a)

/-- **The missing theorem.** `(Prog S, idHandler)` is INITIAL in the
category of `S`-models: for every monad `M` and every handler `h` there
is exactly one monad morphism out of `Prog S` sending each operation to
its handled meaning — and it is `interpret h`. -/
theorem prog_is_initial_in_S_models {S : Sig} {M : Type → Type}
    [Monad M] [LawfulMonad M] (h : Handler S M) :
    ∃ φ : (A : Type) → Prog S A → M A,
      (IsMorphE S φ ∧ ∀ op : S.Op, φ _ (Prog.op op) = h.handle op)
        ∧ ∀ ψ : (A : Type) → Prog S A → M A, IsMorphE S ψ →
            (∀ op : S.Op, ψ _ (Prog.op op) = h.handle op) → ψ = φ := by
  refine ⟨fun _ p => interpret h p,
    ⟨⟨fun _ a => interpret_pure h a, fun _ _ p f => interpret_bind h p f⟩,
      fun op => interpret_op h op⟩, ?_⟩
  intro ψ hψ hop
  have hm : IsMonadMorphism S (fun {A : Type} (p : Prog S A) => ψ A p) :=
    ⟨fun a => hψ.pure_law _ a, fun p f => hψ.bind_law _ _ p f⟩
  have hh : (⟨fun op => ψ _ (Prog.op op)⟩ : Handler S M) = h :=
    Handler.ext fun op => hop op
  funext A p
  have key := interpret_of_isMonadMorphism (fun {A : Type} (p : Prog S A) => ψ A p) hm p
  rw [key, hh]

/-! ## 5. THE BOUNDARY — the witness, its reason, and the theorem the
name promises

§7(b) of the castle gives a REASON for putting `step`/`run` outside:
"they are not maps `Prog S A → M A` at all". §5a re-verifies the
witness. §5b refutes the reason. §5c supplies the theorem the name
`run_fixed_fuel_is_not_compositional` and the packet's FALSIFIER BOUND
promise and the castle does not carry. -/

section Boundary

variable (H : Bytes → Addr32)

def loadOnce (a : Addr32) : Prog CasSig Unit :=
  .vis (CasE.load a) fun _ => .pure ()

def loadTwice (a : Addr32) : Prog CasSig Unit :=
  .vis (CasE.load a) fun _ => .vis (CasE.load a) fun _ => .pure ()

/-! ### 5a. The castle's witness, re-computed -/

/-- Castle `run_fixed_fuel_is_not_compositional`, re-proved here. -/
theorem re_run_fixed_fuel_is_not_compositional (a : Addr32) (n : Node) :
    run H 2 (loadOnce a) [Binding.mk a n] = (.done (), [Binding.mk a n])
      ∧ run H 2 ((loadOnce a).bind fun _ => loadOnce a) [Binding.mk a n]
          = (.running (Prog.pure ()), [Binding.mk a n]) := by
  refine ⟨?_, ?_⟩
  · simp [loadOnce, run, step, Word.find]
  · simp [loadOnce, Prog.bind, run, step, Word.find]

/-! ### 5b. The castle's stated REASON is false

`Status CasSig` is a `Type → Type`, so `fun A => Word → Status CasSig A × Word`
is one too, and both `step H` and `run H f` are families
`{A : Type} → Prog CasSig A → M A` over it. The definitions below
type-check; that IS the refutation. The obstruction is compositional,
not shape-theoretic, and the difference matters because "wrong shape"
would put `run` outside forever while "no composition law" is a fact
about a particular fuel discipline. -/

def RunM (A : Type) : Type := Word → Status CasSig A × Word

/-- A monad structure on the run codomain, so the objection "there is
no `Monad M` to state `IsMonadMorphism` over" is closed too: `pure`
halts, `bind` threads the word, and fuel exhaustion is a refusal. -/
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

/-- So is `step H`. The continuation "escaping into the codomain" does
not leave the shape: it lands in `Status CasSig A`, which is indexed by
the same `A`. -/
def stepAsMap : {A : Type} → Prog CasSig A → RunM A :=
  fun p => step H p

/-! ### 5c. The theorem the name promises

Non-compositionality is the statement that `run H f (p.bind g)` is not a
FUNCTION of `run H f p` and `run H f ∘ g`. The castle exhibits one
composite that outruns its parts, which is evidence; the statement needs
two programs with the SAME fixed-fuel run whose composites differ. At
fuel 3, one load and two loads run identically at every word — both halt
`done` where the address binds and refuse identically where it does not
— and binding a third load separates them. That kills EVERY candidate
composition law at once, for any monad structure whatsoever, because any
`bind` is in particular a function of its two arguments. -/

/-- At fuel 3 one load and two loads are the SAME run, at every word. -/
theorem run3_load_once_eq_twice (a : Addr32) :
    (fun w => run H 3 (loadOnce a) w) = (fun w => run H 3 (loadTwice a) w) := by
  funext w
  cases hf : Word.find w a <;> simp [loadOnce, loadTwice, run, step, hf]

/-- **The missing boundary theorem.** No binary operation on run-results
reproduces the run of a bind. `run H 3` is therefore not a monad
morphism out of `Prog CasSig` under ANY monad structure on its
codomain — the obstruction is well-definedness, not the choice of
`bind`. -/
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

end Boundary

/-! ## 6. A FOURTH SEMANTICS — and a FIFTH — that the packet's boundary
neither classifies nor can classify by its stated reasons

The packet's claim-scope enumerates THREE semantics outside the handler
algebra (`handleLlm`, the `step`/`run` family, `replayHandler`) and
offers reasons for each. Two more live in this very repository, in
modules the same wave landed, and neither reason reaches them.

**Fourth: `Cas.Lang.runP`** (`Cas/Lang/Defun.lean:293`) — the direct
interpreter of the defunctionalized table. Its domain is `PProg`, not
`Prog S A`, so it is neither a handler nor a map out of `Prog`; and the
packet's reason for excluding fueled runs ("a fueled run reports
`.running`") does NOT apply to it, because `runP_halts` proves it never
reports `.running`. It is a TOTAL semantics of store programs sitting
outside the universal property's reach for a reason the packet does not
name.

**Fifth: `Cas.Lang.wp` / `Cas.Lang.wlp`** (`Cas/Lang/Wp.lean:150,154`,
PDD-2's castle) — the predicate-transformer semantics. It is
CONTRAVARIANT: it maps postconditions to preconditions, so it is not of
the shape `Prog S A → M A` in any monad `M`, and no reading of R10's
"a semantics IS a handler" reaches it. The packet's `claim-scope`
section names the WLP/WP distinction as a class it honours and then does
not place the estate's own WLP/WP transformer against the property.

The shapes are written out below rather than asserted; each definition
type-checks against the shipped declaration, which is the witness. -/

section FourthSemantics

/-- `runP`'s shape, written out: `PProg` in, no `Prog`, no monad. -/
def runPShape :
    (Bytes → Addr32) → PProg → Word → Status CasSig Addr32 × Word := runP

/-- And it never reports `.running`, so the packet's stated reason for
excluding the fueled runs does not reach it. -/
theorem runP_is_not_a_fuelled_run (H : Bytes → Addr32) (p : PProg) (w : Word) :
    (runP H p w).1.isRunning = false := runP_halts H p w

/-- `wp`'s shape: postconditions to preconditions. Contravariant, so no
`M` and no morphism law can be written for it. -/
def wpShape : (Bytes → Addr32) → PProg → WPost → WPre := wp

/-- `wlp` likewise — the partial-correctness twin. -/
def wlpShape : (Bytes → Addr32) → PProg → WPost → WPre := wlp

end FourthSemantics

/-! ## 7. The breaker's own attempts, pass or fail

Every attempt is recorded, including the ones that failed to break
anything: a failed break is earned confidence and earned confidence is
record. -/

/-! ### F1 — `interpret_pinned` is VACUOUS at the castle's own unlawful
monad, and its anti-vacuity companion does not cover it

Commit `8a241313` added `interpret_satisfies_the_property` to "close the
vacuity reading of the adequacy pin". That companion carries
`[LawfulMonad M]`. `interpret_pinned` does not. At `Collapse` — the very
target the castle's own F-LAWFUL falsifier uses — the pin's hypothesis
class is EMPTY, so "there is no wrong-but-passing interpreter" is true
there only because there is no interpreter at all. FIRED. -/

/-- **The vacuity witness.** No operator satisfies `interpret_pinned`'s
two hypotheses over `Collapse`: `bind_law` forces every `I h (Prog.op op)`
to `true`, and `hop` then demands `hFalse.handle () = true`. -/
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

/-! ### F2 — `interpret_pinned`'s two hypotheses ARE load-bearing

The castle states the pin and never falsifies its hypotheses, though the
packet applies exactly that discipline to L17 (F-LAWFUL) and L18
(F-BIND). Both drops are supplied here, and both fire. -/

/-- Drop `hop`: an operator that ignores its handler. It is a morphism
at every handler, and it is not `interpret`. -/
def IIgnores (_h : Handler OneSig St) : {A : Type} → Prog OneSig A → St A :=
  fun p => interpret hNop p

/-- **FALSIFIER for `interpret_pinned`'s operation-agreement
hypothesis.** -/
theorem pinned_needs_op_agreement :
    (∀ h : Handler OneSig St,
      IsMonadMorphism OneSig (fun {_A} (p : Prog OneSig _A) => IIgnores h p))
      ∧ IIgnores hInc (Prog.op ()) ≠ interpret hInc (Prog.op ()) := by
  refine ⟨fun _ => interpret_isMonadMorphism hNop, ?_⟩
  intro h
  have h0 : (((), 0) : Unit × Nat) = ((), 1) := congrFun h 0
  exact absurd (congrArg Prod.snd h0) (by decide)

/-- Drop the morphism law: the drifting interpreter, parameterised by
the handler it is given. -/
def IDrifts (h : Handler OneSig St) : {A : Type} → Prog OneSig A → St A :=
  fun p => phiDrifts hInc h p

/-- **FALSIFIER for `interpret_pinned`'s morphism hypothesis.**
`IDrifts` agrees with every handler on every single operation and still
is not `interpret`. -/
theorem pinned_needs_the_morphism_law :
    (∀ (h : Handler OneSig St) (op : OneSig.Op),
      IDrifts h (Prog.op op) = h.handle op)
      ∧ IDrifts hNop twoOps ≠ interpret hNop twoOps := by
  refine ⟨fun _ _ => rfl, re_bind_law_is_load_bearing.2⟩

/-! ### F3 — `through_assoc`'s `[LawfulMonad M]` is surplus too

Attempted break: find a target where associativity of `through` fails.
FAILED — and the failure is informative, because it fails over an
UNLAWFUL target: `Collapse` satisfies `through_assoc` while carrying no
`LawfulMonad` instance. Three of the castle's declarations
(`handler_eq_of_interpret_op_eq`, `through_id_left`, `through_assoc`)
therefore demand more than they spend. -/

theorem through_assoc_holds_over_collapse {S T U : Sig}
    (t : Handler S (Prog T)) (u : Handler T (Prog U))
    (h : Handler U Collapse) :
    (t.through u).through h = t.through (u.through h) :=
  Handler.ext fun op => by
    show interpret h (interpret u (t.handle op))
      = interpret (u.through h) (t.handle op)
    rw [collapse_interpret, collapse_interpret]

/-! ### F4 — the universal property's SUBJECT is a proper subclass of
`Prog`

`Handler S M` fixes `M : Type → Type v`, so `interpret` exists only at
`A : Type`. `Prog S A` is polymorphic in `A : Type u`. So there are
programs no handler can interpret — not "not yet", but not ever, at the
shipped `Handler`. The packet discloses "every statement is at
`A : Type`" under claim-scope; the sharper consequence, that R10's "a
semantics IS a handler" is false for such programs because they have NO
handler semantics at all, is not drawn. -/

/-- A program at `Type 1`. Nothing of the form `interpret h` accepts it,
for any handler over any `M : Type → Type v`. -/
def bigProg : Prog OneSig Type := .pure Nat

/-- The witness is the TYPE: `Prog OneSig Type` lives one universe up
from every `interpret`'s domain. -/
def bigProgShape : Prog OneSig Type := bigProg

/-! ## 8. This file's own axiom census

Printed here so the attack is held to the standard it applies. Nothing
below may name `sorryAx`, and nothing does. -/

#print axioms bare_monad_strengthening_is_real
#print axioms shift_admits_no_morphism
#print axioms one_type_can_be_enough
#print axioms l17_holds_where_the_castle_cannot_state_it
#print axioms prog_is_not_initial_among_monads
#print axioms prog_is_initial_in_S_models
#print axioms run_has_no_composition_law
#print axioms interpret_pinned_is_vacuous_over_collapse
#print axioms pinned_needs_op_agreement
#print axioms pinned_needs_the_morphism_law

end Cas.Lang.AttackPDD8
