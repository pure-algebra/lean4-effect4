import Cas.Lang.Defun

/-!
# Breaker witnesses against `workshop/s1/T003.lean` (`EC1-T003`)

Adversarial file. Nothing here is offered as support for row `EC1-T003`; every
declaration exists to REFUTE a claim made by `T003.lean` or by its report, or to
prove the nearest true statement where a claim overshoots its theorem.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/attack-T003.lean
```

Nothing under `library/`, `formal/`, or any packet `.md` is touched.

## Attack map

| § | Target claim | Result |
|---|--------------|--------|
| A | "THE PREMISE REFUTATION that forces the deletion of `EnvWF env`"; "a unary environment premise can neither totalise the evaluator nor inhabit the backward half of the iff." | REFUTED AS STATED. `no_unary_env_premise_totalises` shows non-totality only. Non-totality does not obstruct the iff (§A1), and an unsatisfiable `EnvWF` satisfies T003's own theorem while making the DAG row hold for EVERY evaluator against EVERY relation (§A2/§A3). The deletion is forced by the carrier change in T003 §3, not by §2. |
| B | `atom_meaning_is_unconstrained` "exhibits two atom tables with IDENTICAL signatures … under which the SAME program denotes 6 and 0." | NOT WHAT THE THEOREM SAYS. `PE` is indexed by the whole `AtomTable`, meanings included, so `sumFold` and `mulFold` are different terms at different types. §B proves the intended statement at a signature-indexed carrier: ONE program, two interpretations. |
| C | "`section Relation` contains ZERO occurrences of `evalPE`/`evalArgs`", offered as the independence gate. | TRUE BUT NARROWER THAN ADVERTISED. Independence is structural only. `Den` quotes `scalarEq`/`scalarLe` verbatim, so the row is blind to a WRONG scalar primitive exactly as it is blind to a wrong atom body — a fact T003 §8 proves for atoms and never states for scalars. §C proves it. |
| D | `EC1-F20` (a "pure" atom reads a mutable counter). | EXERCISED. Adequacy holds at every counter value while the same program answers differently at different values, so the row cannot refute F20. |

§B-§D share one small carrier. It is NOT a rival model of `EC1-A08`: it drops
`ArgMap`, collections, products and sums, because none of them bears on the four
claims above. The `EC1-A10` companion `T003.lean` adds is not under attack — it
is the part of that file this review finds most clearly owed.
-/

namespace AttackT003

/-! ## §A — the premise-deletion argument proves less than it is used for

`T003.lean:163-176` states `no_unary_env_premise_totalises` and glosses it:
"A unary environment premise therefore cannot make a pure evaluator total and
cannot inhabit the backward half of the iff."

The first conjunct is what the theorem proves. The second does not follow from
it, and is false. Three witnesses. -/

section UnaryPremise

open Cas (Addr32)
open Cas.Lang

/-- The relational reading of an operand that `T003.lean:169` uses, restated so
this file is self-contained. -/
inductive PInDen (env : List Addr32) : PIn → Addr32 → Prop where
  | lit (a : Addr32) : PInDen env (.lit a) a
  | ans {i : Nat} {a : Addr32} (h : env[i]? = some a) : PInDen env (.ans i) a

/-- **§A1 — the backward half IS inhabited under every unary predicate.**
`PIn.resolve` is exactly the evaluator that `no_unary_env_premise_totalises`
proves non-total, and two-sided adequacy over it holds under an ARBITRARY
`EnvWF`, `True` included. Danglingness obstructs the bare `= v` spelling and
nothing else; it does not obstruct the row.

This is `T003.lean`'s own `pin_eval_adequate` with the premise the DAG asks for
put back on, to show that putting it back costs nothing — so the gloss's second
conjunct is false. -/
theorem premised_row_is_inhabited_under_every_unary_predicate
    (EnvWF : List Addr32 → Prop) (env : List Addr32) (_hwf : EnvWF env)
    (i : PIn) (a : Addr32) :
    PIn.resolve env i = some a ↔ PInDen env i a := by
  cases i with
  | lit b =>
    constructor
    · intro h
      have hb : b = a := by simpa [PIn.resolve] using h
      subst hb
      exact .lit b
    · intro h
      cases h
      rfl
  | ans j =>
    constructor
    · intro h
      exact .ans (by simpa [PIn.resolve] using h)
    · intro h
      cases h with
      | ans hj => simpa [PIn.resolve] using hj

/-- **§A2 — the vacuity hazard in the DAG's premise slot, unmeasured by T003.**
An unsatisfiable `EnvWF` discharges the DAG row for EVERY evaluator against
EVERY relation. The row as `PROOF-DAG.md:191` writes it therefore has a premise
slot that can be filled to make it say nothing. `T003.lean` §2 attacks the
premise for being on the wrong ARGUMENT and never tests it for satisfiability,
which is the failure the packet has hit five times elsewhere. -/
theorem unsatisfiable_premise_rescues_any_evaluator
    {E X V : Type} (EnvWF : E → Prop) (hempty : ∀ e, ¬ EnvWF e)
    (f : X → E → V) (R : E → X → V → Prop) :
    ∀ env : E, EnvWF env → ∀ (x : X) (v : V), f x env = v ↔ R env x v :=
  fun env h => absurd h (hempty env)

/-- **§A3 — and that predicate satisfies T003's theorem simultaneously.** So
`no_unary_env_premise_totalises` is CONSISTENT with a unary premise carrying the
row. A statement that holds equally in the world where the premise works cannot
force the premise's deletion: what forces it is the intrinsic carrier of
`T003.lean` §3, where no predicate on `Env Γ` has anything left to exclude. -/
theorem dangling_theorem_is_consistent_with_a_rescuing_premise :
    (∀ env : List Addr32, (fun _ : List Addr32 => False) env →
        ∃ i : PIn, PIn.resolve env i = none)
      ∧ (∀ (f : PIn → List Addr32 → Option Addr32)
            (R : List Addr32 → PIn → Option Addr32 → Prop)
            (env : List Addr32), (fun _ : List Addr32 => False) env →
              ∀ (i : PIn) (v : Option Addr32), f i env = v ↔ R env i v) := by
  refine ⟨fun env h => h.elim, fun f R env h => h.elim⟩

end UnaryPremise

/-! ## §B-§D — a signature-indexed carrier

`T003.lean:307` declares `inductive PE (Θ : AtomTable) : Ctx → VTy → Type`,
where `AtomTable` (`:300-302`) carries BOTH `sig : Nat → AtomSig` and
`meaning : (n : Nat) → Env (sig n).args → Val (sig n).ret`. No constructor of
`PE` mentions `Θ.meaning`; only `Θ.sig` is used. Yet the syntax TYPE is indexed
by the meaning, with two consequences the file does not record.

1. `PE addTable Γ τ` and `PE mulTable Γ τ` are different types with no
   transport between them. `sumFold` and `mulFold` are therefore written out
   twice (`T003.lean:717/728`) and `atom_meaning_is_unconstrained` compares two
   DIFFERENT terms. "The same program denotes 6 and 0" is not a Lean statement
   anywhere in that file.
2. `T003.lean:281-283` calls the syntax first-order because "every `PE` node
   holds finite data and `Nat` ids". That is true of the constructor PAYLOADS
   and false of the TYPE: `PE Θ` is a family indexed by a structure containing a
   function. `EC1-T005 serialized_fields_first_order` scopes to serialized raw
   fields and `R14a` P1 to definitions outside `Prog`, so neither is broken —
   the file's own defence (`:280-283`, "`Θ` is a semantic environment, not
   serialized content") holds. What does not hold is consequence 1: the price of
   the over-indexing is paid by §8, and it is avoidable.

Both are removable. Below, the syntax is indexed by the atom signature table
only, and the interpretation — atom bodies AND the scalar primitive — is a
separate argument to the evaluator and to the relation. Adequacy still holds,
and §8's intended statement becomes provable about one program. -/

section Interpretation

inductive TY where
  | bool | nat
  deriving DecidableEq

def V : TY → Type
  | .bool => Bool
  | .nat  => Nat

abbrev Cx := List TY

inductive Vr : Cx → TY → Type where
  | z {Γ : Cx} {τ : TY} : Vr (τ :: Γ) τ
  | s {Γ : Cx} {σ τ : TY} : Vr Γ τ → Vr (σ :: Γ) τ

inductive Rho : Cx → Type where
  | nil : Rho []
  | cons {Γ : Cx} {τ : TY} : V τ → Rho Γ → Rho (τ :: Γ)

def Rho.get : {Γ : Cx} → {τ : TY} → Rho Γ → Vr Γ τ → V τ
  | _, _, .cons v _, .z => v
  | _, _, .cons _ ρ, .s x => Rho.get ρ x

/-- The syntax. `S n` is atom `n`'s result type; every atom is binary on `nat`,
which is all four claims need. The index is the SIGNATURE table alone. -/
inductive EX (S : Nat → TY) : Cx → TY → Type where
  | litN {Γ : Cx} (n : Nat) : EX S Γ .nat
  | litB {Γ : Cx} (b : Bool) : EX S Γ .bool
  | var  {Γ : Cx} {τ : TY} : Vr Γ τ → EX S Γ τ
  | eqn  {Γ : Cx} : EX S Γ .nat → EX S Γ .nat → EX S Γ .bool
  | atom {Γ : Cx} (n : Nat) : EX S Γ .nat → EX S Γ .nat → EX S Γ (S n)

/-- The interpretation: `EC1-A09` clause 2 atom bodies AND the scalar primitive
that `T003.lean` fixes globally as `scalarEq`. Making it an argument is what
exposes what the adequacy row can and cannot see. -/
structure Interp (S : Nat → TY) where
  meaning : (n : Nat) → Nat → Nat → V (S n)
  eqPrim  : Nat → Nat → Bool

def ev (S : Nat → TY) (I : Interp S) :
    {Γ : Cx} → {τ : TY} → Rho Γ → EX S Γ τ → V τ
  | _, _, _, .litN n => n
  | _, _, _, .litB b => b
  | _, _, ρ, .var x => ρ.get x
  | _, _, ρ, .eqn p q => I.eqPrim (ev S I ρ p) (ev S I ρ q)
  | _, _, ρ, .atom n p q => I.meaning n (ev S I ρ p) (ev S I ρ q)

/-- The relation, by cases on the syntax, with no occurrence of `ev` — the
independence discipline of `T003.lean` §5, reproduced faithfully, including the
part §C is about: the primitive and the atom body appear as the DENOTATIONS of
their operations. -/
inductive Dn (S : Nat → TY) (I : Interp S) :
    {Γ : Cx} → {τ : TY} → Rho Γ → EX S Γ τ → V τ → Prop where
  | litN {Γ : Cx} (ρ : Rho Γ) (n : Nat) : Dn S I ρ (.litN n) n
  | litB {Γ : Cx} (ρ : Rho Γ) (b : Bool) : Dn S I ρ (.litB b) b
  | var {Γ : Cx} {τ : TY} (ρ : Rho Γ) (x : Vr Γ τ) : Dn S I ρ (.var x) (ρ.get x)
  | eqn {Γ : Cx} {ρ : Rho Γ} {p q : EX S Γ .nat} {u v : Nat} :
      Dn S I ρ p u → Dn S I ρ q v → Dn S I ρ (.eqn p q) (I.eqPrim u v)
  | atom {Γ : Cx} {ρ : Rho Γ} {n : Nat} {p q : EX S Γ .nat} {u v : Nat} :
      Dn S I ρ p u → Dn S I ρ q v → Dn S I ρ (.atom n p q) (I.meaning n u v)

theorem ev_sound (S : Nat → TY) (I : Interp S) :
    {Γ : Cx} → {τ : TY} → (ρ : Rho Γ) → (e : EX S Γ τ) → Dn S I ρ e (ev S I ρ e)
  | _, _, ρ, .litN n => by simp only [ev]; exact .litN ρ n
  | _, _, ρ, .litB b => by simp only [ev]; exact .litB ρ b
  | _, _, ρ, .var x => by simp only [ev]; exact .var ρ x
  | _, _, ρ, .eqn p q => by
      simp only [ev]; exact .eqn (ev_sound S I ρ p) (ev_sound S I ρ q)
  | _, _, ρ, .atom n p q => by
      simp only [ev]; exact .atom (ev_sound S I ρ p) (ev_sound S I ρ q)

theorem ev_complete (S : Nat → TY) (I : Interp S) :
    {Γ : Cx} → {τ : TY} → {ρ : Rho Γ} → {e : EX S Γ τ} → {v : V τ} →
    Dn S I ρ e v → ev S I ρ e = v
  | _, _, _, _, _, .litN _ _ => by simp only [ev] <;> rfl
  | _, _, _, _, _, .litB _ _ => by simp only [ev] <;> rfl
  | _, _, _, _, _, .var _ _ => by simp only [ev] <;> rfl
  | _, _, _, _, _, .eqn hp hq => by
      simp only [ev, ev_complete S I hp, ev_complete S I hq] <;> rfl
  | _, _, _, _, _, .atom hp hq => by
      simp only [ev, ev_complete S I hp, ev_complete S I hq] <;> rfl

/-- Adequacy at the repaired carrier, for EVERY interpretation. The quantifier
placement is the point: `I` is universally quantified OUTSIDE the row, which is
what makes the next three theorems statable at all. -/
theorem adequate_at_every_interpretation (S : Nat → TY) (I : Interp S)
    {Γ : Cx} {τ : TY} (ρ : Rho Γ) (e : EX S Γ τ) (v : V τ) :
    ev S I ρ e = v ↔ Dn S I ρ e v :=
  ⟨fun h => h ▸ ev_sound S I ρ e, ev_complete S I⟩

end Interpretation

section Witnesses

/-- One signature table, shared by every interpretation below, so "identical
signatures" is a Lean fact rather than a reading of two source texts. -/
def binS : Nat → TY := fun _ => .nat

def addI : Interp binS := ⟨fun _ => Nat.add, Nat.beq⟩
def mulI : Interp binS := ⟨fun _ => Nat.mul, Nat.beq⟩

/-- A deliberately WRONG scalar primitive: everything equals everything. The
atom bodies are the honest ones. -/
def sloppyI : Interp binS := ⟨fun _ => Nat.add, fun _ _ => true⟩

/-- `EC1-F20`: an atom body that reads an ambient counter. `ALGEBRA.md` §3
clause 4 forbids exactly this. -/
def counterI (c : Nat) : Interp binS :=
  ⟨fun _ x y => Nat.add c (Nat.add x y), Nat.beq⟩

/-- `V` is an ordinary `def`, so a `V .nat` has no `OfNat`. These three move
host literals in and answers out at default transparency; they are notation,
not content. -/
def nv (n : Nat) : V .nat := n
def bv (b : Bool) : V .bool := b
def out (v : V .nat) : Nat := v

/-- ONE program — one term, usable under every interpretation. That is exactly
what indexing the syntax on the meaning prevents. -/
def prog : EX binS [] .nat := EX.atom 0 (.litN 3) (.litN 4)

def eqProg : EX binS [] .bool := EX.eqn (.litN 1) (.litN 2)

/-! The closed evaluations are obtained FROM the row, the way `T003.lean`'s
`caseProj_denotes` is: build the derivation by constructors — which never
mentions `ev` — and take the backward half. (`ev` here happens to be compiled by
well-founded recursion rather than `brecOn`, so it does not reduce under `rfl`;
nothing below needs it to. The reviewed file's `evalPE` DOES compile
structurally — `#print EC1T003.evalPE` reports `PE.brecOn` — and that claim of
its report is confirmed.) -/

theorem prog_add : ev binS addI Rho.nil prog = nv 7 :=
  (adequate_at_every_interpretation binS addI Rho.nil prog (nv 7)).mpr
    (Dn.atom (Dn.litN Rho.nil 3) (Dn.litN Rho.nil 4))

theorem prog_mul : ev binS mulI Rho.nil prog = nv 12 :=
  (adequate_at_every_interpretation binS mulI Rho.nil prog (nv 12)).mpr
    (Dn.atom (Dn.litN Rho.nil 3) (Dn.litN Rho.nil 4))

theorem eq_honest : ev binS addI Rho.nil eqProg = bv false :=
  (adequate_at_every_interpretation binS addI Rho.nil eqProg (bv false)).mpr
    (Dn.eqn (Dn.litN Rho.nil 1) (Dn.litN Rho.nil 2))

theorem eq_sloppy : ev binS sloppyI Rho.nil eqProg = bv true :=
  (adequate_at_every_interpretation binS sloppyI Rho.nil eqProg (bv true)).mpr
    (Dn.eqn (Dn.litN Rho.nil 1) (Dn.litN Rho.nil 2))

theorem prog_c0 : ev binS (counterI 0) Rho.nil prog = nv 7 :=
  (adequate_at_every_interpretation binS (counterI 0) Rho.nil prog (nv 7)).mpr
    (Dn.atom (Dn.litN Rho.nil 3) (Dn.litN Rho.nil 4))

theorem prog_c1 : ev binS (counterI 1) Rho.nil prog = nv 8 :=
  (adequate_at_every_interpretation binS (counterI 1) Rho.nil prog (nv 8)).mpr
    (Dn.atom (Dn.litN Rho.nil 3) (Dn.litN Rho.nil 4))

/-- **§B — the statement `atom_meaning_is_unconstrained` was reaching for.**
Two interpretations over the SAME signature table, each satisfying full
two-sided adequacy, under which THE SAME program answers 7 and 12.

`T003.lean:825-838` proves the analogue with `sumFold : PE addTable [] .nat` and
`mulFold : PE mulTable [] .nat` — two distinct terms at two distinct types. The
conclusion §8 draws is sound; its theorem does not carry it, and the gap is
caused entirely by indexing the syntax on the meaning. -/
theorem same_program_two_atom_meanings :
    (∀ {Γ : Cx} {τ : TY} (ρ : Rho Γ) (e : EX binS Γ τ) (v : V τ),
        ev binS addI ρ e = v ↔ Dn binS addI ρ e v)
      ∧ (∀ {Γ : Cx} {τ : TY} (ρ : Rho Γ) (e : EX binS Γ τ) (v : V τ),
          ev binS mulI ρ e = v ↔ Dn binS mulI ρ e v)
      ∧ ev binS addI Rho.nil prog = nv 7
      ∧ ev binS mulI Rho.nil prog = nv 12 :=
  ⟨fun ρ e v => adequate_at_every_interpretation binS addI ρ e v,
   fun ρ e v => adequate_at_every_interpretation binS mulI ρ e v,
   prog_add, prog_mul⟩

/-- **§C — the row is blind to the SCALAR primitive, not only to atom bodies.**
`T003.lean` §5 justifies `Den`'s independence with "no constructor mentions
`evalPE`", then records that `scalarEq`/`scalarLe` "appear because they are the
DENOTATIONS of their operations". That is precisely the atom situation and it
has precisely the atom consequence: an equality primitive answering `true` on
`1 = 2` still passes two-sided adequacy, because the relation quotes it.

`T003.lean` proves this opacity for `Θ.meaning` (§8) and never states it for
`scalarEq`/`scalarLe`. No theorem in that file constrains `boolEq`, `boolLe`,
`scalarEq` or `scalarLe` in any way. It is the same hole, one clause wider. -/
theorem the_row_is_blind_to_the_scalar_primitive :
    (∀ {Γ : Cx} {τ : TY} (ρ : Rho Γ) (e : EX binS Γ τ) (v : V τ),
        ev binS addI ρ e = v ↔ Dn binS addI ρ e v)
      ∧ (∀ {Γ : Cx} {τ : TY} (ρ : Rho Γ) (e : EX binS Γ τ) (v : V τ),
          ev binS sloppyI ρ e = v ↔ Dn binS sloppyI ρ e v)
      ∧ ev binS addI Rho.nil eqProg = bv false
      ∧ ev binS sloppyI Rho.nil eqProg = bv true :=
  ⟨fun ρ e v => adequate_at_every_interpretation binS addI ρ e v,
   fun ρ e v => adequate_at_every_interpretation binS sloppyI ρ e v,
   eq_honest, eq_sloppy⟩

/-- **§D — `EC1-F20` exercised.** A `PureAtom` body that reads a mutable counter
satisfies `EC1-T003` at every value of the counter, while the same program
answers differently at different values. The row cannot refute F20; only
`ALGEBRA.md` §3 clauses 3-5, which have no instrument, can.

The falsifier is SURVIVED in the sense that adequacy stays true, and FAILED in
the sense that adequacy cannot detect the violation. `T003.lean` §8 reaches this
conclusion for one fixed pair of tables; this is the parametric form. -/
theorem F20_pure_atom_reading_a_counter_is_invisible :
    (∀ (c : Nat) {Γ : Cx} {τ : TY} (ρ : Rho Γ) (e : EX binS Γ τ) (v : V τ),
        ev binS (counterI c) ρ e = v ↔ Dn binS (counterI c) ρ e v)
      ∧ out (ev binS (counterI 0) Rho.nil prog)
          ≠ out (ev binS (counterI 1) Rho.nil prog) := by
  refine ⟨?_, ?_⟩
  · intro c _ _ ρ e v
    exact adequate_at_every_interpretation binS (counterI c) ρ e v
  · rw [prog_c0, prog_c1]
    decide

end Witnesses

/-! ## Receipts -/

#print axioms premised_row_is_inhabited_under_every_unary_predicate
#print axioms unsatisfiable_premise_rescues_any_evaluator
#print axioms dangling_theorem_is_consistent_with_a_rescuing_premise
#print axioms ev_sound
#print axioms ev_complete
#print axioms adequate_at_every_interpretation
#print axioms prog_add
#print axioms prog_mul
#print axioms eq_honest
#print axioms eq_sloppy
#print axioms prog_c0
#print axioms prog_c1
#print axioms same_program_two_atom_meanings
#print axioms the_row_is_blind_to_the_scalar_primitive
#print axioms F20_pure_atom_reading_a_counter_is_invisible

/-! ## Falsifiers NOT exercisable at this row's carrier, and why

- `EC1-F01` (delete a target block), `EC1-F02` (swap an answer type in
  `Resume`), `EC1-F08` (unregistered host callback in raw content), `EC1-F59`
  (omit a deep public module from the recursive census), `EC1-F60` (drop or
  duplicate a row's seven-way disposition), `EC1-F80` (mark cutover with an open
  edge), `EC1-F87` (`Sig` reification): none touches
  `PureExpr`/`PureDenotes`. There is no block, no `Resume`, no raw content, no
  census row, no disposition, no cutover edge and no `Sig` anywhere in
  `T003.lean`'s carrier.
- `EC1-F03` (duplicate an operation ID): UNEXPRESSIBLE in the reviewed model.
  `AtomTable.sig : Nat → AtomSig` (`T003.lean:301`) is a FUNCTION, so one id
  cannot carry two signatures and the hazard cannot be posed. The reviewed file
  discloses this and routes it to `EC1-T004`.
- `EC1-F82` (permute a duplicate-key raw row): UNEXPRESSIBLE. Records are
  iterated products (`VTy.prod`) with no keys, disclosed as omission 3, so
  `EC1-CE030`'s obstruction cannot be posed against this carrier.
- `EC1-F86` (a second value meaning for an inhabited `Cas.Schema.El` code):
  `Val .unit = Unit`, `Val .bool = Bool` and `Val (.list a) = List (Val a)`
  duplicate the inhabited `El` arms at `Cas/Schema/El.lean:179` (`.null => Unit`),
  `:180` (`.bool => Bool`) and `:184` (`.arr a => List (El a)`), while
  `Val .nat = Nat` sits beside `El .int => SafeInt`. That is what
  `PROOF-DAG.md` §16's Values row names as the prohibited shortcut and what §17
  condition 13 gates. The reviewed file promotes nothing and discloses the gap,
  so the finding is about the claim ceiling, not a rule broken.
-/

end AttackT003
