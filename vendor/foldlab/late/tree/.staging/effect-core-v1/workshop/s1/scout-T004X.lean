import Cas.Backend.SumAlgebra

/-!
# Effect Core v1 — scout probe for `EC1-T004X` (`alphabet_sum_preserves_arms`)

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/scout-T004X.lean
```

Stage: `lean-formalization-strategy`, **Pass A** — no contract exists for this
row. `Alphabet`, `OpDesc`, `extend` and `toSig` do not exist anywhere in the
estate (`grep -rn 'Alphabet' library/cas/Cas` is empty), and
`formal/effect-core-v1/EffectCore/Foundation/Alphabet.lean` is an 11-line stub.
Freeze condition 14 (`Alphabet` indexed by `Sig.Op`) is recorded **UNRULED** in
`.staging/agent-reports/2026-08-31-effect-core-s17-rulings.md`. So the carriers
below are THROWAWAY scratch models, deliberately continuing `scout-T004.lean`'s
shape so the two scouts agree; nothing here is proposed for `library/` or for
`formal/`. It mints no signature, no program carrier, and no CAS spelling.

The DAG row (`PROOF-DAG.md:195`) is

    alphabet_sum_preserves_arms : (extend a b).toSig = a.toSig ⊕ₛ b.toSig
      "with left/right metadata and handler projections"

and `PROOF-DAG.md` §16 routes it as *"pending condition 14 ... preserve `Sig.sum`
with left/right laws"*.

## The fork this file establishes

`Alphabet.toSig` can be built in exactly two ways, and the row's equation is
degenerate in both:

* **§2 — stored-signature reading.** If the alphabet CARRIES its `Sig` and
  `extend` sets that field to `a.sig ⊕ₛ b.sig`, the equation is `rfl`. The
  estate already ships this reading twice: `StoreSig = CasSig ⊕ₛ RootSig` and
  `WordedSig = StoreSig ⊕ₛ WordSig` are both `rfl` (§2.1). The row then joins
  the two forms `PROOF-DAG.md:207` already deleted as tautologies.
* **§4 — derived-signature reading.** If `toSig.Op` is the subtype of operation
  ids the table actually declares (`scout-T004.lean` §5's `Alphabet.toSig`,
  forced there by `Sig.Ans`'s totality), the equation is **FALSE** as soon as
  the two arms name a common operation: the left side is a subsingleton and the
  right side has two elements, and unequal-cardinality types are unequal
  (`T004X_false_on_overlapping_arms`).

§3 shows the equation cannot state the clause the row's prose calls
"left/right metadata" — a `Sig` has two fields and neither is metadata.

§5–§7 give the statements that DO carry content: arm-wise descriptor
agreement (with the disjointness premise proved necessary, §5), the
answer-type arm law and why it is provable at all (§6), and the handler /
program projections, which are the estate's theorems **verbatim** (§7).

§8 records the cost of the fork: without the equation, a
`Handler (a.extend b).toSig M` is not a `Handler (a.toSig ⊕ₛ b.toSig) M`, so
none of `Handler.sum_handle_inl`, `Handler.sum_unique`, `interpret_inl` or
`Prog.inl_unique` apply to an extended alphabet. That transport is the row's
whole purpose, and it must be bought by CONSTRUCTION, not by a proof. §8 also
shows what remains once it is: on a TOTAL alphabet over a tagged operation
universe the equation is a one-line `funext` (`extend_toSig`, not even `rfl`),
both metadata arm laws are `rfl`, and the only surviving obligation is the one
the equation cannot state — the arms' stable operation identifiers must not
collide (`extend_idOf_injective`, `id_collision_survives_the_sum`).

25 receipts at the foot. Ceiling `propext` / `Quot.sound`; ten are axiom-free;
no `sorryAx`, no `Classical.choice`, no `native_decide`, no `#eval`.
-/

namespace EffectCoreScoutT004X

open Cas.Lang

/-! ## §1 — a type-inequality tool

Lean has no univalence, so equivalent types are not equal; but unequal
CARDINALITY does give a kernel-checkable inequality, and that is all §4 needs.
No `Classical.choice`, no `Function.Bijective` (which does not exist here —
`library/cas` pins `leanprover/lean4:v4.33.1` with an empty `.lake/packages`). -/

/-- A subsingleton type is not a type with two distinct elements. -/
theorem type_ne_of_subsingleton_of_two {α β : Type}
    (hα : ∀ x y : α, x = y) {u v : β} (huv : u ≠ v) : α ≠ β := by
  intro h
  subst h
  exact huv (hα u v)

/-! ## §2 — the stored-signature reading: the row is `rfl`

### §2.1 the estate has already shipped this reading, twice -/

/-- `Cas/Lang/Roots.lean:42`. The store extension's "sum preserves arms"
equation is definitional — there is nothing to prove. -/
theorem storeSig_extension_is_definitional : StoreSig = CasSig ⊕ₛ RootSig := rfl

/-- `Cas/Lang/Worded.lean:77`. The word extension, likewise. -/
theorem wordedSig_extension_is_definitional : WordedSig = StoreSig ⊕ₛ WordSig := rfl

/-- `Cas/Lang/Ops.lean:46`. And the LLM extension. Three shipped signature
extensions, three `rfl`s. -/
theorem agentSig_extension_is_definitional : AgentSig = CasSig ⊕ₛ LlmSig := rfl

/-! ### §2.2 the same, for an arbitrary versioned carrier that STORES its `Sig` -/

/-- A minimal stand-in for a versioned alphabet that carries its signature as a
field, rather than deriving it from a table. -/
structure SigCarrier where
  version : Nat
  sig : Sig

/-- The only `extend` such a carrier can have. -/
def SigCarrier.extend (a b : SigCarrier) : SigCarrier :=
  ⟨a.version + b.version, a.sig ⊕ₛ b.sig⟩

/-- **Finding 1.** Under the stored-signature reading `EC1-T004X` is `rfl` for
every alphabet, every version and every signature. It is the third instance of
the pattern `PROOF-DAG.md:207` deletes: *"tautologies for any Lean function"*. -/
theorem T004X_is_rfl_when_the_signature_is_stored (a b : SigCarrier) :
    (a.extend b).sig = a.sig ⊕ₛ b.sig := rfl

/-! ## §3 — the equation cannot mention metadata

`Sig` has exactly two fields, `Op` and `Ans` (`Cas/Lang/Sig.lean:13`). The
alphabet's `opId`, `errorRow`, `requirementRow`, `handlerRoute`, `resumption`,
`cancellation`, `observation` and `capabilityClass` (`ALGEBRA.md` §2.2) are all
absent from it. So the row's prose clause "with left/right metadata" is not
something the stated equation can express, in either reading. -/

/-- **Finding 2.** Two carriers that differ in metadata satisfy the same
`toSig` equation. Whatever `EC1-T004X` proves, it proves nothing about the
descriptor table. -/
theorem sig_equation_is_metadata_blind :
    (SigCarrier.mk 1 CasSig) ≠ (SigCarrier.mk 2 CasSig)
      ∧ (SigCarrier.mk 1 CasSig).sig = (SigCarrier.mk 2 CasSig).sig := by
  refine ⟨fun h => ?_, rfl⟩
  exact absurd (congrArg SigCarrier.version h) (by decide)

/-! ## §4 — the derived-signature reading: the row is FALSE

`scout-T004.lean` §5 established the shape `toSig` must have once descriptors
are looked up rather than indexed: the operation universe is the SUBTYPE of ids
the table declares, because `Sig.Ans : Op → Type` is total by typing and
`lookup` is `Option`-valued. That file's carrier is reproduced here with one
added metadata column (`route`) so §3's point is visible at the table too. -/

/-- Scratch operation identities. -/
inductive OpId where
  | get | put | ask
  deriving DecidableEq, Repr

/-- Scratch answer codes — stand-in for the packet's `ValueTy` (`EC1-D001`). -/
inductive AnsCode where
  | nat | str
  deriving DecidableEq, Repr

/-- The answer code's meaning. First-order code, decoded by a function: this is
what makes §6 provable. -/
def AnsCode.interp : AnsCode → Type
  | .nat => Nat
  | .str => String

/-- Scratch handler routing — a metadata column that `toSig` discards. -/
inductive Route where
  | builtin | service
  deriving DecidableEq, Repr

/-- Scratch `OpDesc`. -/
structure OpDesc where
  op : OpId
  answerTy : AnsCode
  route : Route
  deriving DecidableEq, Repr

/-- Scratch `Alphabet`: a keyed metadata table over operations. -/
structure Alphabet where
  table : List OpDesc

/-- Association-list search, `Option`-valued — `scout-T004.lean`'s `lookup`. -/
def Alphabet.lookup (a : Alphabet) (op : OpId) : Option OpDesc :=
  a.table.find? (fun d => decide (d.op = op))

/-- `scout-T004.lean` §5's `toSig`: the operations are the FOUND ops, carrying
their own found-ness. Nothing about `Sig` is modified. -/
def Alphabet.toSig (a : Alphabet) : Sig where
  Op := { op : OpId // (a.lookup op).isSome = true }
  Ans := fun op => AnsCode.interp ((a.lookup op.1).get op.2).answerTy

/-- The only composition a closed first-order table admits: concatenation.
`ALGEBRA.md` §2.2 gives the alphabet no composition operation at all, so this
is the operation `EC1-T004X` proposes to add. -/
def Alphabet.extend (a b : Alphabet) : Alphabet := ⟨a.table ++ b.table⟩

/-- Two extension packs that both declare `get`, differing only in routing.
Nothing in the packet forbids this: `ALGEBRA.md` §2.2's arms are authored
independently, and `Sig.sum` tags by POSITION, not by identifier. -/
def aGet : Alphabet := ⟨[⟨.get, .nat, .builtin⟩]⟩

/-- The right arm, same operation, different route. -/
def bGet : Alphabet := ⟨[⟨.get, .nat, .service⟩]⟩

/-- Every operation of the extended alphabet is `get`. -/
theorem extend_op_is_get (x : (aGet.extend bGet).toSig.Op) : x.1 = OpId.get := by
  obtain ⟨u, hu⟩ := x
  cases u
  · rfl
  · exact absurd hu (by decide)
  · exact absurd hu (by decide)

/-- So the extended alphabet's operation universe is a subsingleton. -/
theorem extend_op_subsingleton (x y : (aGet.extend bGet).toSig.Op) : x = y :=
  Subtype.ext ((extend_op_is_get x).trans (extend_op_is_get y).symm)

/-- The left arm's `get`. -/
def lGet : aGet.toSig.Op := ⟨.get, by decide⟩

/-- The right arm's `get`. -/
def rGet : bGet.toSig.Op := ⟨.get, by decide⟩

/-- The summed signature's operation universe has two distinct elements: the
sum keeps both arms' `get`, tagged. -/
theorem sum_op_has_two :
    (Sum.inl lGet : aGet.toSig.Op ⊕ bGet.toSig.Op) ≠ Sum.inr rGet := by
  simp

/-- **Finding 3 — `EC1-T004X` is FALSE under the derived-signature reading.**
Concatenation collapses the shared operation; the signature sum does not. The
two signatures are therefore unequal, at the smallest possible witness: one
operation each. -/
theorem T004X_false_on_overlapping_arms :
    (aGet.extend bGet).toSig ≠ aGet.toSig ⊕ₛ bGet.toSig := by
  intro h
  exact type_ne_of_subsingleton_of_two
    extend_op_subsingleton sum_op_has_two (congrArg Sig.Op h)

/-! ## §5 — the descriptor arm laws, and the premise they need

These are the statements the row's "left/right metadata" clause is reaching
for. The left arm is unconditional; the right arm is FALSE without a
disjointness premise — the alphabet-level replay of `EC1-CE030`
(`COUNTEREXAMPLES.md:94`, "add a duplicate-free premise or make row validity
supply it"), exactly as `scout-T004.lean` §4 found for `EC1-T004`. -/

/-- **Left arm.** A descriptor declared by the left alphabet survives
extension, with no premise. -/
theorem extend_lookup_left (a b : Alphabet) {op : OpId} {d : OpDesc}
    (h : a.lookup op = some d) : (a.extend b).lookup op = some d := by
  show (a.table ++ b.table).find? (fun x : OpDesc => decide (x.op = op)) = some d
  rw [List.find?_append]
  show (a.lookup op).or _ = some d
  rw [h]
  rfl

/-- **Right arm**, with the premise. -/
theorem extend_lookup_right (a b : Alphabet) {op : OpId} {d : OpDesc}
    (hna : a.lookup op = none) (h : b.lookup op = some d) :
    (a.extend b).lookup op = some d := by
  show (a.table ++ b.table).find? (fun x : OpDesc => decide (x.op = op)) = some d
  rw [List.find?_append]
  show (a.lookup op).or (b.lookup op) = some d
  rw [hna, h]
  rfl

/-- **Finding 4 — the right arm's premise is load-bearing.** `bGet` declares
`get` as a `service` operation; the extended alphabet answers `builtin`. A
generated handler table built from the right arm's metadata would route the
operation to the wrong side. -/
theorem right_arm_needs_disjointness :
    ¬ ∀ (a b : Alphabet) (op : OpId) (d : OpDesc),
        b.lookup op = some d → (a.extend b).lookup op = some d := by
  intro h
  have hbad := h aGet bGet .get ⟨.get, .nat, .service⟩ (by decide)
  exact absurd hbad (by decide)

/-! ## §6 — the answer-type arm law, and why it is provable

A per-operation equality of ANSWER TYPES is provable where the `Sig` equality
is not — but only because `Ans` factors through a first-order code universe
(`AnsCode.interp`), so type equality is `congrArg` on codes. If `OpDesc`
carried an opaque `Type` instead of a `ValueTy` code, this would fail too.
That is `EFFECTS-BACKEND` R14a paying for itself at the alphabet. -/

/-- Equal options have equal contents, whatever found-ness proofs are used. -/
theorem optionGet_congr {α : Type} {o o' : Option α} (h : o = o')
    {h1 : o.isSome = true} {h2 : o'.isSome = true} : o.get h1 = o'.get h2 := by
  subst h; rfl

/-- Strengthening of `extend_lookup_left`: on a declared operation the extended
table's search agrees with the left arm's, as an equation between `Option`s. -/
theorem extend_lookup_left_eq (a b : Alphabet) {op : OpId}
    (h : (a.lookup op).isSome = true) : (a.extend b).lookup op = a.lookup op := by
  rcases hl : a.lookup op with _ | d
  · rw [hl] at h; exact absurd h (by simp)
  · exact extend_lookup_left a b hl

/-- The left injection at the operation level — the reindexing that replaces
the row's signature equation. -/
def extendInl (a b : Alphabet) (op : a.toSig.Op) : (a.extend b).toSig.Op :=
  ⟨op.1, by rw [extend_lookup_left_eq a b op.2]; exact op.2⟩

/-- **Finding 5.** The left arm's answer types agree, as a genuine equality of
types, obtained by `congrArg` through the answer-code universe. -/
theorem extendInl_ans (a b : Alphabet) (op : a.toSig.Op) :
    (a.extend b).toSig.Ans (extendInl a b op) = a.toSig.Ans op :=
  congrArg (fun d : OpDesc => AnsCode.interp d.answerTy)
    (optionGet_congr (extend_lookup_left_eq a b op.2))

/-! ## §7 — the handler and program projections are INHERITED, verbatim

Nothing in the row's third clause is owed. Every projection law it names is a
shipped estate theorem applied at the alphabet-derived signatures with no new
proof, and the estate keeps the adversaries that make each one non-vacuous:
`swapSum_not_sum_handle_inl` (`Cas/Backend/SumAlgebra.lean:685`),
`doubleInl_not_interpret_inl` (`:790`),
`badAgentSum_not_interpret_inr` (`:753`),
`narrowing_to_Id_fails` (`:966`). -/

/-- `Cas/Backend/SumAlgebra.lean:196`, at two alphabets. Proof term: the estate
theorem, unmodified. -/
theorem alphabet_handler_projects_left {M : Type → Type v} (a b : Alphabet)
    (h : Handler a.toSig M) (g : Handler b.toSig M) (op : a.toSig.Op) :
    (h.sum g).handle (Sum.inl op) = h.handle op :=
  Handler.sum_handle_inl h g op

/-- `Cas/Backend/SumAlgebra.lean:202`, likewise. -/
theorem alphabet_handler_projects_right {M : Type → Type v} (a b : Alphabet)
    (h : Handler a.toSig M) (g : Handler b.toSig M) (op : b.toSig.Op) :
    (h.sum g).handle (Sum.inr op) = g.handle op :=
  Handler.sum_handle_inr h g op

/-- `Cas/Backend/SumAlgebra.lean:231`. The program-level left projection. -/
theorem alphabet_interpret_left {M : Type → Type v} [Monad M] {A : Type}
    (a b : Alphabet) (h : Handler a.toSig M) (g : Handler b.toSig M)
    (p : Prog a.toSig A) : interpret (h.sum g) p.inl = interpret h p :=
  interpret_inl h g p

/-- `Cas/Backend/SumAlgebra.lean:239`. The mirror. -/
theorem alphabet_interpret_right {M : Type → Type v} [Monad M] {A : Type}
    (a b : Alphabet) (h : Handler a.toSig M) (g : Handler b.toSig M)
    (q : Prog b.toSig A) : interpret (h.sum g) q.inr = interpret g q :=
  interpret_inr h g q

/-- `Cas/Backend/SumAlgebra.lean:212`. Categoricity transports too: the summed
handler is the ONLY one agreeing with both arms. -/
theorem alphabet_handler_sum_unique {M : Type → Type v} (a b : Alphabet)
    (h : Handler a.toSig M) (g : Handler b.toSig M)
    (k : Handler (a.toSig ⊕ₛ b.toSig) M)
    (hl : ∀ op, k.handle (Sum.inl op) = h.handle op)
    (hr : ∀ op, k.handle (Sum.inr op) = g.handle op) : k = h.sum g :=
  Handler.sum_unique h g k hl hr

/-! ## §8 — what the fork costs

Every theorem in §7 is stated at `a.toSig ⊕ₛ b.toSig`. An extended alphabet's
handler has type `Handler (a.extend b).toSig M`, and §4 proves those two
signatures are not equal in the derived reading, so no §7 theorem applies to it
and no coercion exists. Transporting the estate's sum laws onto `extend` is
therefore not a theorem anyone can prove — it is a CONSTRAINT on how `extend`
is defined.

The scratch below shows the constraint discharged the way the estate already
discharges it for `StoreSig`, `WordedSig` and `AgentSig`: the extended
alphabet's operation universe IS the tagged sum. The descriptor arm laws then
collapse to `rfl`, the signature equation costs one `funext` (Finding 6a — not
even `rfl`, because `Sig.sum`'s `Sum.elim` does not commute definitionally with
the alphabet's answer decoder), and the whole of `EC1-T004X`'s remaining
content moves to the identifier obligation
that the `Sig` equation is blind to (§3): the arms' STABLE OPERATION IDS must
stay distinct, or `R4`'s presentation identity and the generated handler table
both break on a collision that `Sig.sum` cannot see. -/

/-- A total alphabet over a tagged operation universe: every operation of `I`
has a descriptor, so no `Option` and no subtype appear. This is the estate's
`DeclarationId.all_complete` shape (`Cas/Schema/Declarations.lean:202`, the
anchor `EC1-T004` already stands on) rather than an association list. -/
structure TotalAlphabet (I : Type) where
  ansOf : I → AnsCode
  idOf : I → String
  routeOf : I → Route

/-- Its signature. -/
def TotalAlphabet.toSig {I : Type} (a : TotalAlphabet I) : Sig where
  Op := I
  Ans := fun op => AnsCode.interp (a.ansOf op)

/-- Extension as the tagged sum — the definition `ALGEBRA.md` §2.2's
"extension is `Sig.sum`/`⊕ₛ`, with metadata reindexed over the left and right
injections" actually describes. -/
def TotalAlphabet.extend {I J : Type} (a : TotalAlphabet I) (b : TotalAlphabet J) :
    TotalAlphabet (I ⊕ J) where
  ansOf := Sum.elim a.ansOf b.ansOf
  idOf := Sum.elim a.idOf b.idOf
  routeOf := Sum.elim a.routeOf b.routeOf

/-- **Finding 6a.** Even in the total reading the equation is NOT `rfl`. The
operation universes coincide definitionally, but `Sig.sum`'s
`Ans := Sum.elim S.Ans T.Ans` does not commute definitionally with the
alphabet's `Ans := AnsCode.interp ∘ ansOf`: the proof is `funext` over the two
arms, one `rfl` per arm. So the row's residue in its best reading is a
functional-extensionality bookkeeping step costing `Quot.sound`. -/
theorem extend_toSig {I J : Type} (a : TotalAlphabet I) (b : TotalAlphabet J) :
    (a.extend b).toSig = a.toSig ⊕ₛ b.toSig := by
  have h : (fun op : I ⊕ J => AnsCode.interp ((a.extend b).ansOf op))
      = Sum.elim (fun op : I => AnsCode.interp (a.ansOf op))
          (fun op : J => AnsCode.interp (b.ansOf op)) := by
    funext op; cases op <;> rfl
  exact congrArg (Sig.mk (I ⊕ J)) h

/-- **Finding 6b.** With `extend` defined as the sum, BOTH metadata arm laws
are `rfl`. The left-metadata and right-metadata clauses of `EC1-T004X` carry no
information whatsoever, and the signature clause carries only `extend_toSig`. -/
theorem T004X_metadata_clauses_are_all_rfl
    {I J : Type} (a : TotalAlphabet I) (b : TotalAlphabet J) :
    ((a.extend b).toSig = a.toSig ⊕ₛ b.toSig)
      ∧ (∀ op : I, (a.extend b).ansOf (Sum.inl op) = a.ansOf op)
      ∧ (∀ op : J, (a.extend b).ansOf (Sum.inr op) = b.ansOf op)
      ∧ (∀ op : I, (a.extend b).routeOf (Sum.inl op) = a.routeOf op)
      ∧ (∀ op : J, (a.extend b).routeOf (Sum.inr op) = b.routeOf op) :=
  ⟨extend_toSig a b, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The obligation that survives, and that the `Sig` equation cannot state:
the two arms must not collide on a stable operation identifier. -/
def TotalAlphabet.IdsDisjoint {I J : Type} (a : TotalAlphabet I)
    (b : TotalAlphabet J) : Prop :=
  ∀ (i : I) (j : J), a.idOf i ≠ b.idOf j

/-- The extended identifier map is injective on the arms exactly when the arms
are id-disjoint and each arm is itself injective. This is the content
`EC1-T004X` should carry. -/
theorem extend_idOf_injective {I J : Type} (a : TotalAlphabet I)
    (b : TotalAlphabet J) (ha : Function.Injective a.idOf)
    (hb : Function.Injective b.idOf) (hd : a.IdsDisjoint b) :
    Function.Injective (a.extend b).idOf := by
  rintro (x | x) (y | y) h
  · exact congrArg Sum.inl (ha h)
  · exact absurd h (hd x y)
  · exact absurd h.symm (hd y x)
  · exact congrArg Sum.inr (hb h)

/-- A left arm and a right arm that both publish the identifier `"get"`. -/
def uGet : TotalAlphabet Unit := ⟨fun _ => .nat, fun _ => "get", fun _ => .builtin⟩

/-- The mirror, routed differently. -/
def vGet : TotalAlphabet Unit := ⟨fun _ => .nat, fun _ => "get", fun _ => .service⟩

/-- **Finding 7 — the surviving obligation is not vacuous.** Two arms may
publish the same stable identifier, the sum admits them, and the extended
identifier map is not injective. `Sig.sum` tags by position and cannot see
this; §3 proves the row's equation cannot state it. -/
theorem id_collision_survives_the_sum :
    ¬ uGet.IdsDisjoint vGet ∧ ¬ Function.Injective (uGet.extend vGet).idOf := by
  refine ⟨fun h => h () () rfl, fun h => ?_⟩
  have hcol : (uGet.extend vGet).idOf (Sum.inl ())
      = (uGet.extend vGet).idOf (Sum.inr ()) := rfl
  have hbad := h hcol
  simp at hbad

end EffectCoreScoutT004X

/-! ## Kernel receipts -/

#print axioms EffectCoreScoutT004X.type_ne_of_subsingleton_of_two
#print axioms EffectCoreScoutT004X.storeSig_extension_is_definitional
#print axioms EffectCoreScoutT004X.wordedSig_extension_is_definitional
#print axioms EffectCoreScoutT004X.agentSig_extension_is_definitional
#print axioms EffectCoreScoutT004X.T004X_is_rfl_when_the_signature_is_stored
#print axioms EffectCoreScoutT004X.sig_equation_is_metadata_blind
#print axioms EffectCoreScoutT004X.extend_op_is_get
#print axioms EffectCoreScoutT004X.extend_op_subsingleton
#print axioms EffectCoreScoutT004X.sum_op_has_two
#print axioms EffectCoreScoutT004X.T004X_false_on_overlapping_arms
#print axioms EffectCoreScoutT004X.extend_lookup_left
#print axioms EffectCoreScoutT004X.extend_lookup_right
#print axioms EffectCoreScoutT004X.right_arm_needs_disjointness
#print axioms EffectCoreScoutT004X.optionGet_congr
#print axioms EffectCoreScoutT004X.extend_lookup_left_eq
#print axioms EffectCoreScoutT004X.extendInl_ans
#print axioms EffectCoreScoutT004X.alphabet_handler_projects_left
#print axioms EffectCoreScoutT004X.alphabet_handler_projects_right
#print axioms EffectCoreScoutT004X.alphabet_interpret_left
#print axioms EffectCoreScoutT004X.alphabet_interpret_right
#print axioms EffectCoreScoutT004X.alphabet_handler_sum_unique
#print axioms EffectCoreScoutT004X.extend_toSig
#print axioms EffectCoreScoutT004X.T004X_metadata_clauses_are_all_rfl
#print axioms EffectCoreScoutT004X.extend_idOf_injective
#print axioms EffectCoreScoutT004X.id_collision_survives_the_sum
