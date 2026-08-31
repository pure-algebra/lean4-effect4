import Cas.Lang.Sig

/-!
# Effect Core v1 — scout probe for `EC1-T004` (`alphabet_lookup_total`)

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/scout-T004.lean
```

Scouting only. Nothing here is proposed for `library/` or for
`formal/effect-core-v1/EffectCore/Foundation/Alphabet.lean`, which is still an
empty stub. `Alphabet`/`OpDesc`/`lookup` do not exist anywhere in the estate
(`grep -rn Alphabet library/cas/Cas` is empty), so the carrier below is a
THROWAWAY scratch model whose only job is to decide the SHAPE of the row's
statement. It mints nothing: the op universe is metadata over an existing
`Cas.Lang.Sig`, per `CONTRACT-PACKET.md:87` ("`Alphabet` is metadata indexed by
an existing `Cas.Lang.Sig.Op` ... it does not replace or modify `Sig`").

The DAG's schematic signature is

    alphabet_lookup_total : op in a -> exists! d, lookup a op = some d

Four findings, each with a kernel behind it:

* §1 the `!` is free for ANY `Option`-valued function — uniqueness is
  `Option.some.inj`, so the row's whole content is existence;
* §2 if `op ∈ a` is defined THROUGH `lookup` (the natural definition once a
  lookup exists) the row is a tautology in the exact sense the DAG already used
  to delete `exists! v, evalPure e env = v` (`PROOF-DAG.md:207`);
* §3 the row HOLDS on a table with a duplicate op — the packet's own named
  negative case (`TYPE-CLOSURE.md:119`, "duplicate op") — so it does not
  exclude the failure it appears to guard. This is `EC1-CE030`'s duplicate-key
  lesson at the alphabet carrier;
* §4 the statement that does have content, with the premise §3 forces.

§5 records the `T004`/`T004S` signature clash separately.
-/

namespace EffectCoreScoutT004

open Cas.Lang

/-! ## §0 — the scratch carrier

Three ops, two answer codes, a keyed metadata table. Deliberately minimal:
every finding below is about the SHAPE of the statement, so a richer `OpDesc`
would only add noise. -/

/-- Scratch operation identities. -/
inductive OpId where
  | get | put | ask
  deriving DecidableEq, Repr

/-- Scratch answer codes — stand-in for the packet's `ValueTy` (`EC1-D0`). -/
inductive AnsCode where
  | nat | str
  deriving DecidableEq, Repr

/-- The answer code's meaning. -/
def AnsCode.interp : AnsCode → Type
  | .nat => Nat
  | .str => String

/-- Scratch `OpDesc`: the per-operation metadata row. -/
structure OpDesc where
  op : OpId
  answerTy : AnsCode
  deriving DecidableEq, Repr

/-- Scratch `Alphabet`: a keyed metadata table over operations. -/
structure Alphabet where
  table : List OpDesc

/-- The lookup the DAG's signature presumes: association-list search,
`Option`-valued. -/
def Alphabet.lookup (a : Alphabet) (op : OpId) : Option OpDesc :=
  a.table.find? (fun d => decide (d.op = op))

/-- Membership read off the declaration table — the INDEPENDENT reading of
`op in a`. This is the reading under which the row has content. -/
def Alphabet.Declares (a : Alphabet) (op : OpId) (d : OpDesc) : Prop :=
  d ∈ a.table ∧ d.op = op

/-- Membership defined THROUGH the lookup — the COLLAPSING reading of
`op in a`, and the one a reader reaches for first once `lookup` exists. -/
def Alphabet.MemViaLookup (a : Alphabet) (op : OpId) : Prop :=
  (a.lookup op).isSome = true

/-! ## §1 — the `!` is free

For any `Option`-valued function whatsoever, existence upgrades to unique
existence. No fact about alphabets, tables, or signatures participates.

First, a carrier finding. `ExistsUnique` DOES NOT EXIST in this environment:
`library/cas` pins `leanprover/lean4:v4.33.1` with an empty `.lake/packages`
(no Mathlib, no dependency at all), `∃!` has no notation there, and
`grep -rn 'ExistsUnique\|∃!' library/cas/Cas` is empty — the estate has never
used the connective. Every DAG row spelled with `exists!` — `EC1-T004`,
`EC1-T008`, `EC1-T016` — owes either this definition or an explicit spelling
before it can be stated at all. -/

/-- The DAG's `exists! d, o = some d`, spelled out. -/
def UniqueSome {δ : Type} (o : Option δ) : Prop :=
  ∃ d, o = some d ∧ ∀ e, o = some e → e = d

/-- **Finding 1.** `exists! d, f x = some d` carries no more information than
`exists d, f x = some d`, for every `f` and every `x`. Uniqueness is
`Option.some.inj` and nothing else. -/
theorem bang_is_free {α δ : Type} (f : α → Option δ) (x : α)
    (h : ∃ d, f x = some d) : UniqueSome (f x) := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d, hd, fun d' hd' => Option.some.inj (hd'.symm.trans hd)⟩

/-- The same fact stated as the row's own shape, still with no alphabet
hypothesis: the whole content of `EC1-T004` is `(lookup a op).isSome`. -/
theorem T004_content_is_isSome {α δ : Type} (f : α → Option δ) (x : α)
    (h : (f x).isSome = true) : UniqueSome (f x) :=
  bang_is_free f x (Option.isSome_iff_exists.mp h)

/-! ## §2 — the tautology, if membership is read through the lookup

`PROOF-DAG.md:207` already deleted `exists! v, evalPure e env = v` and the
same-input function-equality forms as "tautologies for any Lean function".
`EC1-T004` survives that deletion ONLY because `some` can be `none`. If
`op in a` is spelled `MemViaLookup`, the escape closes and the row joins the
deleted forms. -/

/-- **Finding 2.** Under the collapsing reading of `op in a`, `EC1-T004` is an
instance of §1 with no alphabet content at all. -/
theorem T004_collapses_when_membership_is_lookup
    (a : Alphabet) (op : OpId) (h : a.MemViaLookup op) :
    UniqueSome (a.lookup op) :=
  T004_content_is_isSome (a.lookup) op h

/-! ## §3 — the row holds on the packet's own forbidden table

`TYPE-CLOSURE.md:119` lists the red controls for `Alphabet`/`OpDesc`:
"unknown op, **duplicate op**, many-shot admission, missing direct
primitive/foreign handler". A reader would expect `alphabet_lookup_total` to be
the theorem that kills "duplicate op". It does not. -/

/-- A table declaring `get` twice, with two DIFFERENT answer codes. -/
def dupGet : Alphabet := ⟨[⟨.get, .nat⟩, ⟨.get, .str⟩]⟩

/-- The table really is the forbidden one: two distinct descriptors are
declared for the same operation. -/
theorem dupGet_declares_two_descriptors :
    dupGet.Declares .get ⟨.get, .nat⟩
      ∧ dupGet.Declares .get ⟨.get, .str⟩
      ∧ (⟨.get, .nat⟩ : OpDesc) ≠ ⟨.get, .str⟩ := by
  refine ⟨⟨by simp [dupGet], rfl⟩, ⟨by simp [dupGet], rfl⟩, by decide⟩

/-- The search silently keeps the first row and discards the second. -/
theorem dupGet_lookup_picks_the_first :
    dupGet.lookup .get = some ⟨.get, .nat⟩ := by
  decide

/-- **Finding 3.** `EC1-T004` as written is TRUE of the duplicate table. The
row therefore does not exclude its own named negative case: a checker relying
on it would admit an alphabet that declares one operation twice with
conflicting answer types. This is `EC1-CE030` (`COUNTEREXAMPLES.md:94`) at the
alphabet carrier — the `∃!` is on the FUNCTION, which is single-valued by
construction, not on the DECLARATION, which is not. -/
theorem T004_holds_on_the_duplicate_table :
    UniqueSome (dupGet.lookup .get) := by
  refine ⟨⟨.get, .nat⟩, dupGet_lookup_picks_the_first, ?_⟩
  intro d hd
  exact Option.some.inj (hd.symm.trans dupGet_lookup_picks_the_first)

/-! ## §4 — the statement that has content

Two repairs are forced together:

* quantify over the DECLARATION relation, not over the function's result; and
* carry the duplicate-free premise, exactly as `EC1-T002` carries one
  (`PROOF-DAG.md:210`) for the same reason.

The result is an agreement theorem between the table and the search — the real
obligation hiding behind "total". -/

/-- The well-formedness the packet's own red control owes. -/
abbrev Alphabet.NodupOps (a : Alphabet) : Prop := (a.table.map (·.op)).Nodup

/-- Distinct entries cannot share a key when the keys are duplicate-free. -/
theorem nodup_key_unique {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α},
      x ∈ l → y ∈ l → f x = f y → x = y := by
  intro l
  induction l with
  | nil => intro _ x y hx _ _; simp at hx
  | cons a t ih =>
    intro hnd x y hx hy h
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnot, hnd'⟩ := hnd
    rcases List.mem_cons.mp hx with rfl | hx'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact absurd (List.mem_map.mpr ⟨y, hy', h.symm⟩) hnot
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd (List.mem_map.mpr ⟨x, hx', h⟩) hnot
      · exact ih hnd' hx' hy' h

/-- **The uniqueness that is not free.** Under `NodupOps`, an operation has at
most one declared descriptor. `dupGet` shows the premise is necessary. -/
theorem alphabet_declares_unique (a : Alphabet) (hnd : a.NodupOps)
    {op : OpId} {d d' : OpDesc}
    (h : a.Declares op d) (h' : a.Declares op d') : d = d' :=
  nodup_key_unique (·.op) hnd h.1 h'.1 (h.2.trans h'.2.symm)

/-- **The existence that is not free.** A declared operation is found. -/
theorem alphabet_lookup_isSome (a : Alphabet) {op : OpId} {d : OpDesc}
    (h : a.Declares op d) : (a.lookup op).isSome = true := by
  rcases hl : a.lookup op with _ | e
  · exact absurd (decide_eq_true h.2) (List.find?_eq_none.mp hl d h.1)
  · rfl

/-- **`EC1-T004`, restated so it has content.** The search AGREES with the
declaration table. This implies both halves of the schematic row, and unlike
that row it is FALSE on `dupGet` — which is the point. -/
theorem alphabet_lookup_agrees (a : Alphabet) (hnd : a.NodupOps)
    {op : OpId} {d : OpDesc} (h : a.Declares op d) : a.lookup op = some d := by
  rcases hl : a.lookup op with _ | e
  · exact absurd (decide_eq_true h.2) (List.find?_eq_none.mp hl d h.1)
  · have hl' : a.table.find? (fun x : OpDesc => decide (x.op = op)) = some e := hl
    have hmem : e ∈ a.table := List.mem_of_find?_eq_some hl'
    have hraw := List.find?_some hl'
    have hkey : e.op = op := of_decide_eq_true hraw
    rw [alphabet_declares_unique a hnd ⟨hmem, hkey⟩ h]

/-- The schematic row is a CONSEQUENCE of the restated one, so nothing is lost
by replacing it. -/
theorem restatement_implies_the_schematic_row
    (a : Alphabet) (hnd : a.NodupOps) {op : OpId} {d : OpDesc}
    (h : a.Declares op d) : UniqueSome (a.lookup op) :=
  T004_content_is_isSome (a.lookup) op
    (by rw [alphabet_lookup_agrees a hnd h]; rfl)

/-- The forbidden table is exactly the one the premise excludes. -/
theorem dupGet_is_not_nodup : ¬ dupGet.NodupOps := by decide

/-- **The premise is load-bearing.** Without `NodupOps` the restated theorem is
FALSE: `dupGet` declares `⟨get, str⟩`, and the search answers `⟨get, nat⟩`.
This is the `EC1-CE030` repair (`COUNTEREXAMPLES.md:94` — "add a duplicate-free
premise or make row validity supply it") transplanted to the alphabet carrier.
Contrast §3: the SCHEMATIC row is true on this same table, which is the whole
argument for replacing it. -/
theorem nodup_premise_is_necessary :
    ¬ ∀ (a : Alphabet) (op : OpId) (d : OpDesc),
        a.Declares op d → a.lookup op = some d := by
  intro h
  have hbad := h dupGet .get ⟨.get, .str⟩ ⟨by simp [dupGet], rfl⟩
  rw [dupGet_lookup_picks_the_first] at hbad
  exact absurd (Option.some.inj hbad) (by decide)

/-! ## §5 — the `T004`/`T004S` signature clash

`EC1-T004S` (`PROOF-DAG.md:194`) reads

    alphabet_answer_bridge : (op : a.toSig.Op) -> Value (lookup a op).answerTy
                               ≃ a.toSig.Ans op

`(lookup a op).answerTy` projects a FIELD. That does not elaborate against
`T004`'s `lookup a op : Option OpDesc`. The two rows disagree about `lookup`'s
codomain, and `EC1-D011` (`PROOF-DAG.md:88`) disagrees with both — it declares
`OpDesc : (a : Alphabet) -> a.toSig.Op -> Type`, a dependent type family, under
which descriptors are not looked up at all.

The estate's own carrier settles the direction. `Cas.Lang.Sig` makes answer
indexing total BY TYPING: `Ans : Op → Type`, no `Option` (`Sig.lean:13`). So the
op universe must be refined FIRST, definitionally, and then `Ans` is total for
free. Below, `toSig` does the refinement and the answer assignment is `rfl`. -/

/-- Elaborating the alphabet to an existing `Sig`: the operations are the FOUND
ops, carrying their own found-ness. Nothing about `Sig` is modified. -/
def Alphabet.toSig (a : Alphabet) : Sig where
  Op := { op : OpId // (a.lookup op).isSome = true }
  Ans := fun op => AnsCode.interp ((a.lookup op.1).get op.2).answerTy

/-- **Finding 4.** Once the op universe is the refinement, the answer
assignment is definitional — there is no residual totality theorem to prove,
and `T004S`'s field projection elaborates because `Option.get` has already
consumed the `isSome`. `EC1-T004`'s real job is to CONSTRUCT this subtype, not
to state a `Prop`. -/
theorem toSig_answer_is_definitional (a : Alphabet) (op : a.toSig.Op) :
    a.toSig.Ans op = AnsCode.interp ((a.lookup op.1).get op.2).answerTy :=
  rfl

/-- The refinement is inhabited exactly by the declared ops, so the bridge
costs nothing beyond §4. -/
def Alphabet.opOfDeclares (a : Alphabet) {op : OpId} {d : OpDesc}
    (h : a.Declares op d) : a.toSig.Op :=
  ⟨op, alphabet_lookup_isSome a h⟩

end EffectCoreScoutT004

/-! ## Kernel receipts -/

#print axioms EffectCoreScoutT004.bang_is_free
#print axioms EffectCoreScoutT004.T004_content_is_isSome
#print axioms EffectCoreScoutT004.T004_collapses_when_membership_is_lookup
#print axioms EffectCoreScoutT004.dupGet_declares_two_descriptors
#print axioms EffectCoreScoutT004.dupGet_lookup_picks_the_first
#print axioms EffectCoreScoutT004.T004_holds_on_the_duplicate_table
#print axioms EffectCoreScoutT004.nodup_key_unique
#print axioms EffectCoreScoutT004.alphabet_declares_unique
#print axioms EffectCoreScoutT004.alphabet_lookup_isSome
#print axioms EffectCoreScoutT004.alphabet_lookup_agrees
#print axioms EffectCoreScoutT004.restatement_implies_the_schematic_row
#print axioms EffectCoreScoutT004.dupGet_is_not_nodup
#print axioms EffectCoreScoutT004.nodup_premise_is_necessary
#print axioms EffectCoreScoutT004.toSig_answer_is_definitional
