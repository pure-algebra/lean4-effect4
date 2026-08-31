import Cas.Lang.Sig

/-!
# Effect Core v1 — `EC1-T004` (`alphabet_lookup_total`), implemented

Slice `EC1-S1`. Skill stage: `lean-model-invariants` (the row is about a
table's representation, its duplicate-free invariant, and the checked boundary
into an existing `Sig`; it is not about sequencing or protocol state).

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/T004.lean
```

## Outcome

The DAG's schematic row

    alphabet_lookup_total : op in a -> exists! d, lookup a op = some d

is **restated**, and the restatement is proved **strictly stronger** than both
the schematic row and the scout's recommendation. §7 proves the restatement
implies the schematic row, and §2/§4 exhibit tables satisfying the schematic row
that the restatement rejects — so the implication is strict in the direction
that matters.

Three defects force the restatement, each with a kernel behind it here:

* §1 the `!` is decoration. For ANY `Option`-valued `f`, `∃ d, f x = some d`
  upgrades to `∃! d, f x = some d` by `Option.some.inj` alone. The row's entire
  content is `(lookup a op).isSome`.
* §2 the row is TRUE of the packet's own forbidden table. `TYPE-CLOSURE.md:119`
  names "duplicate op" a red control for `Alphabet`/`OpDesc`; `dupGet` declares
  one operation twice with conflicting answer codes and satisfies the row. This
  is `EC1-CE030`'s duplicate-key lesson (`COUNTEREXAMPLES.md:94`, forced repair
  "add a duplicate-free premise or make row validity supply it") transplanted to
  the alphabet carrier, discharged with a fresh witness rather than cited.
* §3 the row is a tautology under the reading of `op in a` a reader reaches for
  once a lookup exists — the exact ground on which `PROOF-DAG.md:207` already
  deleted `exists! v, evalPure e env = v`.

## New this pass, beyond the scout

The scout recommended a one-sided agreement theorem (`Declares → lookup = some
d`, under `NodupOps`). That is proved here as `alphabet_lookup_complete`, but it
is **not adequate on its own**, and §4 proves it:

* `TYPE-CLOSURE.md:119` names TWO red controls, "unknown op" and "duplicate op".
  The `NodupOps` premise and the completeness direction together exclude only the
  second. §4 exhibits `fabricate`, a lookup that INVENTS a descriptor for every
  undeclared operation, satisfies the completeness direction for every
  duplicate-free alphabet, and satisfies the schematic row with no premise at
  all. The clause that excludes it is the **soundness** direction, which is
  premise-free and which neither the DAG row nor the scout's recommendation
  states.
* So the row that carries both red controls is the **iff**
  (`alphabet_lookup_iff`): the search DECIDES the declaration relation. This is
  the estate's own shape — `Cas/Schema/Declarations.lean:184
  DeclarationId.payloadWf_iff`, `Cas/Core/Admission.lean:60 checkRefs_ok_iff`.
* §6 pushes the consequence into the bridge. On `dupGet`, `toSig` does not merely
  survive: it assigns `get` the answer type `Nat` while the table declares that
  `get` answers a string (`dupGet_toSig_types_a_declared_op_wrongly`). The
  duplicate table produces a `Sig` whose answer typing CONTRADICTS a row of the
  very table it was elaborated from. `NodupOps` is what makes the answer
  assignment well-defined (`toSig_ans_of_declares`).

## Invariant record (`lean-model-invariants`)

* **Invariant.** `NodupOps a := (a.table.map (·.op)).Nodup` — subject:
  representation + boundary validation. Locality: a stable global fact about one
  alphabet value, fixed at construction. Decidable (`goodAlphabet_nodup` is
  `by decide`); the estate discharges the same fact on a closed table at
  elaboration time with a `#guard` (`Cas/Schema/Declarations.lean:207`), which
  §5 mirrors.
* **Mechanism: raw + `WF`, plus a subtype at the boundary.** `Alphabet` is plain
  data and `NodupOps` is extrinsic, because a duplicate-op table MUST be
  representable for the red control to have anything to reject — the same law
  `ALGEBRA.md` states for raw rows. The refinement into `Sig` is a subtype
  carrying `isSome` as a proof field, because `Cas.Lang.Sig` (`Sig.lean:13`)
  makes `Ans : Op → Type` total by typing and admits no `Option`.
* **Boundary.** `table (raw) → NodupOps (validate) → lookup/Declares agreement
  (checked) → toSig (meaning, into the EXISTING `Cas.Lang.Sig`)`.
* **Kept extrinsic deliberately.** Everything freeze conditions 3 and 14 own:
  the real operation universe, the real descriptor fields, and the protocol
  identity bridge. No mutator is modelled (`extend` is `EC1-T004X`'s row), so no
  preservation obligation is discharged here.

## What this file does NOT establish

The carrier below is a THROWAWAY shape probe. `Alphabet`, `OpDesc`,
`Alphabet.lookup` and `Alphabet.toSig` do not exist anywhere in the estate
(`grep -rn Alphabet library/cas/Cas` is empty) and
`formal/effect-core-v1/EffectCore/Foundation/Alphabet.lean` is an empty stub.
`PROOF-DAG.md` §17 freeze condition 3 (the closed alphabet/handler table) and
condition 14 (the neutral protocol operation identity and its admission bridge to
`Sig.Op`/`Sig.Ans`) are both **OPEN**. A green elaboration here proves the stated
propositions about this scratch model and NOTHING about the eventual carrier; in
particular it does not close `EC1-T004`.

Checks omitted, explicitly:

* `EC1-T004S`, `EC1-T004X` and `EC1-T004RW` were NOT opened. §6 shows only that
  the subtype refinement makes `T004S`'s field projection ELABORATE; it does not
  attempt `T004S`'s equivalence, and it says nothing about `Sig.sum`
  reindexing or the Root/Word agreement laws.
* `Alphabet.lookup` here is a `List.find?` association search. Nothing was
  checked about any other representation, and if freeze condition 3 rules the
  alphabet the estate's way (closed inductive op universe + total `desc` by
  pattern match + `#guard` Nodup, i.e. `Cas/Schema/Declarations.lean`), there is
  no `Option`, every theorem in §4 becomes `rfl` or disappears, and `EC1-T004`
  should be DELETED outright alongside the two forms already deleted at
  `PROOF-DAG.md:207` rather than proved. The obligation would then migrate into
  the carrier definitionally, as §6 already does for the answer assignment.
* No `lake build` was run, no `library/` or `formal/` byte was touched, and no
  packet `.md` was edited. `EC1-CE030` and `EC1-CE033` are cited from the
  register; §2/§4a are independent witnesses, not re-derivations of theirs.
* The three-operation, two-code carrier settles statement SHAPE only. It has no
  error row, no requirement row, no resumption/cancellation/observation field,
  and no capability class — the rest of `ALGEBRA.md` §2.2's `OpDesc`.

Nothing is minted. The op universe is metadata over the existing
`Cas.Lang.Sig` (`CONTRACT-PACKET.md:87`); `toSig` builds a value of that
signature and modifies nothing about it, which is §16's sanctioned route for the
Operation-families row (an explicit admission bridge) and not its prohibited
shortcut (pretending every protocol identity already has a `Sig.Op`). All work
is effect-free, first-order, and outside `Prog` — `EFFECTS-BACKEND.md` R14a P1.

`ExistsUnique` DOES NOT EXIST in this toolchain: `library/cas` pins
`leanprover/lean4:v4.33.1` with an empty `.lake/packages` (no Mathlib), `∃!` has
no notation, and `grep -rn 'ExistsUnique\|∃!' library/cas/Cas` is empty. §1
spells the connective out as `UniqueSome`. Every DAG row written with `exists!`
— `EC1-T004`, `EC1-T008`, `EC1-T016`, `EC1-T035` — owes this.

No `sorry`, no `axiom`, no `native_decide`, no `#eval` carrying a claim. Every
theorem reports `#print axioms` at the foot.
-/

namespace EffectCoreV1.T004

open Cas.Lang

/-! ## §0 — the scratch carrier

Minimal and first-order: three operations, two answer codes, a keyed metadata
table. Every finding is about the SHAPE of the statement, so a richer `OpDesc`
would add only noise. Duplicate-op tables are deliberately representable. -/

/-- Scratch operation identities. -/
inductive OpId where
  | get | put | ask
  deriving DecidableEq, Repr

/-- Scratch answer codes — stand-in for the packet's `ValueTy` (`EC1-D001`). -/
inductive AnsCode where
  | nat | str
  deriving DecidableEq, Repr

/-- The answer code's meaning. First-order codes, so answer types are compared
by comparing CODES; no type inequality is ever needed. -/
def AnsCode.interp : AnsCode → Type
  | .nat => Nat
  | .str => String

/-- Scratch `OpDesc`: the per-operation metadata row. -/
structure OpDesc where
  op : OpId
  answerTy : AnsCode
  deriving DecidableEq, Repr

/-- Scratch `Alphabet`: a keyed metadata table over operations. RAW — a
duplicate-op table is representable, which is what gives the red control
something to reject. -/
structure Alphabet where
  table : List OpDesc
  deriving DecidableEq, Repr

/-- The lookup the DAG's signature presumes: association-list search,
`Option`-valued. -/
def Alphabet.lookup (a : Alphabet) (op : OpId) : Option OpDesc :=
  a.table.find? (fun d => decide (d.op = op))

/-- Membership read off the DECLARATION TABLE — the reading under which the row
has content. -/
def Alphabet.Declares (a : Alphabet) (op : OpId) (d : OpDesc) : Prop :=
  d ∈ a.table ∧ d.op = op

/-- Membership read THROUGH the lookup — the collapsing reading. -/
def Alphabet.MemViaLookup (a : Alphabet) (op : OpId) : Prop :=
  (a.lookup op).isSome = true

/-- The well-formedness `TYPE-CLOSURE.md:119`'s "unique IDs" owes and which no
packet declaration currently supplies. -/
abbrev Alphabet.NodupOps (a : Alphabet) : Prop := (a.table.map (·.op)).Nodup

/-! ## §1 — the `!` is decoration

`ExistsUnique` is unavailable, so the connective is spelled out. -/

/-- The DAG's `exists! d, o = some d`, spelled out. -/
def UniqueSome {δ : Type} (o : Option δ) : Prop :=
  ∃ d, o = some d ∧ ∀ e, o = some e → e = d

/-- **Defect 1.** For every `f` and every `x`, existence upgrades to unique
existence. Uniqueness is `Option.some.inj` and nothing else; no fact about
alphabets, tables or signatures participates. -/
theorem bang_is_free {α δ : Type} (f : α → Option δ) (x : α)
    (h : ∃ d, f x = some d) : UniqueSome (f x) := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d, hd, fun d' hd' => Option.some.inj (hd'.symm.trans hd)⟩

/-- The same fact in the row's own shape: the entire content of `EC1-T004` is
`(lookup a op).isSome`. -/
theorem dag_row_content_is_isSome {α δ : Type} (f : α → Option δ) (x : α)
    (h : (f x).isSome = true) : UniqueSome (f x) :=
  bang_is_free f x (Option.isSome_iff_exists.mp h)

/-! ## §2 — the row is true of the packet's own forbidden table

`TYPE-CLOSURE.md:119` lists the red controls for `Alphabet`/`OpDesc`: "unknown
op, **duplicate op**, many-shot admission, missing direct primitive/foreign
handler". A reader would take `alphabet_lookup_total` to be the theorem that
kills "duplicate op". It does not. -/

/-- A table declaring `get` twice, with two DIFFERENT answer codes. -/
def dupGet : Alphabet := ⟨[⟨.get, .nat⟩, ⟨.get, .str⟩]⟩

/-- The table really is the forbidden one: two distinct descriptors are declared
for one operation. -/
theorem dupGet_declares_two_descriptors :
    dupGet.Declares .get ⟨.get, .nat⟩
      ∧ dupGet.Declares .get ⟨.get, .str⟩
      ∧ (⟨.get, .nat⟩ : OpDesc) ≠ ⟨.get, .str⟩ :=
  ⟨⟨by simp [dupGet], rfl⟩, ⟨by simp [dupGet], rfl⟩, by decide⟩

/-- The search silently keeps the first row and discards the second. -/
theorem dupGet_lookup_picks_the_first :
    dupGet.lookup .get = some ⟨.get, .nat⟩ := by
  decide

/-- **Defect 2.** `EC1-T004` as written is TRUE of the duplicate table. The row
does not exclude its own named negative case: a checker relying on it admits an
alphabet that declares one operation twice with conflicting answer types. The
`∃!` sits on the FUNCTION, which is single-valued by construction, not on the
DECLARATION, which is not. -/
theorem dag_row_holds_on_the_duplicate_table :
    UniqueSome (dupGet.lookup .get) :=
  dag_row_content_is_isSome dupGet.lookup .get
    (by rw [dupGet_lookup_picks_the_first]; rfl)

/-- The premise the restatement carries is exactly what this table fails. -/
theorem dupGet_is_not_nodup : ¬ dupGet.NodupOps := by decide

/-! ## §3 — the row is a tautology under the collapsing reading of `op in a`

`op in a` has no definition anywhere in the packet, and its spelling decides the
row. Spelled through the lookup, `EC1-T004` joins the family
`PROOF-DAG.md:207` already deleted twice. -/

/-- **Defect 3.** Under `MemViaLookup` the row is an instance of §1 with zero
alphabet content: the surface, the table and the operation are all discarded. -/
theorem dag_row_collapses_under_lookup_membership
    (a : Alphabet) (op : OpId) (h : a.MemViaLookup op) :
    UniqueSome (a.lookup op) :=
  dag_row_content_is_isSome a.lookup op h

/-! ## §4 — the restatement, and why BOTH directions are required

`TYPE-CLOSURE.md:119` names two red controls. This section proves they are
carried by the two directions of an iff, and that neither direction implies the
other. -/

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

/-- **The uniqueness that is not free.** Under `NodupOps` an operation has at
most one declared descriptor. `dupGet` shows the premise necessary. -/
theorem alphabet_declares_unique (a : Alphabet) (hnd : a.NodupOps)
    {op : OpId} {d d' : OpDesc}
    (h : a.Declares op d) (h' : a.Declares op d') : d = d' :=
  nodup_key_unique (·.op) hnd h.1 h'.1 (h.2.trans h'.2.symm)

/-- **SOUNDNESS — the "unknown op" clause, and it needs NO premise.** Whatever
the search answers really is declared, by this table, for this operation. This
direction is stated neither by the DAG row nor by the scout's recommendation,
and §4's fabricator shows it is exactly what they are missing. -/
theorem alphabet_lookup_sound (a : Alphabet) {op : OpId} {d : OpDesc}
    (h : a.lookup op = some d) : a.Declares op d := by
  have h' : a.table.find? (fun x : OpDesc => decide (x.op = op)) = some d := h
  have hraw := List.find?_some h'
  have hkey : d.op = op := of_decide_eq_true hraw
  exact ⟨List.mem_of_find?_eq_some h', hkey⟩

/-- **COMPLETENESS — the "duplicate op" clause, and it needs `NodupOps`.**
Everything declared is found, and found AS DECLARED. -/
theorem alphabet_lookup_complete (a : Alphabet) (hnd : a.NodupOps)
    {op : OpId} {d : OpDesc} (h : a.Declares op d) : a.lookup op = some d := by
  rcases hl : a.lookup op with _ | e
  · have hl' : a.table.find? (fun x : OpDesc => decide (x.op = op)) = none := hl
    exact absurd (decide_eq_true h.2) (List.find?_eq_none.mp hl' d h.1)
  · have hl' : a.table.find? (fun x : OpDesc => decide (x.op = op)) = some e := hl
    have hraw := List.find?_some hl'
    have hkey : e.op = op := of_decide_eq_true hraw
    have hd : a.Declares op e := ⟨List.mem_of_find?_eq_some hl', hkey⟩
    rw [alphabet_declares_unique a hnd hd h]

/-- **`EC1-T004`, restated.** The search DECIDES the declaration relation. This
is the estate's own shape (`Cas/Schema/Declarations.lean:184 payloadWf_iff`,
`Cas/Core/Admission.lean:60 checkRefs_ok_iff`) and it carries both red controls
at once: `mpr` excludes a dropped or shadowed declaration, `mp` excludes a
fabricated one.

The premise is ASYMMETRIC and the statement does not show it: `mp` is
`alphabet_lookup_sound`, which takes no premise at all; only `mpr` consumes
`hnd`. The estate carries a comparable asymmetry at the keyed-row carrier —
`Cas/Backend/Canon.lean:313 canonServices_perm` takes only the LEFT `Nodup` and
derives the right from the permutation — so an under-consumed duplicate-free
premise is a known shape here, not an error. -/
theorem alphabet_lookup_iff (a : Alphabet) (hnd : a.NodupOps)
    (op : OpId) (d : OpDesc) : a.lookup op = some d ↔ a.Declares op d :=
  ⟨alphabet_lookup_sound a, alphabet_lookup_complete a hnd⟩

/-- **The honest reading of "total".** Search succeeds exactly on the declared
operations. Premise-free in both directions — `NodupOps` buys uniqueness of the
ANSWER, not existence. -/
theorem alphabet_lookup_isSome_iff (a : Alphabet) (op : OpId) :
    (a.lookup op).isSome = true ↔ ∃ d, a.Declares op d := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
    exact ⟨d, alphabet_lookup_sound a hd⟩
  · rintro ⟨d, hd⟩
    rcases hl : a.lookup op with _ | e
    · have hl' : a.table.find? (fun x : OpDesc => decide (x.op = op)) = none := hl
      exact absurd (decide_eq_true hd.2) (List.find?_eq_none.mp hl' d hd.1)
    · rfl

/-! ### §4a — the `NodupOps` premise is load-bearing

`EC1-CE030`'s forced repair, discharged rather than cited. Contrast §2: the
SCHEMATIC row is true on this same table. -/

/-- Without `NodupOps` the completeness direction is FALSE: `dupGet` declares
`⟨get, str⟩` and the search answers `⟨get, nat⟩`. -/
theorem nodup_premise_is_necessary :
    ¬ ∀ (a : Alphabet) (op : OpId) (d : OpDesc),
        a.Declares op d → a.lookup op = some d := by
  intro h
  have hbad := h dupGet .get ⟨.get, .str⟩ ⟨by simp [dupGet], rfl⟩
  rw [dupGet_lookup_picks_the_first] at hbad
  exact absurd (Option.some.inj hbad) (by decide)

/-! ### §4b — completeness ALONE is not adequate

The scout's recommended row is the completeness direction. This subsection
proves it insufficient: a lookup that INVENTS descriptors for undeclared
operations satisfies it for every duplicate-free alphabet, and satisfies the
schematic row with no premise at all. `TYPE-CLOSURE.md:119`'s FIRST red control,
"unknown op", is carried by soundness and by nothing else. -/

/-- The adversary: answers the table where it can, and fabricates elsewhere. -/
def fabricate (a : Alphabet) (op : OpId) : Option OpDesc :=
  match a.lookup op with
  | some d => some d
  | none => some ⟨op, .nat⟩

/-- The empty alphabet — declares nothing at all. -/
def emptyAlphabet : Alphabet := ⟨[]⟩

/-- The adversary satisfies the SCHEMATIC row for every alphabet and every
operation, with no premise whatsoever. -/
theorem dag_row_holds_of_the_fabricator (a : Alphabet) (op : OpId) :
    UniqueSome (fabricate a op) := by
  refine dag_row_content_is_isSome (fabricate a) op ?_
  show (fabricate a op).isSome = true
  unfold fabricate
  cases a.lookup op <;> rfl

/-- The adversary satisfies the COMPLETENESS direction for every duplicate-free
alphabet. So the scout's recommended row does not exclude it either. -/
theorem fabricate_satisfies_completeness (a : Alphabet) (hnd : a.NodupOps)
    {op : OpId} {d : OpDesc} (h : a.Declares op d) : fabricate a op = some d := by
  unfold fabricate
  rw [alphabet_lookup_complete a hnd h]

/-- But the adversary is UNSOUND: it answers for an operation the empty alphabet
does not declare. This is the "unknown op" red control, live. -/
theorem fabricate_is_unsound :
    fabricate emptyAlphabet .get = some ⟨.get, .nat⟩
      ∧ ¬ emptyAlphabet.Declares .get ⟨.get, .nat⟩ := by
  refine ⟨rfl, ?_⟩
  intro h
  simp [Alphabet.Declares, emptyAlphabet] at h

/-- **Adequacy finding.** Completeness plus `NodupOps` does not pin the lookup,
so the scout's one-sided recommendation must be strengthened to the iff. Stated
as one proposition so the two halves cannot drift apart. -/
theorem completeness_alone_admits_an_unknown_op_fabricator :
    (∀ (a : Alphabet), a.NodupOps → ∀ (op : OpId) (d : OpDesc),
        a.Declares op d → fabricate a op = some d)
      ∧ (∀ (a : Alphabet) (op : OpId), UniqueSome (fabricate a op))
      ∧ (∃ (a : Alphabet) (op : OpId) (d : OpDesc),
          fabricate a op = some d ∧ ¬ a.Declares op d) :=
  ⟨fun a hnd _ _ h => fabricate_satisfies_completeness a hnd h,
   dag_row_holds_of_the_fabricator,
   ⟨emptyAlphabet, .get, ⟨.get, .nat⟩, fabricate_is_unsound.1,
     fabricate_is_unsound.2⟩⟩

/-! ## §5 — positive control, and the estate's actual discipline

The restatement is not vacuously unsatisfiable. On a closed duplicate-free table
the premise is discharged by `decide`, and the estate's own way of discharging
"no duplicate key" on a closed table is an elaboration-time `#guard`
(`Cas/Schema/Declarations.lean:207`), not a premise-carrying lemma. The `#guard`
below mirrors that pattern; the theorem beside it is what the kernel checks and
what the rest of this file uses. -/

/-- A well-formed alphabet: every operation declared once. -/
def goodAlphabet : Alphabet := ⟨[⟨.get, .nat⟩, ⟨.put, .nat⟩, ⟨.ask, .str⟩]⟩

/-- The invariant is decidable and holds. -/
theorem goodAlphabet_nodup : goodAlphabet.NodupOps := by decide

-- The estate's spelling of the same gate, for a closed table
-- (`Cas/Schema/Declarations.lean:207`). Illustrative; `goodAlphabet_nodup`
-- above is the load-bearing statement.
#guard decide ((goodAlphabet.table.map (·.op)).Nodup)

/-- Every clause fires on the good table: search and declaration agree in both
directions, and the row is not satisfied for an operation nobody declared. -/
theorem goodAlphabet_agrees :
    goodAlphabet.lookup .ask = some ⟨.ask, .str⟩
      ∧ goodAlphabet.Declares .ask ⟨.ask, .str⟩
      ∧ (goodAlphabet.lookup .get).isSome = true := by
  refine ⟨by decide, ⟨by simp [goodAlphabet], rfl⟩, by decide⟩

/-! ## §6 — the bridge, and the type-level cost of a duplicate table

`Cas.Lang.Sig` (`Sig.lean:13`) makes answer indexing TOTAL BY TYPING:
`Ans : Op → Type`, no `Option` anywhere. So the operation universe must be
REFINED first, definitionally, and the answer assignment is then `rfl`. This is
`EC1-T004`'s real job — construct the refinement — and it is what makes
`EC1-T004S`'s field projection `(lookup a op).answerTy` elaborate at all, since
`Option.get` has already consumed the `isSome`.

`Sig` is reused, never modified: `toSig` builds a value of the shipped
structure. This is §16's admission bridge for the Operation-families row, not
its prohibited shortcut. -/

/-- Elaborating the alphabet into the EXISTING `Cas.Lang.Sig`. The operations are
the FOUND ops, carrying their found-ness as a proof field. -/
def Alphabet.toSig (a : Alphabet) : Sig where
  Op := { op : OpId // (a.lookup op).isSome = true }
  Ans := fun op => AnsCode.interp ((a.lookup op.1).get op.2).answerTy

/-- The answer assignment is definitional — no residual totality theorem. -/
theorem toSig_answer_is_definitional (a : Alphabet) (op : a.toSig.Op) :
    a.toSig.Ans op = AnsCode.interp ((a.lookup op.1).get op.2).answerTy :=
  rfl

/-- The refinement is inhabited exactly by the declared operations, in both
directions — this is `alphabet_lookup_isSome_iff` at the carrier. -/
def Alphabet.opOfDeclares (a : Alphabet) {op : OpId} {d : OpDesc}
    (h : a.Declares op d) : a.toSig.Op :=
  ⟨op, (alphabet_lookup_isSome_iff a op).mpr ⟨d, h⟩⟩

/-- Reading a `some` back through `Option.get`. -/
theorem lookup_get_eq {δ : Type} {o : Option δ} {d : δ}
    (hs : o.isSome = true) (h : o = some d) : o.get hs = d := by
  subst h
  rfl

/-- **What `EC1-T004` buys downstream.** Under `NodupOps`, the answer type the
bridge assigns a declared operation is the interpretation of THAT DECLARATION's
answer code. Without the premise this is exactly what fails — see below. -/
theorem toSig_ans_of_declares (a : Alphabet) (hnd : a.NodupOps)
    {op : OpId} {d : OpDesc} (h : a.Declares op d) :
    a.toSig.Ans (a.opOfDeclares h) = AnsCode.interp d.answerTy := by
  have hs : (a.lookup op).isSome = true := (a.opOfDeclares h).2
  have hget : (a.lookup op).get hs = d :=
    lookup_get_eq hs (alphabet_lookup_complete a hnd h)
  exact congrArg AnsCode.interp (congrArg OpDesc.answerTy hget)

/-- `get` is found in the duplicate table, so the refinement admits it. -/
theorem dupGet_get_isSome : (dupGet.lookup .get).isSome = true := by decide

/-- **The duplicate table produces a `Sig` that contradicts its own table.**
`dupGet` declares that `get` answers a string; the bridge types `get`'s answer as
`Nat`. Stated at the CODE level, so no type inequality is needed — and then also
at the type level, where the assignment is `rfl`.

This is strictly sharper than §2: the forbidden table does not merely survive the
schematic row, it elaborates to a signature whose answer typing is a lie about a
row of the table it came from. `NodupOps` is what makes the assignment
well-defined. -/
theorem dupGet_toSig_types_a_declared_op_wrongly :
    dupGet.Declares .get ⟨.get, .str⟩
      ∧ ((dupGet.lookup .get).get dupGet_get_isSome).answerTy = AnsCode.nat
      ∧ (AnsCode.nat ≠ AnsCode.str)
      ∧ dupGet.toSig.Ans ⟨.get, dupGet_get_isSome⟩ = Nat :=
  ⟨⟨by simp [dupGet], rfl⟩, by decide, by decide, rfl⟩

/-! ## §7 — nothing is lost by the replacement

The restatement implies the schematic row, so replacing it forfeits nothing. The
converse fails: §2 exhibits a table satisfying the schematic row that the
restatement rejects (`dupGet_is_not_nodup`), and §4b exhibits a lookup satisfying
the schematic row that the restatement rejects (`fabricate_is_unsound`). The
implication is therefore strict in both directions that matter. -/

/-- The schematic row is a consequence of the restatement. -/
theorem restatement_implies_the_schematic_row
    (a : Alphabet) (hnd : a.NodupOps) {op : OpId} {d : OpDesc}
    (h : a.Declares op d) : UniqueSome (a.lookup op) :=
  dag_row_content_is_isSome a.lookup op
    (by rw [alphabet_lookup_complete a hnd h]; rfl)

/-- The whole result in one proposition: the iff, both premises live, and the
schematic row recovered. -/
theorem T004_restated :
    (∀ (a : Alphabet), a.NodupOps → ∀ (op : OpId) (d : OpDesc),
        a.lookup op = some d ↔ a.Declares op d)
      ∧ (∀ (a : Alphabet) (op : OpId),
          (a.lookup op).isSome = true ↔ ∃ d, a.Declares op d)
      ∧ (¬ ∀ (a : Alphabet) (op : OpId) (d : OpDesc),
          a.Declares op d → a.lookup op = some d)
      ∧ (∃ (a : Alphabet) (op : OpId) (d : OpDesc),
          fabricate a op = some d ∧ ¬ a.Declares op d)
      ∧ (∀ (a : Alphabet), a.NodupOps → ∀ (op : OpId) (d : OpDesc),
          a.Declares op d → UniqueSome (a.lookup op)) :=
  ⟨fun a hnd => alphabet_lookup_iff a hnd,
   alphabet_lookup_isSome_iff,
   nodup_premise_is_necessary,
   ⟨emptyAlphabet, .get, ⟨.get, .nat⟩, fabricate_is_unsound.1,
     fabricate_is_unsound.2⟩,
   fun a hnd _ _ h => restatement_implies_the_schematic_row a hnd h⟩

end EffectCoreV1.T004

/-! ## Kernel receipts -/

#print axioms EffectCoreV1.T004.bang_is_free
#print axioms EffectCoreV1.T004.dag_row_content_is_isSome
#print axioms EffectCoreV1.T004.dupGet_declares_two_descriptors
#print axioms EffectCoreV1.T004.dupGet_lookup_picks_the_first
#print axioms EffectCoreV1.T004.dag_row_holds_on_the_duplicate_table
#print axioms EffectCoreV1.T004.dupGet_is_not_nodup
#print axioms EffectCoreV1.T004.dag_row_collapses_under_lookup_membership
#print axioms EffectCoreV1.T004.nodup_key_unique
#print axioms EffectCoreV1.T004.alphabet_declares_unique
#print axioms EffectCoreV1.T004.alphabet_lookup_sound
#print axioms EffectCoreV1.T004.alphabet_lookup_complete
#print axioms EffectCoreV1.T004.alphabet_lookup_iff
#print axioms EffectCoreV1.T004.alphabet_lookup_isSome_iff
#print axioms EffectCoreV1.T004.nodup_premise_is_necessary
#print axioms EffectCoreV1.T004.dag_row_holds_of_the_fabricator
#print axioms EffectCoreV1.T004.fabricate_satisfies_completeness
#print axioms EffectCoreV1.T004.fabricate_is_unsound
#print axioms EffectCoreV1.T004.completeness_alone_admits_an_unknown_op_fabricator
#print axioms EffectCoreV1.T004.goodAlphabet_nodup
#print axioms EffectCoreV1.T004.goodAlphabet_agrees
#print axioms EffectCoreV1.T004.toSig_answer_is_definitional
#print axioms EffectCoreV1.T004.lookup_get_eq
#print axioms EffectCoreV1.T004.toSig_ans_of_declares
#print axioms EffectCoreV1.T004.dupGet_get_isSome
#print axioms EffectCoreV1.T004.dupGet_toSig_types_a_declared_op_wrongly
#print axioms EffectCoreV1.T004.restatement_implies_the_schematic_row
#print axioms EffectCoreV1.T004.T004_restated
