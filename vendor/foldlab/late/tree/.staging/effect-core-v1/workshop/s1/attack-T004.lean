import Cas.Lang.Sig

/-!
# BREAKER attack on `EC1-T004` (`workshop/s1/T004.lean`), slice `EC1-S1`

Skill stage: `.claude/skills/lean/workflows/lean-assurance-review` — the target
is a landed proof claiming `PROVED-STRONGER`, so this is an assurance review run
adversarially, not a proof lane.

Run from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/s1/attack-T004.lean
```

The carrier below is a VERBATIM re-declaration of `T004.lean`'s scratch carrier
(`OpId`, `AnsCode`, `AnsCode.interp`, `OpDesc`, `Alphabet`, `lookup`, `Declares`,
`NodupOps`, `toSig`). Nothing is imported from `T004.lean` — it is not a Lake
module — so soundness and completeness are RE-DERIVED here rather than assumed.
Re-derivation is itself one of the checks: if the landed proofs were unsound the
attacks below would not close.

## What survives

* §1 `UniqueSome o ↔ o.isSome = true` — the target's "the `!` is decoration"
  diagnosis is not merely sound, it is an EQUIVALENCE. `EC1-T004`'s schematic
  row carries exactly the information `(lookup a op).isSome`, no more.
* §5 `EC1-F82` (permute a duplicate-key raw row): survived, but only because
  the target states no permutation law. The positive law is proved here
  (`lookup_perm_congr`) and the negative witness shows the bridge's ANSWER TYPE
  depends on row order without the premise.
* §7 the two headline negatives re-derive independently.

## What does not

* §2 `restatement_implies_the_schematic_row` carries a DEAD premise. §7's prose
  claim ("nothing is lost") is discharged only on duplicate-free alphabets by
  the theorem the file cites; the premise-free recovery is one line and is
  proved here.
* §3 `NodupOps` is NOT the weakest sufficient premise. `alphabet_lookup_iff`
  holds under strictly weaker `FunctionalKeys`, and the two conditions DISAGREE
  on a representable table (`dupSame`). The packet's red control "duplicate op"
  (`TYPE-CLOSURE.md:119`) is therefore not pinned by this row.
* §6 the §6 bridge is PROVABLY BLIND to the duplicate it is used to indict.
  `dupGet` and its de-duplicated shadow have pointwise-equal lookups and an
  EQUAL `toSig.Op` type, so no downstream consumer of the signature can recover
  the red control. It must be refused at admission.
* §8 `NodupOps` is not preserved by table extension, so `EC1-T004X` cannot
  inherit this row's premise.

No `sorry`, no `axiom`, no `native_decide`, no `#eval` carrying a claim. Every
theorem reports `#print axioms` at the foot.
-/

namespace EffectCoreV1.AttackT004

open Cas.Lang

/-! ## §0 — the carrier, re-declared verbatim from `T004.lean` §0/§6 -/

inductive OpId where
  | get | put | ask
  deriving DecidableEq, Repr

inductive AnsCode where
  | nat | str
  deriving DecidableEq, Repr

def AnsCode.interp : AnsCode → Type
  | .nat => Nat
  | .str => String

structure OpDesc where
  op : OpId
  answerTy : AnsCode
  deriving DecidableEq, Repr

structure Alphabet where
  table : List OpDesc
  deriving DecidableEq, Repr

def Alphabet.lookup (a : Alphabet) (op : OpId) : Option OpDesc :=
  a.table.find? (fun d => decide (d.op = op))

def Alphabet.Declares (a : Alphabet) (op : OpId) (d : OpDesc) : Prop :=
  d ∈ a.table ∧ d.op = op

abbrev Alphabet.NodupOps (a : Alphabet) : Prop := (a.table.map (·.op)).Nodup

def UniqueSome {δ : Type} (o : Option δ) : Prop :=
  ∃ d, o = some d ∧ ∀ e, o = some e → e = d

def Alphabet.toSig (a : Alphabet) : Sig where
  Op := { op : OpId // (a.lookup op).isSome = true }
  Ans := fun op => AnsCode.interp ((a.lookup op.1).get op.2).answerTy

/-! ### §0a — soundness and completeness, RE-DERIVED

Independent of the landed proofs. Everything below stands on these. -/

theorem lookup_sound (a : Alphabet) {op : OpId} {d : OpDesc}
    (h : a.lookup op = some d) : a.Declares op d := by
  have h' : a.table.find? (fun x : OpDesc => decide (x.op = op)) = some d := h
  have hraw := List.find?_some h'
  have hkey : d.op = op := of_decide_eq_true hraw
  exact ⟨List.mem_of_find?_eq_some h', hkey⟩

theorem lookup_none_of_not_declared (a : Alphabet) {op : OpId} {d : OpDesc}
    (hd : a.Declares op d) : a.lookup op ≠ none := by
  intro hl
  have hl' : a.table.find? (fun x : OpDesc => decide (x.op = op)) = none := hl
  exact absurd (decide_eq_true hd.2) (List.find?_eq_none.mp hl' d hd.1)

/-! ## §1 — the `!` is not merely free, it is EQUIVALENT to `isSome`

`T004.lean` §1 proves `isSome → UniqueSome`. The converse is immediate, and the
biconditional is the sharp form of the diagnosis: the DAG's
`exists! d, lookup a op = some d` and `(lookup a op).isSome` are the SAME
proposition. Nothing about alphabets, tables or signatures can be recovered from
the schematic row that is not already in the `Bool`. -/

theorem uniqueSome_iff_isSome {δ : Type} (o : Option δ) :
    UniqueSome o ↔ o.isSome = true := by
  constructor
  · rintro ⟨d, hd, -⟩
    rw [hd]; rfl
  · intro h
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp h
    exact ⟨d, hd, fun e he => Option.some.inj (he.symm.trans hd)⟩

/-! ## §2 — FINDING: `restatement_implies_the_schematic_row` carries a DEAD premise

`T004.lean` §7 states, as prose, "The restatement implies the schematic row, so
replacing it forfeits nothing", and cites
`restatement_implies_the_schematic_row`, whose signature is

    (a : Alphabet) (hnd : a.NodupOps) {op d} (h : a.Declares op d)
      : UniqueSome (a.lookup op)

A universally quantified statement with an extra premise is WEAKER, not
stronger, and `hnd` restricts the recovery to exactly the alphabets the
restatement does not reject. On `dupGet` — where the schematic row is TRUE
(`dag_row_holds_on_the_duplicate_table`) — the cited theorem says nothing, so as
landed it does not discharge "nothing is lost" there.

The premise is unnecessary. The recovery is premise-free, and the proof does not
touch `NodupOps` at any point. -/

theorem schematic_row_holds_premise_free
    (a : Alphabet) {op : OpId} {d : OpDesc} (h : a.Declares op d) :
    UniqueSome (a.lookup op) := by
  refine (uniqueSome_iff_isSome _).mpr ?_
  cases hl : a.lookup op with
  | none => exact absurd hl (lookup_none_of_not_declared a h)
  | some _ => rfl

/-- The same fact stated as the comparison `T004.lean` §7 actually needs: the
schematic row holds on EVERY alphabet at every declared operation, duplicate-free
or not. This is what makes "the restatement forfeits nothing" true. -/
theorem nothing_is_lost_unconditionally :
    (∀ (a : Alphabet) (op : OpId) (d : OpDesc),
        a.Declares op d → UniqueSome (a.lookup op))
      ∧ ∀ (a : Alphabet) (op : OpId), UniqueSome (a.lookup op) ↔
          (a.lookup op).isSome = true :=
  ⟨fun a _ _ h => schematic_row_holds_premise_free a h,
   fun a op => uniqueSome_iff_isSome (a.lookup op)⟩

/-! ## §3 — FINDING: `NodupOps` is not the weakest sufficient premise

`nodup_premise_is_necessary` proves the PREMISE-FREE universal false. It does
not show `NodupOps` minimal, and it is not. The property the completeness
direction actually consumes is that no two DISTINCT rows share a key — a
functional-dependence condition. `NodupOps` implies it and is strictly stronger.

This matters because `TYPE-CLOSURE.md:119` names "duplicate op" as a red control
for `Alphabet`/`OpDesc` without spelling it. The two candidate spellings are
inequivalent and disagree on a representable table, and `EC1-T004` as landed
does not say which one the alphabet gate owes. -/

def Alphabet.FunctionalKeys (a : Alphabet) : Prop :=
  ∀ d ∈ a.table, ∀ d' ∈ a.table, d.op = d'.op → d = d'

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

/-- `NodupOps` is sufficient for functional keys. -/
theorem functionalKeys_of_nodup (a : Alphabet) (hnd : a.NodupOps) :
    a.FunctionalKeys :=
  fun _ hd _ hd' hkey => nodup_key_unique (·.op) hnd hd hd' hkey

/-- The completeness direction under the WEAKER premise. -/
theorem lookup_complete_functional (a : Alphabet) (hfk : a.FunctionalKeys)
    {op : OpId} {d : OpDesc} (h : a.Declares op d) : a.lookup op = some d := by
  cases hl : a.lookup op with
  | none => exact absurd hl (lookup_none_of_not_declared a h)
  | some e =>
    have he : a.Declares op e := lookup_sound a hl
    rw [hfk e he.1 d h.1 (he.2.trans h.2.symm)]

/-- **`alphabet_lookup_iff` under a strictly weaker hypothesis.** -/
theorem lookup_iff_functional (a : Alphabet) (hfk : a.FunctionalKeys)
    (op : OpId) (d : OpDesc) : a.lookup op = some d ↔ a.Declares op d :=
  ⟨lookup_sound a, lookup_complete_functional a hfk⟩

/-- A table with a literally repeated row. `NodupOps` REFUSES it; the theorem
does not need to. -/
def dupSame : Alphabet := ⟨[⟨.get, .nat⟩, ⟨.get, .nat⟩]⟩

theorem dupSame_is_not_nodup : ¬ dupSame.NodupOps := by decide

theorem dupSame_has_functional_keys : dupSame.FunctionalKeys := by
  intro d hd d' hd' _
  simp [dupSame] at hd hd'
  subst hd
  subst hd'
  rfl

/-- **Minimality finding.** The landed premise is strictly stronger than what
the conclusion needs, and the gap is inhabited by a table the packet's red
control has to rule on and this row does not. -/
theorem nodup_is_not_the_weakest_premise :
    ¬ dupSame.NodupOps
      ∧ dupSame.FunctionalKeys
      ∧ (∀ (op : OpId) (d : OpDesc),
          dupSame.lookup op = some d ↔ dupSame.Declares op d)
      ∧ (∀ (a : Alphabet), a.NodupOps → a.FunctionalKeys) :=
  ⟨dupSame_is_not_nodup, dupSame_has_functional_keys,
   lookup_iff_functional dupSame dupSame_has_functional_keys,
   functionalKeys_of_nodup⟩

/-! ## §4 — the duplicate table, re-declared, and the negatives re-derived -/

def dupGet : Alphabet := ⟨[⟨.get, .nat⟩, ⟨.get, .str⟩]⟩

theorem dupGet_lookup_picks_the_first :
    dupGet.lookup .get = some ⟨.get, .nat⟩ := by decide

/-- `nodup_premise_is_necessary`, re-derived independently. -/
theorem nodup_premise_is_necessary_recheck :
    ¬ ∀ (a : Alphabet) (op : OpId) (d : OpDesc),
        a.Declares op d → a.lookup op = some d := by
  intro h
  have hbad := h dupGet .get ⟨.get, .str⟩ ⟨by simp [dupGet], rfl⟩
  rw [dupGet_lookup_picks_the_first] at hbad
  exact absurd (Option.some.inj hbad) (by decide)

def fabricate (a : Alphabet) (op : OpId) : Option OpDesc :=
  match a.lookup op with
  | some d => some d
  | none => some ⟨op, .nat⟩

def emptyAlphabet : Alphabet := ⟨[]⟩

/-- `fabricate_is_unsound`, re-derived independently. -/
theorem fabricate_is_unsound_recheck :
    fabricate emptyAlphabet .get = some ⟨.get, .nat⟩
      ∧ ¬ emptyAlphabet.Declares .get ⟨.get, .nat⟩ := by
  refine ⟨rfl, ?_⟩
  intro h
  simp [Alphabet.Declares, emptyAlphabet] at h

/-! ## §5 — `EC1-F82`: permute a duplicate-key raw row

`CONTRACT-PACKET.md:745`. The falsifier's stated response is "duplicate-free
premise is unavailable and admission rejects both rows; no permutation theorem
applies". `T004.lean` states NO permutation theorem, so the falsifier cannot be
tripped there — it is survived by silence.

Both halves are supplied here. The NEGATIVE half shows the cost of the silence:
without the premise the bridge's ANSWER TYPE is a function of row order, so a
permutation of one forbidden table changes the meaning of the signature it
elaborates to. The POSITIVE half is the law that does hold, the exact analogue
of the estate's `Cas/Backend/Canon.lean:313 canonServices_perm`, which takes the
LEFT `Nodup` and derives the right from the permutation. -/

def dupGetSwapped : Alphabet := ⟨[⟨.get, .str⟩, ⟨.get, .nat⟩]⟩

theorem dupGetSwapped_is_a_permutation :
    dupGet.table.Perm dupGetSwapped.table :=
  List.Perm.swap _ _ []

theorem dupGet_get_isSome : (dupGet.lookup .get).isSome = true := by decide
theorem dupGetSwapped_get_isSome : (dupGetSwapped.lookup .get).isSome = true := by
  decide

/-- **`EC1-F82`, negative half.** One permutation of a duplicate-key table; two
different signatures. `Nat` on one side, `String` on the other, both by `rfl`. -/
theorem permutation_changes_the_answer_type :
    dupGet.table.Perm dupGetSwapped.table
      ∧ dupGet.lookup .get ≠ dupGetSwapped.lookup .get
      ∧ dupGet.toSig.Ans ⟨.get, dupGet_get_isSome⟩ = Nat
      ∧ dupGetSwapped.toSig.Ans ⟨.get, dupGetSwapped_get_isSome⟩ = String :=
  ⟨dupGetSwapped_is_a_permutation, by decide, rfl, rfl⟩

/-- **`EC1-F82`, positive half — the law `T004.lean` omits.** Under the
duplicate-free premise the search is permutation-invariant, so the bridge's
meaning does not depend on row order. Stated with the premise on the LEFT only,
matching `canonServices_perm`. -/
theorem lookup_perm_congr {a b : Alphabet} (hnd : a.NodupOps)
    (hp : a.table.Perm b.table) (op : OpId) : a.lookup op = b.lookup op := by
  have hnd' : b.NodupOps := (hp.map (·.op)).nodup hnd
  have hmem : ∀ d : OpDesc, a.Declares op d ↔ b.Declares op d := fun d =>
    ⟨fun h => ⟨(hp.mem_iff).mp h.1, h.2⟩, fun h => ⟨(hp.mem_iff).mpr h.1, h.2⟩⟩
  cases hl : a.lookup op with
  | some d =>
    exact (lookup_complete_functional b (functionalKeys_of_nodup b hnd')
      ((hmem d).mp (lookup_sound a hl))).symm
  | none =>
    cases hr : b.lookup op with
    | none => rfl
    | some e =>
      have hda : a.Declares op e := (hmem e).mpr (lookup_sound b hr)
      exact absurd hl (lookup_none_of_not_declared a hda)

/-- The invariance transported to the bridge: the refinement's inhabitants agree
pointwise under permutation of a duplicate-free table. -/
theorem toSig_op_predicate_perm_invariant {a b : Alphabet} (hnd : a.NodupOps)
    (hp : a.table.Perm b.table) :
    (fun op : OpId => (a.lookup op).isSome = true)
      = (fun op : OpId => (b.lookup op).isSome = true) := by
  funext op
  rw [lookup_perm_congr hnd hp op]

/-! ## §6 — FINDING: the §6 bridge is BLIND to the duplicate it indicts

`dupGet_toSig_types_a_declared_op_wrongly` shows the duplicate table elaborates
to a signature that contradicts a row of the table. The sharper fact is that the
signature CANNOT WITNESS THE CONTRADICTION: `toSig` factors entirely through
`lookup`, which is a lossy projection of `table`, and the shadowed row is
invisible to it.

`dedupGet` deletes the shadowed row — `EC1-F01` at the alphabet carrier. The
declaration relation changes; the lookup does not change at ANY operation; and
the refinement `toSig.Op` is the SAME TYPE. So no consumer downstream of the
bridge can distinguish the forbidden table from an admissible one, and
`NodupOps` cannot be recovered after the bridge. It has to be a gate at
admission, which is what `TYPE-CLOSURE.md:119`'s red control requires and what
`T004.lean`'s `#guard` only illustrates. -/

def dedupGet : Alphabet := ⟨[⟨.get, .nat⟩]⟩

theorem dedupGet_is_nodup : dedupGet.NodupOps := by decide

/-- Deleting the shadowed row is invisible to the search, at every operation. -/
theorem lookup_cannot_see_the_deletion (op : OpId) :
    dupGet.lookup op = dedupGet.lookup op := by
  cases op <;> rfl

/-- …and therefore the refinement is the SAME TYPE. -/
theorem toSig_op_cannot_see_the_deletion : dupGet.toSig.Op = dedupGet.toSig.Op := by
  show Subtype (fun op : OpId => (dupGet.lookup op).isSome = true)
      = Subtype (fun op : OpId => (dedupGet.lookup op).isSome = true)
  exact congrArg Subtype (funext fun op => by rw [lookup_cannot_see_the_deletion op])

/-- **Blindness finding.** A forbidden table and an admissible one, identical
under everything `EC1-T004`'s bridge can observe, differing in the declaration
`TYPE-CLOSURE.md:119`'s red control exists to catch. -/
theorem the_bridge_cannot_recover_the_red_control :
    dupGet.Declares .get ⟨.get, .str⟩
      ∧ ¬ dedupGet.Declares .get ⟨.get, .str⟩
      ∧ ¬ dupGet.NodupOps
      ∧ dedupGet.NodupOps
      ∧ (∀ op : OpId, dupGet.lookup op = dedupGet.lookup op)
      ∧ dupGet.toSig.Op = dedupGet.toSig.Op := by
  refine ⟨⟨by simp [dupGet], rfl⟩, ?_, by decide, dedupGet_is_nodup,
    lookup_cannot_see_the_deletion, toSig_op_cannot_see_the_deletion⟩
  intro h
  simp [Alphabet.Declares, dedupGet] at h

/-! ## §7 — positive controls: nothing above is vacuous

Every premise used in this file is inhabited, and the iff has content in both
directions on a good table. -/

def goodAlphabet : Alphabet := ⟨[⟨.get, .nat⟩, ⟨.put, .nat⟩, ⟨.ask, .str⟩]⟩

theorem goodAlphabet_nodup : goodAlphabet.NodupOps := by decide

theorem positive_control :
    goodAlphabet.NodupOps
      ∧ goodAlphabet.FunctionalKeys
      ∧ goodAlphabet.lookup .ask = some ⟨.ask, .str⟩
      ∧ goodAlphabet.Declares .ask ⟨.ask, .str⟩
      ∧ emptyAlphabet.lookup .get = none
      ∧ ¬ ∃ d, emptyAlphabet.Declares .get d := by
  refine ⟨goodAlphabet_nodup, functionalKeys_of_nodup _ goodAlphabet_nodup,
    by decide, ⟨by simp [goodAlphabet], rfl⟩, rfl, ?_⟩
  rintro ⟨d, hd, -⟩
  simp [emptyAlphabet] at hd

/-! ## §8 — FINDING: the premise does not survive to `EC1-T004X`

`PROOF-DAG.md:195` owes
`alphabet_sum_preserves_arms : extend a b |>.toSig = a.toSig ⊕ₛ b.toSig`.
Whatever `extend` is, it must at least join two tables. `NodupOps` is NOT closed
under that join: two duplicate-free alphabets whose key sets overlap produce a
table this row's premise refuses. So `EC1-T004X` cannot inherit `EC1-T004`'s
premise, and the packet states no key-disjointness side condition anywhere.

The consequence at the bridge is concrete: the joined table exposes ONE
operation keyed `get`, answering `Nat`, while `a.toSig ⊕ₛ b.toSig` has TWO,
answering `Nat` and `String`. An arm is silently dropped. -/

def leftA : Alphabet := ⟨[⟨.get, .nat⟩]⟩
def rightB : Alphabet := ⟨[⟨.get, .str⟩]⟩
def joined : Alphabet := ⟨leftA.table ++ rightB.table⟩

theorem nodup_is_not_closed_under_join :
    leftA.NodupOps ∧ rightB.NodupOps ∧ ¬ joined.NodupOps := by
  refine ⟨by decide, by decide, ?_⟩
  decide

theorem leftA_get_isSome : (leftA.lookup .get).isSome = true := by decide
theorem rightB_get_isSome : (rightB.lookup .get).isSome = true := by decide
theorem joined_get_isSome : (joined.lookup .get).isSome = true := by decide

/-- The sum keeps both arms; the joined table keeps one. `String` is reachable on
the left of the equation `EC1-T004X` proposes and unreachable on the right. -/
theorem join_drops_an_arm :
    (leftA.toSig ⊕ₛ rightB.toSig).Ans (.inl ⟨.get, leftA_get_isSome⟩) = Nat
      ∧ (leftA.toSig ⊕ₛ rightB.toSig).Ans (.inr ⟨.get, rightB_get_isSome⟩) = String
      ∧ joined.toSig.Ans ⟨.get, joined_get_isSome⟩ = Nat
      ∧ ∀ z : joined.toSig.Op, joined.toSig.Ans z = Nat := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rintro ⟨op, hop⟩
  cases op with
  | get => rfl
  | put => exact absurd hop (by decide)
  | ask => exact absurd hop (by decide)

end EffectCoreV1.AttackT004

/-! ## Kernel receipts -/

#print axioms EffectCoreV1.AttackT004.lookup_sound
#print axioms EffectCoreV1.AttackT004.lookup_none_of_not_declared
#print axioms EffectCoreV1.AttackT004.uniqueSome_iff_isSome
#print axioms EffectCoreV1.AttackT004.schematic_row_holds_premise_free
#print axioms EffectCoreV1.AttackT004.nothing_is_lost_unconditionally
#print axioms EffectCoreV1.AttackT004.nodup_key_unique
#print axioms EffectCoreV1.AttackT004.functionalKeys_of_nodup
#print axioms EffectCoreV1.AttackT004.lookup_complete_functional
#print axioms EffectCoreV1.AttackT004.lookup_iff_functional
#print axioms EffectCoreV1.AttackT004.dupSame_is_not_nodup
#print axioms EffectCoreV1.AttackT004.dupSame_has_functional_keys
#print axioms EffectCoreV1.AttackT004.nodup_is_not_the_weakest_premise
#print axioms EffectCoreV1.AttackT004.dupGet_lookup_picks_the_first
#print axioms EffectCoreV1.AttackT004.nodup_premise_is_necessary_recheck
#print axioms EffectCoreV1.AttackT004.fabricate_is_unsound_recheck
#print axioms EffectCoreV1.AttackT004.dupGetSwapped_is_a_permutation
#print axioms EffectCoreV1.AttackT004.permutation_changes_the_answer_type
#print axioms EffectCoreV1.AttackT004.lookup_perm_congr
#print axioms EffectCoreV1.AttackT004.toSig_op_predicate_perm_invariant
#print axioms EffectCoreV1.AttackT004.dedupGet_is_nodup
#print axioms EffectCoreV1.AttackT004.lookup_cannot_see_the_deletion
#print axioms EffectCoreV1.AttackT004.toSig_op_cannot_see_the_deletion
#print axioms EffectCoreV1.AttackT004.the_bridge_cannot_recover_the_red_control
#print axioms EffectCoreV1.AttackT004.goodAlphabet_nodup
#print axioms EffectCoreV1.AttackT004.positive_control
#print axioms EffectCoreV1.AttackT004.nodup_is_not_closed_under_join
#print axioms EffectCoreV1.AttackT004.join_drops_an_arm
