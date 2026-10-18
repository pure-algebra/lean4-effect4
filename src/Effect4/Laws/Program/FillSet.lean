import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Program.FillReference
import Effect4.Laws.Program.Typing.PartsTable
import Effect4.Laws.Program.AddressMove
import Effect4.Laws.Program.Edit
import Effect4.Laws.Program.SourceTable
import Effect4.Laws.Program.PathFold
import Effect4.Laws.Program.ReferenceTyping
import Effect4.Laws.Program.Typing.SigData

/-!
# Laws.Program.FillSet — fixed-base parallel fills and deterministic materialization

Slice D of `docs/research/2026-10-17-proof-scout/README.md` (§7.4).

* D1 (`Table.typedAt_splice_outside`): a splice keeps the typed entry of an address outside its subtree.
* D2 (`at_replaceAt_incomparable`): a replacement keeps the node at an incomparable address.
* D3 (`sigAt_fillAt`): a fill below the root keeps the signature of every address.
* D4 (`focusAt_fill_incomparable`): an exact fill keeps the focus at an incomparable address.
* D5 (`fills_compose`): certified fills at pairwise incomparable addresses all apply and keep the
  base's type.
* D6 (`materialize_congr`): two lists with the same members and no located conflict FillReference.materialize
  alike, via `lookup_congr`, `ordered_congr`, and `conflictFree_of_conflictAt`.
* D7 (`ordered_compose`): the materializer's order satisfies D5's premises.
* D8 (`refSites_replaceAt_nil`): a reference-free fill keeps a program free of references.
* D9 (`materialize_refFree`): the materializer accepts a conflict-free set of certified
  reference-free fills through the source check, at the base's type.
* Construction invariant (`FillSet.add_wf`, from `FillSet.wellFormed`): every sealed set has
  conflict-free entries at incomparable addresses, each accepted by the anchor's keepExact feed.
* `kept_eq_certified` and `FillSet.publish_eq_materialize` connect the new operations to the
  retained D1–D9 reference observations. Their positive-base and reference-free premises remain
  explicit. D9 is the publication's consumer; D6 has no consumer since the old materializing
  operations were removed.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Effect4.Program

open Effect4 Effect4.Store
open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing (HasTy check_complete check_sound effTy_sound)

/-! ## Symmetry and decidability of `Incomparable` -/

theorem Incomparable.symm {a b : List Nat} (h : Incomparable a b) : Incomparable b a :=
  ⟨h.2, h.1⟩

theorem incomparable_of_incomparableB {a b : List Nat} (h : incomparableB a b = true) :
    Incomparable a b := by
  unfold incomparableB at h
  cases hu1 : Table.under a b <;> cases hu2 : Table.under b a
  · exact ⟨hu1, hu2⟩
  · rw [hu1, hu2] at h; cases h
  · rw [hu1, hu2] at h; cases h
  · rw [hu1, hu2] at h; cases h

/-! ## D1: a splice keeps the entries outside its subtree -/

theorem filter_outside_nil {a b : List Nat} (hb : Table.under a b = false) :
    ∀ {L : List Table.Entry}, (∀ e ∈ L, Table.under a e.path = true) →
      L.filter (fun e => decide (e.path = b)) = []
  | [], _ => rfl
  | e :: L, hL => by
    have he := hL e List.mem_cons_self
    have hne : decide (e.path = b) = false := by
      cases hd : decide (e.path = b) with
      | false => rfl
      | true =>
        rw [decide_eq_true_eq] at hd
        rw [hd, hb] at he
        cases he
    rw [List.filter_cons_of_neg (by rw [hne]; exact Bool.false_ne_true)]
    exact filter_outside_nil hb (fun e' he' => hL e' (List.mem_cons_of_mem _ he'))

/-- **D1: a splice keeps the typed entry of an address outside the spliced subtree.**

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: step D1 of the proposed claim `workspace-fill-agreement` (role compatibility);
   consumer: `focusAt_fill_incomparable` (D4).
3. Reach: one address table `old`, any replacement subtree `sub` rooted at `a`, and any address `b`
   with `Table.under a b = false`.
4. What it does not establish: entries inside the spliced subtree `a`.
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem Table.typedAt_splice_outside {old sub : List Table.Entry} {a b : List Nat}
    (hb : Table.under a b = false) (hsub : ∀ e ∈ sub, Table.under a e.path = true) :
    Table.typedAt (Table.splice old a sub) b = Table.typedAt old b := by
  have hfind : (Table.splice old a sub).find? (fun e => decide (e.path = b)) =
      old.find? (fun e => decide (e.path = b)) := by
    rw [← List.head?_filter, ← List.head?_filter]
    congr 1
    have hmid : ∀ e ∈ ((old.dropWhile fun e => !Table.under a e.path).takeWhile
        fun e => Table.under a e.path), Table.under a e.path = true :=
      fun e he => List.all_eq_true.mp List.all_takeWhile e he
    conv => rhs; rw [← List.takeWhile_append_dropWhile (p := fun e => !Table.under a e.path) (l := old)]
    conv => rhs; rw [← List.takeWhile_append_dropWhile (p := fun e => Table.under a e.path)
      (l := old.dropWhile fun e => !Table.under a e.path)]
    unfold Table.splice
    simp only [List.filter_append, filter_outside_nil hb hsub, filter_outside_nil hb hmid,
      List.append_nil, List.nil_append]
  unfold Table.typedAt
  rw [hfind]

/-! ## D2: a replacement keeps the node at an incomparable address -/

/-- **D2: a replacement keeps the node at an incomparable address.**

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: step D2 of the proposed claim `workspace-fill-agreement` (role compatibility);
   consumer: `focusAt_fill_incomparable` (D4).
3. Reach: any node `n`, replacement `r` at `a`, and address `b` with `Incomparable a b`.
4. What it does not establish: nodes at an ancestor or descendant of `a`.
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem at_replaceAt_incomparable {n n' r : Node NativeOp} {a b : List Nat}
    (h : n.replaceAt a r = some n') (hinc : Incomparable a b) : n'.at_ b = n.at_ b := by
  rcases Path.prefix_cases a b with ⟨rest, rfl⟩ | ⟨i, rest, rfl⟩ | ⟨c, i, j, x, y, hij, rfl, rfl⟩
  · have hu := Table.under_append b rest
    rw [hinc.2] at hu
    cases hu
  · have hu := Table.under_append a (i :: rest)
    rw [hinc.1] at hu
    cases hu
  · exact Node.at_replaceAt_disjoint c x y h (Ne.symm hij)

/-! ## D3: a fill below the root keeps the signature of every address

`sigAt_fillAt` (D3), with `bodyAt_sig_replaceAt` and `partAt_sig_replaceAt`, lives in
`Laws/Program/SourceTable.lean`: the feed's splice law reads it too. -/

/-! ## D4: an exact fill keeps the focus at an incomparable address -/

/-- **D4: an exact fill keeps the focus at an incomparable address.**

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: step D4 of the proposed claim `workspace-fill-agreement` (role compatibility);
   consumer: `fills_compose` (D5).
3. Reach: one checked sketch `s`, a certified exact fill at `p1 ≠ []`, and an incomparable
   focus at `p2` (`Incomparable p1 p2`).
4. What it does not establish: fills that change their focus's type (`keepExactType` is required),
   or addresses comparable with `p1`.
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem focusAt_fill_incomparable {s s' : Sketch} {app : SigApp} {T : EffTy} {p1 p2 : List Nat}
    {f1 f2 : Focus NativeOp} {q1 : NativeEff}
    (hs : s.check app = .ok T) (hp1 : p1 ≠ []) (hf1 : s.focusAt app p1 = some f1)
    (hq1 : HasTy (s.sigAt app p1) f1.env q1 f1.ty) (hfill : s.fillAt p1 q1 = some s')
    (hf2 : s.focusAt app p2 = some f2) (hinc : Incomparable p1 p2) :
    s'.focusAt app p2 = some f2 := by
  have hp2 : p2 ≠ [] := by
    intro h0
    subst h0
    have hu : Table.under [] p1 = true := rfl
    rw [hinc.2] at hu
    cases hu
  have htable := Sketch.table_fill hs hp1 hf1 hq1 hfill
  have hsub : ∀ e ∈ tableAt (s.sigAt app p1) (some (.env f1.env)) (.eff q1) p1,
      Table.under p1 e.path = true := by
    intro e he
    obtain ⟨b, hb⟩ := tableAt_path he
    rw [hb]
    exact Table.under_append p1 b
  have htyped : Table.typedAt (s'.table app) p2 = some (f2.env, f2.ty) := by
    rw [htable, Table.typedAt_splice_outside hinc.1 hsub]
    exact Table.typedAt_table_of_focusAt hf2 hp2
  obtain ⟨q, hq⟩ := Table.typedAt_table htyped hp2
  obtain ⟨p', hrep, rfl⟩ := Sketch.fillAt_some hfill
  have hat' := Sketch.focusAt_at hq
  have hat := Sketch.focusAt_at hf2
  rw [at_replaceAt_incomparable hrep hinc, hat] at hat'
  simp only [Option.some.injEq, Node.eff.injEq] at hat'
  rw [hq, ← hat']

/-! ## D5: certified fills at incomparable addresses compose -/

/-- `FillReference.certifiedB` soundness: when `FillReference.certifiedB s app p q = true`, `(p, q)` is `FillReference.Certified s app`. -/
theorem certified_of_certifiedB {s : Sketch} {app : SigApp} {p : List Nat} {q : NativeEff}
    (h : FillReference.certifiedB s app p q = true) : FillReference.Certified s app (p, q) := by
  unfold FillReference.certifiedB at h
  obtain ⟨hp, hf⟩ := Bool.and_eq_true_iff.mp h
  have hp_ne : p ≠ [] := by
    intro h0
    subst h0
    cases hp
  cases hfocus : s.focusAt app p with
  | none =>
    rw [hfocus] at hf
    cases hf
  | some f =>
    rw [hfocus] at hf
    have hchk : Checker.check (s.sigAt app p) f.env p q = .ok f.ty :=
      decide_eq_true_eq.mp hf
    exact ⟨hp_ne, f, hfocus, effTy_sound _ _ _ _ (effTy_of_check hchk)⟩

/-- **D5: fills certified against one base, at pairwise incomparable addresses, all apply, and
the result keeps the base's type.**

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: step D5 of the proposed claim `workspace-fill-agreement` (role compatibility);
   consumer: `ordered_compose` (D7).
3. Reach: one checked base sketch `s`, a list of fills pairwise `Incomparable` and each `FillReference.Certified`
   against `s` and `app`.
4. What it does not establish: source admission through layer references (`Sketch.sourceCheck`),
   which `materialize_refFree` (D9) and `FillReference.materialize` cover.
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem fills_compose {app : SigApp} {T : EffTy} :
    ∀ (fills : List (List Nat × NativeEff)) (s : Sketch), s.check app = .ok T →
      fills.Pairwise (fun a b => Incomparable a.1 b.1) →
      (∀ x ∈ fills, FillReference.Certified s app x) →
      ∃ s', applyFills s fills = some s' ∧ s'.check app = .ok T
  | [], s, hs, _, _ => ⟨s, rfl, hs⟩
  | (p, q) :: rest, s, hs, hpw, hcert => by
    obtain ⟨hp, f, hf, hq⟩ := hcert (p, q) List.mem_cons_self
    obtain ⟨p', hrep⟩ := Node.replaceAt_eff q (Sketch.focusAt_at hf)
    have hfill := Sketch.fillAt_of_replaceAt hrep
    have hs1 := Sketch.check_fill_kept hs hf hq hrep
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpw
    have hcert' : ∀ x ∈ rest, FillReference.Certified { s with program := p' } app x := by
      intro x hx
      obtain ⟨hxp, fx, hfx, hqx⟩ := hcert x (List.mem_cons_of_mem _ hx)
      refine ⟨hxp, fx, focusAt_fill_incomparable hs hp hf hq hfill hfx (hhead x hx), ?_⟩
      rw [sigAt_fillAt hp hfill x.1]
      exact hqx
    obtain ⟨s', happ, hs'⟩ := fills_compose rest { s with program := p' } hs1 htail hcert'
    refine ⟨s', ?_, hs'⟩
    simp only [applyFills, hfill, Option.bind_some, happ]

/-! ## D6 and D7: the materializer's canonical order and set congruence -/

/-- No address has two different fillings in the set. -/
def ConflictFree (fs : List (List Nat × NativeEff)) : Prop :=
  ∀ x ∈ fs, ∀ y ∈ fs, x.1 = y.1 → x = y

/-- **A conflict-free set's lookup reads its members only**: two lists with the same members
answer alike, whatever their order and repeats. -/
theorem lookup_congr {fs gs : List (List Nat × NativeEff)} (hmem : ∀ x, x ∈ fs ↔ x ∈ gs)
    (hcf : ConflictFree fs) (a : List Nat) : lookup fs a = lookup gs a := by
  unfold lookup
  cases hf : fs.find? (fun x => decide (x.1 = a)) with
  | some x =>
    have hxa : x.1 = a := by
      have := List.find?_some hf
      rwa [decide_eq_true_eq] at this
    have hxg : x ∈ gs := (hmem x).mp (List.mem_of_find?_eq_some hf)
    cases hg : gs.find? (fun x => decide (x.1 = a)) with
    | some y =>
      have hya : y.1 = a := by
        have := List.find?_some hg
        rwa [decide_eq_true_eq] at this
      have hyf : y ∈ fs := (hmem y).mpr (List.mem_of_find?_eq_some hg)
      have hxy : x = y := hcf x (List.mem_of_find?_eq_some hf) y hyf (hxa.trans hya.symm)
      rw [hxy]
    | none =>
      have := List.find?_eq_none.mp hg x hxg
      rw [decide_eq_true_eq] at this
      exact absurd hxa this
  | none =>
    cases hg : gs.find? (fun x => decide (x.1 = a)) with
    | some y =>
      have hya : y.1 = a := by
        have := List.find?_some hg
        rwa [decide_eq_true_eq] at this
      have hyf : y ∈ fs := (hmem y).mpr (List.mem_of_find?_eq_some hg)
      have := List.find?_eq_none.mp hf y hyf
      rw [decide_eq_true_eq] at this
      exact absurd hya this
    | none => rfl

theorem mem_uniq : ∀ {l : List (List Nat)} {x : List Nat}, x ∈ uniq l ↔ x ∈ l
  | [], _ => Iff.rfl
  | a :: l, x => by
    unfold uniq
    split
    · rename_i ha
      rw [mem_uniq, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun hx => hx ▸ ha) id⟩
    · rw [List.mem_cons, mem_uniq, List.mem_cons]

theorem uniq_pairwise : ∀ (l : List (List Nat)), (uniq l).Pairwise (· ≠ ·)
  | [] => List.Pairwise.nil
  | a :: l => by
    unfold uniq
    split
    · exact uniq_pairwise l
    · rename_i ha
      refine List.pairwise_cons.mpr ⟨fun b hb hab => ha ?_, uniq_pairwise l⟩
      rw [hab]
      exact mem_uniq.mp hb

/-- **The order is a function of the set.** -/
theorem ordered_congr {base : Sketch} {fs gs : List (List Nat × NativeEff)}
    (hmem : ∀ x, x ∈ fs ↔ x ∈ gs) (hcf : ConflictFree fs) : ordered base fs = ordered base gs := by
  have hl : lookup fs = lookup gs := funext (lookup_congr hmem hcf)
  unfold ordered
  rw [hl]

/-- A member of the ordered list is a member of the set. -/
theorem ordered_mem {base : Sketch} {fs : List (List Nat × NativeEff)} {x : List Nat × NativeEff}
    (hx : x ∈ ordered base fs) : x ∈ fs := by
  unfold ordered at hx
  obtain ⟨a, -, ha⟩ := List.mem_filterMap.mp hx
  unfold lookup at ha
  cases hf : fs.find? (fun y => decide (y.1 = a)) with
  | none =>
    rw [hf] at ha
    cases ha
  | some y =>
    rw [hf] at ha
    have hya : y.1 = a := by
      have := List.find?_some hf
      rwa [decide_eq_true_eq] at this
    simp only [Option.map_some, Option.some.injEq] at ha
    have hy : y = (a, y.2) := Prod.ext hya rfl
    rw [← ha, ← hy]
    exact List.mem_of_find?_eq_some hf

/-- The ordered list holds each address once. -/
theorem ordered_pairwise (base : Sketch) (fs : List (List Nat × NativeEff)) :
    (ordered base fs).Pairwise (fun x y => x.1 ≠ y.1) := by
  unfold ordered
  refine List.Pairwise.filterMap _ (fun a a' hne b hb b' hb' => ?_) (uniq_pairwise _)
  simp only [Option.map_eq_some_iff] at hb hb'
  obtain ⟨q, -, rfl⟩ := hb
  obtain ⟨q', -, rfl⟩ := hb'
  exact hne

/-- **D7: the materializer's fills compose**: a conflict-free set of certified fills whose distinct
addresses are incomparable applies in the base's address order, and keeps the base's type.

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: step D7 of the proposed claim `workspace-fill-agreement` (role compatibility);
   consumer: `materialize_refFree` (D9).
3. Reach: one checked base sketch `base`, and a set `fs` of certified fills whose distinct addresses
   are `Incomparable`.
4. What it does not establish: source admission through layer references (`Sketch.sourceCheck`).
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem ordered_compose {app : SigApp} {T : EffTy} {base : Sketch}
    {fs : List (List Nat × NativeEff)} (hs : base.check app = .ok T)
    (hinc : ∀ x ∈ fs, ∀ y ∈ fs, x.1 ≠ y.1 → Incomparable x.1 y.1)
    (hcert : ∀ x ∈ fs, FillReference.Certified base app x) :
    ∃ s', applyFills base (ordered base fs) = some s' ∧ s'.check app = .ok T := by
  refine fills_compose _ base hs ?_ (fun x hx => hcert x (ordered_mem hx))
  exact List.Pairwise.imp_of_mem (fun hx hy hne => hinc _ (ordered_mem hx) _ (ordered_mem hy) hne)
    (ordered_pairwise base fs)

/-- A set with no located conflict is conflict-free. -/
theorem conflictFree_of_conflictAt {fs : List (List Nat × NativeEff)} (h : FillReference.conflictAt fs = none) :
    ConflictFree fs := by
  intro x hx y hy hxy
  unfold FillReference.conflictAt at h
  have hnone : fs.find? (fun x => fs.any fun y => decide (y.1 = x.1) && decide (y.2 ≠ x.2)) = none := by
    cases hf : fs.find? (fun x => fs.any fun y => decide (y.1 = x.1) && decide (y.2 ≠ x.2)) with
    | none => rfl
    | some z =>
      rw [hf] at h
      cases h
  have hx' := List.find?_eq_none.mp hnone x hx
  have h2 : x.2 = y.2 := by
    cases hd : decide (y.2 = x.2) with
    | true => exact (decide_eq_true_eq.mp hd).symm
    | false =>
      exfalso
      apply hx'
      refine List.any_eq_true.mpr ⟨y, hy, ?_⟩
      have hne : y.2 ≠ x.2 := fun he => by
        rw [decide_eq_true he] at hd
        cases hd
      rw [decide_eq_true hxy.symm, decide_eq_true hne]
      rfl
  exact Prod.ext hxy h2

/-- Converse of `conflictFree_of_conflictAt`: a `ConflictFree` list has `FillReference.conflictAt fs = none`. -/
theorem conflictAt_eq_none_of_conflictFree {fs : List (List Nat × NativeEff)}
    (hcf : ConflictFree fs) : FillReference.conflictAt fs = none := by
  unfold FillReference.conflictAt
  suffices hnone : fs.find? (fun x => fs.any fun y => decide (y.1 = x.1) && decide (y.2 ≠ x.2)) = none by
    rw [hnone]
    rfl
  refine List.find?_eq_none.mpr fun x hx htrue => ?_
  obtain ⟨y, hy, hboth⟩ := List.any_eq_true.mp htrue
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hboth
  have hxy : y = x := hcf y hy x hx (decide_eq_true_eq.mp h1)
  have hne : y.2 ≠ x.2 := decide_eq_true_eq.mp h2
  exact hne (congrArg Prod.snd hxy)

/-! ## The materializer's address checks

`FillReference.materialize` refuses a root fill and a fill where the base holds no program, before it orders the
fills. Both checks read the fills' members only, so D6 still holds, and certified fills pass both,
so D9 still holds. -/

/-- Two lists with the same members agree on `List.any`.

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: a step of D6 (`materialize_congr`), the first half of the proposed claim
   `workspace-fill-agreement` (role compatibility); consumer: `materialize_congr`.
3. Reach: any two lists with the same members, and any test.
4. What it does not establish: anything about the order or the repeats of the lists.
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem any_eq_of_mem_iff {α : Type} {fs gs : List α} (hmem : ∀ x, x ∈ fs ↔ x ∈ gs) (P : α → Bool) :
    fs.any P = gs.any P := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, (hmem x).mp hx, h⟩, fun ⟨x, hx, h⟩ => ⟨x, (hmem x).mpr hx, h⟩⟩

/-- A certified fill names no root, and an address at which the base holds a program.

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: a step of D9 (`materialize_refFree`), the second half of the proposed claim
   `workspace-fill-agreement` (role compatibility); consumer: `certified_passes_checks`.
3. Reach: any fill `FillReference.Certified` against a sketch and an application.
4. What it does not establish: that the fill applies beside other fills (D5 does).
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem holdsProgram_of_certified {s : Sketch} {app : SigApp} {x : List Nat × NativeEff}
    (h : FillReference.Certified s app x) : x.1.isEmpty = false ∧ holdsProgram s x.1 = true := by
  obtain ⟨hne, f, hf, -⟩ := h
  refine ⟨?_, ?_⟩
  · cases hx : x.1 with
    | nil => exact absurd hx hne
    | cons _ _ => rfl
  · unfold holdsProgram
    rw [Sketch.focusAt_at hf]

/-- FillReference.Certified fills pass both of the materializer's address checks.

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: a step of D9 (`materialize_refFree`), the second half of the proposed claim
   `workspace-fill-agreement` (role compatibility); consumer: `materialize_refFree`.
3. Reach: any list of fills, each `FillReference.Certified` against one base and one application.
4. What it does not establish: that the materializer accepts them (D9 does, on reference-free
   fills at incomparable addresses).
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem certified_passes_checks {s : Sketch} {app : SigApp} {fs : List (List Nat × NativeEff)}
    (hcert : ∀ x ∈ fs, FillReference.Certified s app x) :
    fs.any (fun x => x.1.isEmpty) = false ∧ fs.any (fun x => !holdsProgram s x.1) = false := by
  refine ⟨List.any_eq_false.mpr fun x hx h => ?_, List.any_eq_false.mpr fun x hx h => ?_⟩
  · have h' : x.1.isEmpty = true := h
    rw [(holdsProgram_of_certified (hcert x hx)).1] at h'
    exact Bool.false_ne_true h'
  · have h' : (!holdsProgram s x.1) = true := h
    rw [(holdsProgram_of_certified (hcert x hx)).2] at h'
    exact Bool.false_ne_true h'

/-- **D6: the materializer reads a set**: two lists with the same members, neither with a located
conflict, FillReference.materialize alike, whatever their order and repeats.

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: the first half of the proposed claim `workspace-fill-agreement` (role compatibility).
   No proof consumes it since `FillSet.materializeSketch` and `FillSet.materializeDoc` were
   removed: `FillSet.publish_eq_materialize` reads the materializer through D9, which orders the
   set itself. It carries that agreement from a set's entries to any conflict-free list with the
   same members.
3. Reach: any two conflict-free fill lists `fs` and `gs` with the same members over one `app` and
   `base`.
4. What it does not establish: that `FillReference.materialize` succeeds (D9 establishes acceptance on
   reference-free fills).
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem materialize_congr {app : SigApp} {base : Sketch} {fs gs : List (List Nat × NativeEff)}
    (hmem : ∀ x, x ∈ fs ↔ x ∈ gs) (hf : FillReference.conflictAt fs = none) (hg : FillReference.conflictAt gs = none) :
    FillReference.materialize app base fs = FillReference.materialize app base gs := by
  unfold FillReference.materialize
  rw [any_eq_of_mem_iff hmem (fun x => x.1.isEmpty), any_eq_of_mem_iff hmem (fun x => !holdsProgram base x.1),
    hf, hg, ordered_congr hmem (conflictFree_of_conflictAt hf)]

/-! ## D8 and D9: reference-free fills keep a reference-free program, so the materializer accepts them -/

/-- **D8: a fill keeps a program free of references** when the filling holds none.

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: step D8 of the proposed claim `workspace-fill-agreement` (role compatibility);
   consumer: `refSites_applyFills_nil` and `materialize_refFree` (D9).
3. Reach: any reference-free program `prog`, replacement path `path`, and reference-free filling `q`.
4. What it does not establish: merges that introduce or break layer references (`refMerge` control).
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem refSites_replaceAt_nil {prog prog' q : NativeEff} {path : List Nat}
    (h : (Node.eff prog).replaceAt path (.eff q) = some (.eff prog'))
    (hp : prog.refSites [] = []) (hq : q.refSites [] = []) : prog'.refSites [] = [] := by
  cases hl : prog'.refSites [] with
  | nil => rfl
  | cons x xs =>
    exfalso
    have hx : x ∈ prog'.refSites [] := by
      rw [hl]
      exact List.mem_cons_self
    have hat := at_of_mem_refSites hx
    rcases Path.prefix_cases x.1 path with ⟨r, hr⟩ | ⟨i, r, hr⟩ | ⟨c, i, j, a, b, hij, ha, hb⟩
    · rw [hr, Node.at_replaceAt_below h r] at hat
      have hmem := mem_refSites_of_at hat
      rw [hq] at hmem
      cases hmem
    · have hbelow := Node.at_replaceAt_below h []
      rw [hr, List.append_nil, Node.at_append, hat, Option.bind_some, Node.at_ref_cons] at hbelow
      cases hbelow
    · have hsame := Node.at_replaceAt_disjoint c b a (hb ▸ h) hij
      rw [← ha, hat] at hsame
      have hmem := mem_refSites_of_at hsame.symm
      rw [hp] at hmem
      cases hmem

/-- Applying reference-free fills keeps a sketch free of references. -/
theorem refSites_applyFills_nil :
    ∀ (fills : List (List Nat × NativeEff)) (s s' : Sketch), s.program.refSites [] = [] →
      (∀ x ∈ fills, x.2.refSites [] = []) → applyFills s fills = some s' →
      s'.program.refSites [] = []
  | [], s, s', hs, _, h => by
    cases h
    exact hs
  | (p, q) :: rest, s, s', hs, hf, h => by
    simp only [applyFills] at h
    cases hfill : s.fillAt p q with
    | none =>
      rw [hfill] at h
      cases h
    | some s1 =>
      rw [hfill, Option.bind_some] at h
      obtain ⟨p', hrep, rfl⟩ := Sketch.fillAt_some hfill
      exact refSites_applyFills_nil rest _ s' (refSites_replaceAt_nil hrep hs
        (hf (p, q) List.mem_cons_self)) (fun x hx => hf x (List.mem_cons_of_mem _ hx)) h

/-- **D9: the materializer accepts a conflict-free set of certified reference-free fills at
incomparable addresses, and keeps the base's type.**

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: the second half of the proposed claim `workspace-fill-agreement` (role compatibility);
   consumer: `FillSet.publish_eq_materialize`.
3. Reach: one checked reference-free base sketch `base`, and a conflict-free set `fs` of certified
   reference-free fills at pairwise `Incomparable` addresses.
4. What it does not establish: fills that change a type (control D), omissions (control omissions),
   nested addresses (control nested), or merges through layer references (control refMerge).
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem materialize_refFree {app : SigApp} {T : EffTy} {base : Sketch}
    {fs : List (List Nat × NativeEff)} (hs : base.check app = .ok T)
    (hcf : FillReference.conflictAt fs = none)
    (hinc : ∀ x ∈ fs, ∀ y ∈ fs, x.1 ≠ y.1 → Incomparable x.1 y.1)
    (hcert : ∀ x ∈ fs, FillReference.Certified base app x) (hbase : base.program.refSites [] = [])
    (hfills : ∀ x ∈ fs, x.2.refSites [] = []) :
    ∃ s', FillReference.materialize app base fs = .ok s' ∧ s'.check app = .ok T := by
  obtain ⟨s', happ, hs'⟩ := ordered_compose hs hinc hcert
  have hnil := refSites_applyFills_nil _ base s' hbase
    (fun x hx => hfills x (ordered_mem hx)) happ
  have hfault : s'.program.firstRefFault = none := by
    unfold Eff.firstRefFault
    rw [hnil]
    rfl
  have hexp : s'.expand = s' := by
    unfold Sketch.expand
    rw [expandRefs_eq_self_of_refSites_nil s'.program hnil]
  refine ⟨s', ?_, hs'⟩
  obtain ⟨hroot, hknown⟩ := certified_passes_checks hcert
  unfold FillReference.materialize
  rw [hroot, hknown, hcf]
  dsimp only
  rw [happ]
  dsimp only
  have hsrc : s'.sourceCheck app = .ok T := by
    unfold Sketch.sourceCheck
    rw [hfault, hexp, hs']
  rw [hsrc]

/-! ## Construction invariant of `FillSet` (§7.4, F1) -/


/-!
Placement: initial-algebras-folds, typed-replacement and source-session-coherent, R14.
Question: the new add_wf construction claim and the reference-fragment connectors below.
Reach: the sealed anchor, exact source-session feed, non-root edits, and explicit reference-free premises.
Exclusions: arbitrary reference composition, admission, progress, and native execution.
Consumers: ordered publication, the tool's pending set, and the D1-D9 reference battery.
-/
open _root_.Effect4.Program.Check

def FeedCertified (s : SourceSession) (x : List Nat × NativeEff) : Prop :=
  x.1 ≠ [] ∧ ∃ next step,
    (s.feed Oracle.uncached .keepExact (.fill x.1 x.2)).value = .ok (next,step)

/-! ## The kept-exact feed against the retired certification -/

/-- A sketch with no layer reference is its own expansion. A step of `kept-fill-reference` and of
`pending-fill-publication`. Its consumers are `SourceSession.expandedEditAgrees_refFree`,
`kept_eq_certified` and `FillSet.publish_eq_materialize`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Sketch.expand_of_refSites_nil {s : Sketch} (h : s.program.refSites [] = []) :
    s.expand = s := by
  unfold Sketch.expand
  rw [expandRefs_eq_self_of_refSites_nil s.program h]

/-- **With no layer reference in the base or in the filling, the expansion moves only at the
edited address.** A step of `kept-fill-reference`. Its consumer is `kept_eq_certified`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem SourceSession.expandedEditAgrees_refFree {s : SourceSession} {p : List Nat}
    {q p' : NativeEff} (hb : s.sketch.program.refSites [] = []) (hc : p'.refSites [] = [])
    (hrep : (Node.eff s.sketch.program).replaceAt p (.eff q) = some (.eff p')) :
    s.expandedEditAgrees { s.sketch with program := p' } (.fill p q) = true := by
  have hce : ({ s.sketch with program := p' } : Sketch).expand = { s.sketch with program := p' } :=
    Sketch.expand_of_refSites_nil hc
  have hat : (Node.eff p').at_ p = some (.eff q) := (Node.replaceAt_spec hrep).1
  unfold SourceSession.expandedEditAgrees
  rw [hce, Sketch.expand_of_refSites_nil hb]
  simp only [Edit.expanded, hat, Sketch.edit, Sketch.fillAt_of_replaceAt hrep, Option.map_some]
  exact decide_eq_true trivial

/-- **The part key of a reference-free filling at a typed focus** checks the filling in the
focus's environment, at the filled sketch's signature data there. A step of
`kept-fill-reference`. Its consumer is `kept_eq_certified`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem SourceSession.partKey_refFree {s : SourceSession} {i : Nat} {rest : List Nat}
    {q p' : NativeEff} {focus : Focus NativeOp} (hc : p'.refSites [] = [])
    (hrep : (Node.eff s.sketch.program).replaceAt (i :: rest) (.eff q) = some (.eff p'))
    (hfocus : s.focusAt (i :: rest) = some focus) :
    s.candidatePartKey (i :: rest) { s.sketch with program := p' } =
      some (.part (sketchSigData { s.sketch with program := p' } s.app (i :: rest)) focus.env q) := by
  have hce : ({ s.sketch with program := p' } : Sketch).expand = { s.sketch with program := p' } :=
    Sketch.expand_of_refSites_nil hc
  have hat : (Node.eff p').at_ (i :: rest) = some (.eff q) := (Node.replaceAt_spec hrep).1
  unfold SourceSession.candidatePartKey
  rw [hce, hfocus]
  simp only [hat]

/-- **On a coherent session with no layer reference, the kept-exact feed accepts a
reference-free filling below the root exactly where the retired certification does.** The feed
reads the focus off the table, which is the sketch's (coherence), and checks the filling as a
part, which is the check at the address moved to its own root (`Checker.check_rebase`); the
expansion moves only at the address, so the feed splices. The pointer of
`kept-fill-reference`. Not established: fillings or bases with layer references, omissions, or
the root. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem kept_eq_certified (s : SourceSession) (hc : s.Coherent)
    (p : List Nat) (q : NativeEff) (hp : p ≠ [])
    (hb : s.sketch.program.refSites [] = []) (hq : q.refSites [] = []) :
    FeedCertified s (p,q) ↔ FillReference.certifiedB s.sketch s.app p q = true := by
  obtain ⟨i, rest, rfl⟩ := List.exists_cons_of_ne_nil hp
  have hsig : ∀ p' : NativeEff, (Node.eff s.sketch.program).replaceAt (i :: rest) (.eff q) =
      some (.eff p') → (s.sketch.program.partAt (s.app.withHoles s.sketch.holes).signature []
        (i :: rest)).isSome = true →
      (sketchSigData { s.sketch with program := p' } s.app (i :: rest)).signature =
        s.sketch.sigAt s.app (i :: rest) := by
    intro p' hrep hpart
    have hpart' := partAt_sig_replaceAt (sig := (s.app.withHoles s.sketch.holes).signature) hrep
      (i :: rest)
    rw [sketchSigData_signature]
    · exact sigAt_fillAt hp (Sketch.fillAt_of_replaceAt hrep) (i :: rest)
    · rw [← Option.isSome_map (f := fun pr : Part NativeOp × List Nat => pr.1.sig)]
      show ((p'.partAt (s.app.withHoles s.sketch.holes).signature [] (i :: rest)).map _).isSome = _
      rw [hpart', Option.isSome_map]
      exact hpart
  constructor
  · rintro ⟨-, next, step, h⟩
    obtain ⟨old, c, key, focus, hat, hedit, hfocus, hkey, hres, -, -⟩ :=
      SourceSession.feed_keepExact_ok (e := .fill (i :: rest) q) hp h
    dsimp only [Edit.path] at hat hfocus hkey hedit
    obtain ⟨-, q0, hf⟩ := SourceSession.focusAt_typed hc hfocus hp
    rw [Sketch.expand_of_refSites_nil hb] at hf
    obtain ⟨p', hrep, rfl⟩ := Sketch.fillAt_some hedit
    have hc' := refSites_replaceAt_nil hrep hb hq
    rw [SourceSession.partKey_refFree hc' hrep hfocus, Option.some.injEq] at hkey
    subst hkey
    have hpart : (s.sketch.program.partAt (s.app.withHoles s.sketch.holes).signature []
        (i :: rest)).isSome = true := by
      have hfp : programFocusAt (s.app.withHoles s.sketch.holes).signature [] s.sketch.program
          (i :: rest) = some ⟨q0, focus.env, focus.ty⟩ := hf
      unfold programFocusAt at hfp
      obtain ⟨pr, hpr, -⟩ := Option.bind_eq_some_iff.mp hfp
      rw [hpr]
      rfl
    have hchk : Checker.check (s.sketch.sigAt s.app (i :: rest)) focus.env [] q = .ok focus.ty := by
      rw [← hsig p' hrep hpart]
      have h1 : (run (.part (sketchSigData { s.sketch with program := p' } s.app (i :: rest))
          focus.env q)).result = Checker.check (sketchSigData { s.sketch with program := p' } s.app
            (i :: rest)).signature focus.env [] q := by
        show (Annotate.check _ _ [] q).2 = _
        rw [Annotate.check_eq]
      rw [← h1]
      exact hres
    have hchk' : Checker.check (s.sketch.sigAt s.app (i :: rest)) focus.env (i :: rest) q =
        .ok focus.ty := by
      have hr := Checker.check_rebase (s.sketch.sigAt s.app (i :: rest)) (i :: rest) focus.env [] q
      rw [List.append_nil, hchk] at hr
      exact hr
    unfold FillReference.certifiedB
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and, hf, hchk', decide_true]
  · intro hcert
    unfold FillReference.certifiedB at hcert
    simp only [List.isEmpty_cons, Bool.not_false, Bool.true_and] at hcert
    cases hf : s.sketch.focusAt s.app (i :: rest) with
    | none =>
      rw [hf] at hcert
      cases hcert
    | some f =>
      rw [hf, decide_eq_true_eq] at hcert
      have hat := Sketch.focusAt_at hf
      obtain ⟨p', hrep⟩ := Node.replaceAt_eff q hat
      have hc' := refSites_replaceAt_nil hrep hb hq
      have hmem : (i :: rest) ∈ Node.addresses (.eff s.sketch.program) :=
        (mem_addresses_iff _ _).mpr (by rw [hat]; rfl)
      have htyped : Table.typedAt s.table (i :: rest) = some (f.env, f.ty) := by
        rw [SourceSession.table_eq hc, Sketch.sourceTable_typedAt s.sketch s.app hmem hp,
          Sketch.expand_of_refSites_nil hb]
        exact Table.typedAt_table_of_focusAt hf hp
      have hfocus : s.focusAt (i :: rest) = some ⟨f.program, f.env, f.ty⟩ := by
        unfold SourceSession.focusAt
        rw [hat, htyped]
      have hpart : (s.sketch.program.partAt (s.app.withHoles s.sketch.holes).signature []
          (i :: rest)).isSome = true := by
        have hfp : programFocusAt (s.app.withHoles s.sketch.holes).signature [] s.sketch.program
            (i :: rest) = some f := hf
        unfold programFocusAt at hfp
        obtain ⟨pr, hpr, -⟩ := Option.bind_eq_some_iff.mp hfp
        rw [hpr]
        rfl
      have hchk : Checker.check (s.sketch.sigAt s.app (i :: rest)) f.env [] q = .ok f.ty := by
        have hr := Checker.check_rebase (s.sketch.sigAt s.app (i :: rest)) (i :: rest) f.env [] q
        rw [List.append_nil, hcert] at hr
        cases hq0 : Checker.check (s.sketch.sigAt s.app (i :: rest)) f.env [] q with
        | error r =>
          rw [hq0] at hr
          cases hr
        | ok t =>
          rw [hq0] at hr
          cases hr
          rfl
      have hres : (run (.part (sketchSigData { s.sketch with program := p' } s.app (i :: rest))
          f.env q)).result = .ok f.ty := by
        show (Annotate.check _ _ [] q).2 = _
        rw [Annotate.check_eq, hsig p' hrep hpart]
        exact hchk
      exact ⟨hp, _, _, SourceSession.feed_keepExact_of (o := Oracle.uncached) hp hat
        (Sketch.fillAt_of_replaceAt hrep) hfocus (SourceSession.partKey_refFree hc' hrep hfocus)
        hres (SourceSession.expandedEditAgrees_refFree hb hc' hrep)⟩

/-! ## The construction invariant -/

namespace FillSetInternal

/-- **One submission either leaves the entries, or records a new filling** that names no
recorded address, is incomparable with every recorded address, and that the anchor's
`keepExact` feed accepts. A step of `pending-fill-construction`. Its consumer is
`addEntry_inv`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem addEntry_cases (o : Oracle) (anchor : SourceSession)
    (entries : List (List Nat × NativeEff)) (p : List Nat) (q : NativeEff) :
    (addEntry o anchor entries p q).value.1 = entries ∨
      ((addEntry o anchor entries p q).value.1 = (p, q) :: entries ∧ p ≠ [] ∧
        (∀ x ∈ entries, x.1 ≠ p) ∧ (∀ x ∈ entries, incomparableB p x.1 = true) ∧
        ∃ r, (anchor.feed o .keepExact (.fill p q)).value = .ok r) := by
  unfold addEntry
  split
  · exact Or.inl rfl
  · rename_i hp
    split
    · exact Or.inl rfl
    · split
      · split <;> exact Or.inl rfl
      · rename_i hfind
        split
        · exact Or.inl rfl
        · rename_i hover
          rw [Checked.bind_value]
          cases hr : (anchor.feed o .keepExact (.fill p q)).value with
          | error why => exact Or.inl rfl
          | ok r =>
            refine Or.inr ⟨rfl, ?_, ?_, ?_, r, rfl⟩
            · intro h0
              subst h0
              exact hp rfl
            · intro x hx hxp
              have := List.find?_eq_none.mp hfind x hx
              rw [decide_eq_true hxp] at this
              exact this rfl
            · intro x hx
              have := List.find?_eq_none.mp hover x hx
              cases hb : incomparableB p x.1 with
              | true => rfl
              | false =>
                rw [hb] at this
                exact (this rfl).elim

/-- **The construction invariant** of the entries at one anchor: no conflict, distinct addresses
incomparable, every entry accepted by the anchor's kept-exact feed. -/
def Inv (anchor : SourceSession) (entries : List (List Nat × NativeEff)) : Prop :=
  ConflictFree entries ∧ (∀ x ∈ entries, ∀ y ∈ entries, x.1 ≠ y.1 → Incomparable x.1 y.1) ∧
    ∀ x ∈ entries, FeedCertified anchor x

/-- One submission keeps the construction invariant. A step of `pending-fill-construction`. Its
consumer is `addRaw_inv`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem addEntry_inv (anchor : SourceSession) (entries : List (List Nat × NativeEff))
    (p : List Nat) (q : NativeEff) (h : Inv anchor entries) :
    Inv anchor ((addEntry Oracle.uncached anchor entries p q).value.1) := by
  rcases addEntry_cases Oracle.uncached anchor entries p q with he | ⟨he, hp, hnot, hinc, r, hr⟩
  · rw [he]
    exact h
  · rw [he]
    obtain ⟨hcf, hpw, hcert⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy hxy
      rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact absurd hxy.symm (hnot _ hy')
      · exact absurd hxy (hnot _ hx')
      · exact hcf x hx' y hy' hxy
    · intro x hx y hy hne
      rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
      · exact absurd rfl hne
      · exact incomparable_of_incomparableB (hinc _ hy')
      · exact (incomparable_of_incomparableB (hinc _ hx')).symm
      · exact hpw x hx' y hy' hne
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨hp, r.1, r.2, hr⟩
      · exact hcert x hx'

/-- Every uncached submission fold keeps the construction invariant. A step of
`pending-fill-construction`. Its consumer is `FillSet.wellFormed`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem addRaw_inv (anchor : SourceSession) : ∀ (subs : List (List Nat × NativeEff))
    (entries : List (List Nat × NativeEff)), Inv anchor entries →
    Inv anchor (subs.foldl (fun entries x =>
      (addEntry Oracle.uncached anchor entries x.1 x.2).value.1) entries)
  | [], _, h => h
  | x :: xs, entries, h => addRaw_inv anchor xs _ (addEntry_inv anchor entries x.1 x.2 h)

end FillSetInternal

namespace FillSet
structure WellFormed (fs : FillSet) : Prop where
  conflictFree : ConflictFree fs.entries
  incomparable : ∀ x ∈ fs.entries, ∀ y ∈ fs.entries, x.1 ≠ y.1 → Incomparable x.1 y.1
  certified : ∀ x ∈ fs.entries, FeedCertified fs.source x

/-- **Every sealed set is well formed**: its entries are an uncached submission fold
(`FillSet.constructed`), which keeps the construction invariant. A step of
`pending-fill-construction`. Its consumers are `add_wf` and `publish_eq_materialize`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem wellFormed (fs : FillSet) : fs.WellFormed := by
  obtain ⟨subs, hs⟩ := fs.constructed
  have h := FillSetInternal.addRaw_inv fs.source subs []
    ⟨(fun _ hx => nomatch hx), (fun _ hx => nomatch hx), (fun _ hx => nomatch hx)⟩
  have hfold : subs.foldl (fun entries x =>
      (FillSetInternal.addEntry Oracle.uncached fs.source entries x.1 x.2).value.1) [] =
      FillSetInternal.addRaw fs.source subs := rfl
  rw [hfold, hs] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- **Every set that `add` answers is well formed**: conflict-free, its distinct addresses
incomparable, each entry accepted by the anchor's kept-exact feed. The pointer of
`pending-fill-construction`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem add_wf (o : Oracle) (fs : FillSet) (submissions : List (List Nat × NativeEff)) :
    ((fs.add o submissions).value.1).WellFormed :=
  wellFormed _

/-- The filling of a commit item that stands at an address: its address and its program. -/
def fillOf : Place × Change → Option (List Nat × NativeEff)
  | (.at_ p _, .fill q) => some (p, q)
  | _ => none

/-- **A kept-exact batch of fillings at addresses applies them in order**: the fresh session's
sketch is the sketch with every filling applied. A step of `pending-fill-publication`. Its
consumer is `publish_eq_materialize`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem batch_keepExact_fills {o : Oracle} : ∀ (items : List (Place × Change))
    (s : SourceSession) (idx : Nat) (fresh : DocInternal.Fresh),
    (∀ it ∈ items, ∃ p e q, it = (Place.at_ p e, Change.fill q)) →
    (DocInternal.batch o .keepExact s idx items).value = .ok fresh →
    applyFills s.sketch (items.filterMap fillOf) = some fresh.session.sketch
  | [], s, idx, fresh, _, h => by
    simp only [DocInternal.batch, Checked.pure_value] at h
    cases h
    rfl
  | it :: rest, s, idx, fresh, hitems, h => by
    obtain ⟨p, e, q, rfl⟩ := hitems it List.mem_cons_self
    unfold DocInternal.batch at h
    split at h
    · cases h
    · rename_i path old hres
      have hpath : path = p := by
        simp only [Place.resolve] at hres
        split at hres
        · cases hres
          rfl
        · cases hres
      subst hpath
      simp only [DocInternal.editOf] at h
      rw [Checked.bind_value] at h
      split at h
      · cases h
      · rename_i next step hfeed
        rw [Checked.bind_value] at h
        split at h
        · cases h
        · rename_i later hlater
          rw [Checked.pure_value] at h
          cases h
          have hedit := SourceSession.feed_keepExact_sketch hfeed
          have ih := batch_keepExact_fills rest next (idx + 1) later
            (fun it' hit' => hitems it' (List.mem_cons_of_mem _ hit')) hlater
          simp only [List.filterMap_cons, fillOf, applyFills]
          exact Option.bind_eq_some_iff.mpr ⟨next.sketch, hedit, ih⟩

/-- A `filterMap` that answers each member with itself is the list. A step of
`pending-fill-publication`. Its consumer is `publication_ok`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem filterMap_eq_self_of {α : Type} {f : α → Option α} :
    ∀ (l : List α), (∀ x ∈ l, f x = some x) → l.filterMap f = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons_some (h a List.mem_cons_self),
      filterMap_eq_self_of l (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- **A publication is one kept-exact commit of the pending fillings**, each at its address,
where the base holds a program at every entry's address. A step of `pending-fill-publication`.
Its consumer is `publish_eq_materialize`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem publication_ok {fs : FillSet} {action : DocAction}
    (hhold : ∀ x ∈ fs.entries, holdsProgram fs.base x.1 = true)
    (h : fs.publication = .ok action) :
    ∃ items, action = .commit items .keepExact ∧ items.filterMap fillOf = fs.pending ∧
      ∀ it ∈ items, ∃ p e q, it = (Place.at_ p e, Change.fill q) := by
  unfold FillSet.publication at h
  split at h
  · cases h
  · cases h
    refine ⟨_, rfl, ?_, ?_⟩
    · rw [List.filterMap_filterMap]
      refine filterMap_eq_self_of _ fun x hx => ?_
      have hheld := hhold x (ordered_mem hx)
      unfold holdsProgram at hheld
      split at hheld
      · rename_i e hat
        simp only [hat, Option.bind_some, fillOf]
      · cases hheld
    · intro it hit
      obtain ⟨⟨p, q⟩, -, hx⟩ := List.mem_filterMap.mp hit
      dsimp only at hx
      split at hx
      · rename_i e hat
        cases hx
        exact ⟨p, e, q, rfl⟩
      · cases hx

/-- A materialization that answers applies the fills in the base's address order. A step of
`pending-fill-publication`. Its consumer is `publish_eq_materialize`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem materialize_ok_apply {app : SigApp} {base s' : Sketch} {fs : List (List Nat × NativeEff)}
    (h : FillReference.materialize app base fs = .ok s') :
    applyFills base (ordered base fs) = some s' := by
  unfold FillReference.materialize at h
  split at h
  · cases h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i s'' happ
        split at h
        · cases h
          exact happ
        · cases h

/-- **A successful publication agrees with the retired materialization** at its exact coherent
anchor, under a positive base and no layer reference: every entry is certified against the base
(`kept_eq_certified`), so the materializer accepts the set in the base's order
(`materialize_refFree`, D9), and the publication's batch applies the same fills in the same order
(`batch_keepExact_fills`). The pointer of `pending-fill-publication`. Not established: layer
references, omissions, or a moved document, which the step refuses `stale`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem publish_eq_materialize {o : Oracle} {fs : FillSet} {d next : Doc} {action : DocAction}
    {receipt : Receipt} {T : EffTy} (ha : fs.anchor = d.snap) (hs : fs.source = d.session)
    (hc : d.session.Coherent) (hpositive : fs.base.sourceCheck fs.app = .ok T)
    (hb : fs.base.program.refSites [] = [])
    (hq : ∀ x ∈ fs.entries, x.2.refSites [] = [])
    (hpublication : fs.publication = .ok action)
    (hstep : (d.step o fs.anchor action).value = .ok (next,receipt)) :
    FillReference.materialize fs.app fs.base fs.entries = .ok next.session.sketch := by
  have wf := wellFormed fs
  have hcoh : fs.source.Coherent := by
    rw [hs]
    exact hc
  have hcert : ∀ x ∈ fs.entries, FillReference.Certified fs.base fs.app x := by
    intro x hx
    have hfc := wf.certified x hx
    exact certified_of_certifiedB
      ((kept_eq_certified fs.source hcoh x.1 x.2 hfc.1 hb (hq x hx)).mp hfc)
  have hhold : ∀ x ∈ fs.entries, holdsProgram fs.base x.1 = true :=
    fun x hx => (holdsProgram_of_certified (hcert x hx)).2
  have hfault : fs.base.program.firstRefFault = none := by
    unfold Eff.firstRefFault
    rw [hb]
    rfl
  have hcheck : fs.base.check fs.app = .ok T := by
    have h1 := hpositive
    unfold Sketch.sourceCheck at h1
    rw [hfault, Sketch.expand_of_refSites_nil hb] at h1
    exact h1
  obtain ⟨s', hmat, -⟩ := materialize_refFree hcheck
    (conflictAt_eq_none_of_conflictFree wf.conflictFree) wf.incomparable hcert hb hq
  have happly := materialize_ok_apply hmat
  rw [ha] at hstep
  obtain ⟨-, fresh, happ, -, -, hsession, -⟩ := Doc.step_ok hstep
  obtain ⟨items, rfl, hfill, hform⟩ := publication_ok hhold hpublication
  cases items with
  | nil =>
    simp only [DocInternal.apply, Checked.pure_value] at happ
    cases happ
  | cons it rest =>
    have h2 := batch_keepExact_fills (it :: rest) d.runtime.session 0 fresh hform happ
    rw [hfill] at h2
    have hbase : d.runtime.session.sketch = fs.base := by
      show d.session.sketch = fs.source.sketch
      rw [hs]
    rw [hbase] at h2
    unfold FillSet.pending at h2
    rw [happly, Option.some.injEq] at h2
    rw [hmat, hsession, ← h2]
end FillSet
end Effect4.Program
