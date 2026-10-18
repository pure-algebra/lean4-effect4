import Effect4.Program.Typing.FillSet
import Effect4.Laws.Program.Typing.PartsTable
import Effect4.Laws.Program.AddressMove
import Effect4.Laws.Program.Edit
import Effect4.Laws.Program.SourceTable
import Effect4.Laws.Program.PathFold
import Effect4.Laws.Program.ReferenceTyping

/-!
# Laws.Program.FillSet — fixed-base parallel fills and deterministic materialization

Slice D of `docs/research/2026-10-17-proof-scout/README.md` (§7.4).

* D1 (`Table.typedAt_splice_outside`): a splice keeps the typed entry of an address outside its subtree.
* D2 (`at_replaceAt_incomparable`): a replacement keeps the node at an incomparable address.
* D3 (`sigAt_fillAt`): a fill below the root keeps the signature of every address.
* D4 (`focusAt_fill_incomparable`): an exact fill keeps the focus at an incomparable address.
* D5 (`fills_compose`): certified fills at pairwise incomparable addresses all apply and keep the
  base's type.
* D6 (`materialize_congr`): two lists with the same members and no located conflict materialize
  alike, via `lookup_congr`, `ordered_congr`, and `conflictFree_of_conflictAt`.
* D7 (`ordered_compose`): the materializer's order satisfies D5's premises.
* D8 (`refSites_replaceAt_nil`): a reference-free fill keeps a program free of references.
* D9 (`materialize_refFree`): the materializer accepts a conflict-free set of certified
  reference-free fills through the source check, at the base's type.
* Construction invariant (`FillSet.WellFormed`, `FillSet.empty_wf`, `FillSet.addOne_wf`,
  `FillSet.add_wf`, `FillSet.conflictAt_eq_none`): every `FillSet` built from `FillSet.empty` by
  `FillSet.add` is `ConflictFree`, pairwise `Incomparable`, and `Certified` at its base.
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

/-! ## D3: a fill below the root keeps the signature of every address -/

/-- An edit inside a spine of bodies keeps each body's signature. -/
theorem bodyAt_sig_replaceAt (sig : Signature NativeOp) (q : NativeEff) :
    ∀ (r : List Nat) (decls : List DefDecl) (bodies bodies' : Effs NativeOp),
      (Node.effs bodies).replaceAt r (.eff q) = some (.effs bodies') →
      ∀ path, (Part.bodyAt sig decls bodies' path).map (·.1.sig) =
        (Part.bodyAt sig decls bodies path).map (·.1.sig)
  | [], _, _, _, h, _ => by
    simp only [Node.replaceAt] at h
    split at h <;> cases h
  | 0 :: _, _, .nil, _, h, _ => by
    simp only [Node.replaceAt, Node.child, Option.bind_none, reduceCtorEq] at h
  | 0 :: _, decls, .cons b bs, _, h, path => by
    obtain ⟨b', -, rfl⟩ := Node.replaceAt_effs_head h
    match decls, path with
    | [], _ => rfl
    | _ :: _, [] => rfl
    | _ :: _, 0 :: _ => rfl
    | _ :: _, 1 :: _ => rfl
    | _ :: _, (_ + 2) :: _ => rfl
  | 1 :: _, _, .nil, _, h, _ => by
    simp only [Node.replaceAt, Node.child, Option.bind_none, reduceCtorEq] at h
  | 1 :: r, decls, .cons b bs, _, h, path => by
    obtain ⟨bs', hr, rfl⟩ := Node.replaceAt_effs_tail h
    match decls, path with
    | [], _ => rfl
    | _ :: _, [] => rfl
    | _ :: _, 0 :: _ => rfl
    | _ :: ds, 1 :: rest => exact bodyAt_sig_replaceAt sig q r ds bs bs' hr rest
    | _ :: _, (_ + 2) :: _ => rfl
  | (_ + 2) :: _, _, .nil, _, h, _ => by
    simp only [Node.replaceAt, Node.child, Option.bind_none, reduceCtorEq] at h
  | (_ + 2) :: _, _, .cons _ _, _, h, _ => by
    simp only [Node.replaceAt, Node.child, Option.bind_none, reduceCtorEq] at h

/-- A replacement below the root keeps the signature of every part. -/
theorem partAt_sig_replaceAt {sig : Signature NativeOp} {p p' q : NativeEff} {i : Nat}
    {rest : List Nat} (h : (Node.eff p).replaceAt (i :: rest) (.eff q) = some (.eff p'))
    (path : List Nat) :
    (p'.partAt sig [] path).map (·.1.sig) = (p.partAt sig [] path).map (·.1.sig) := by
  cases hb : p.isBlock
  · have hb' : p'.isBlock = false := by
      have := Node.replaceAt_cons_isBlock h
      simp only [Node.isBlock] at this
      rw [this, hb]
    rw [Eff.partAt_plain hb, Eff.partAt_plain hb']
    rfl
  · obtain ⟨decls, bodies, main, layers, rfl⟩ := Eff.eq_defs_of_isBlock hb
    match i, h with
    | 0, h =>
      obtain ⟨bodies', hr, rfl⟩ := Node.replaceAt_defs_body h
      unfold Eff.partAt
      match path, layers with
      | [], _ => rfl
      | 0 :: r, _ => exact bodyAt_sig_replaceAt _ q rest decls bodies bodies' hr r
      | 1 :: _, _ => rfl
      | 2 :: _, .nil => rfl
      | 2 :: _, .cons _ _ => rfl
      | (_ + 3) :: _, _ => rfl
    | 1, h =>
      obtain ⟨main', -, rfl⟩ := Node.replaceAt_defs_main h
      unfold Eff.partAt
      match path, layers with
      | [], _ => rfl
      | 0 :: _, _ => rfl
      | 1 :: _, _ => rfl
      | 2 :: _, .nil => rfl
      | 2 :: _, .cons _ _ => rfl
      | (_ + 3) :: _, _ => rfl
    | 2, h =>
      rw [defs_replaceAt_layers] at h
      cases hr : (Node.layers layers).replaceAt rest (.eff q) with
      | none =>
        rw [hr] at h
        cases h
      | some n =>
        rw [hr, Option.bind_some] at h
        match n, h with
        | .layers ls', h =>
          simp only [Option.some.injEq, Node.eff.injEq] at h
          subst h
          cases layers with
          | nil =>
            cases rest with
            | nil =>
              simp only [Node.replaceAt] at hr
              split at hr <;> cases hr
            | cons j t =>
              simp only [Node.replaceAt, Node.child, Option.bind_none, reduceCtorEq] at hr
          | cons hd tl =>
            obtain ⟨h', t', rfl⟩ := Node.replaceAt_layers_cons hr
            unfold Eff.partAt
            match path with
            | [] => rfl
            | 0 :: _ => rfl
            | 1 :: _ => rfl
            | 2 :: _ => rfl
            | (_ + 3) :: _ => rfl
    | k + 3, h =>
      simp only [Node.replaceAt, Node.child, Option.bind_none, reduceCtorEq] at h

/-- **D3: a fill below the root keeps the signature of every address.**

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: step D3 of the proposed claim `workspace-fill-agreement` (role compatibility);
   consumer: `fills_compose` (D5).
3. Reach: any sketch `s`, application `app`, non-empty path `p ≠ []`, filling `q`, and target
   address `path`.
4. What it does not establish: root replacement (`p = []`), which can change `defs` declarations.
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem sigAt_fillAt {s s' : Sketch} {app : SigApp} {p : List Nat} {q : NativeEff}
    (hp : p ≠ []) (h : s.fillAt p q = some s') (path : List Nat) :
    s'.sigAt app path = s.sigAt app path := by
  obtain ⟨p', hrep, rfl⟩ := Sketch.fillAt_some h
  obtain ⟨i, rest, rfl⟩ := List.exists_cons_of_ne_nil hp
  unfold Sketch.sigAt
  dsimp only
  rw [partAt_sig_replaceAt hrep path]

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

/-- A fill certified against a sketch: below the root, at a focus that the sketch answers, typed
at the focus's type in its environment at the address's signature. -/
def Certified (s : Sketch) (app : SigApp) (x : List Nat × NativeEff) : Prop :=
  x.1 ≠ [] ∧ ∃ f, s.focusAt app x.1 = some f ∧ HasTy (s.sigAt app x.1) f.env x.2 f.ty

/-- `certifiedB` soundness: when `certifiedB s app p q = true`, `(p, q)` is `Certified s app`. -/
theorem certified_of_certifiedB {s : Sketch} {app : SigApp} {p : List Nat} {q : NativeEff}
    (h : certifiedB s app p q = true) : Certified s app (p, q) := by
  unfold certifiedB at h
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
3. Reach: one checked base sketch `s`, a list of fills pairwise `Incomparable` and each `Certified`
   against `s` and `app`.
4. What it does not establish: source admission through layer references (`Sketch.sourceCheck`),
   which `materialize_refFree` (D9) and `materialize` cover.
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem fills_compose {app : SigApp} {T : EffTy} :
    ∀ (fills : List (List Nat × NativeEff)) (s : Sketch), s.check app = .ok T →
      fills.Pairwise (fun a b => Incomparable a.1 b.1) →
      (∀ x ∈ fills, Certified s app x) →
      ∃ s', applyFills s fills = some s' ∧ s'.check app = .ok T
  | [], s, hs, _, _ => ⟨s, rfl, hs⟩
  | (p, q) :: rest, s, hs, hpw, hcert => by
    obtain ⟨hp, f, hf, hq⟩ := hcert (p, q) List.mem_cons_self
    obtain ⟨p', hrep⟩ := Node.replaceAt_eff q (Sketch.focusAt_at hf)
    have hfill := Sketch.fillAt_of_replaceAt hrep
    have hs1 := Sketch.check_fill_kept hs hf hq hrep
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpw
    have hcert' : ∀ x ∈ rest, Certified { s with program := p' } app x := by
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
    (hcert : ∀ x ∈ fs, Certified base app x) :
    ∃ s', applyFills base (ordered base fs) = some s' ∧ s'.check app = .ok T := by
  refine fills_compose _ base hs ?_ (fun x hx => hcert x (ordered_mem hx))
  exact List.Pairwise.imp_of_mem (fun hx hy hne => hinc _ (ordered_mem hx) _ (ordered_mem hy) hne)
    (ordered_pairwise base fs)

/-- A set with no located conflict is conflict-free. -/
theorem conflictFree_of_conflictAt {fs : List (List Nat × NativeEff)} (h : conflictAt fs = none) :
    ConflictFree fs := by
  intro x hx y hy hxy
  unfold conflictAt at h
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

/-- Converse of `conflictFree_of_conflictAt`: a `ConflictFree` list has `conflictAt fs = none`. -/
theorem conflictAt_eq_none_of_conflictFree {fs : List (List Nat × NativeEff)}
    (hcf : ConflictFree fs) : conflictAt fs = none := by
  unfold conflictAt
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

`materialize` refuses a root fill and a fill where the base holds no program, before it orders the
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
3. Reach: any fill `Certified` against a sketch and an application.
4. What it does not establish: that the fill applies beside other fills (D5 does).
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem holdsProgram_of_certified {s : Sketch} {app : SigApp} {x : List Nat × NativeEff}
    (h : Certified s app x) : x.1.isEmpty = false ∧ holdsProgram s x.1 = true := by
  obtain ⟨hne, f, hf, -⟩ := h
  refine ⟨?_, ?_⟩
  · cases hx : x.1 with
    | nil => exact absurd hx hne
    | cons _ _ => rfl
  · unfold holdsProgram
    rw [Sketch.focusAt_at hf]

/-- Certified fills pass both of the materializer's address checks.

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: a step of D9 (`materialize_refFree`), the second half of the proposed claim
   `workspace-fill-agreement` (role compatibility); consumer: `materialize_refFree`.
3. Reach: any list of fills, each `Certified` against one base and one application.
4. What it does not establish: that the materializer accepts them (D9 does, on reference-free
   fills at incomparable addresses).
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem certified_passes_checks {s : Sketch} {app : SigApp} {fs : List (List Nat × NativeEff)}
    (hcert : ∀ x ∈ fs, Certified s app x) :
    fs.any (fun x => x.1.isEmpty) = false ∧ fs.any (fun x => !holdsProgram s x.1) = false := by
  refine ⟨List.any_eq_false.mpr fun x hx h => ?_, List.any_eq_false.mpr fun x hx h => ?_⟩
  · have h' : x.1.isEmpty = true := h
    rw [(holdsProgram_of_certified (hcert x hx)).1] at h'
    exact Bool.false_ne_true h'
  · have h' : (!holdsProgram s x.1) = true := h
    rw [(holdsProgram_of_certified (hcert x hx)).2] at h'
    exact Bool.false_ne_true h'

/-- **D6: the materializer reads a set**: two lists with the same members, neither with a located
conflict, materialize alike, whatever their order and repeats.

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: the first half of the proposed claim `workspace-fill-agreement` (role compatibility);
   consumer: `FillSet.materializeSketch` and `FillSet.materializeDoc`.
3. Reach: any two conflict-free fill lists `fs` and `gs` with the same members over one `app` and
   `base`.
4. What it does not establish: that `materialize` succeeds (D9 establishes acceptance on
   reference-free fills).
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem materialize_congr {app : SigApp} {base : Sketch} {fs gs : List (List Nat × NativeEff)}
    (hmem : ∀ x, x ∈ fs ↔ x ∈ gs) (hf : conflictAt fs = none) (hg : conflictAt gs = none) :
    materialize app base fs = materialize app base gs := by
  unfold materialize
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
   consumer: `FillSet.materializeSketch` and `FillSet.materializeDoc`.
3. Reach: one checked reference-free base sketch `base`, and a conflict-free set `fs` of certified
   reference-free fills at pairwise `Incomparable` addresses.
4. What it does not establish: fills that change a type (control D), omissions (control omissions),
   nested addresses (control nested), or merges through layer references (control refMerge).
5. Unlocks: R14 (`workspace-fill-agreement`). -/
theorem materialize_refFree {app : SigApp} {T : EffTy} {base : Sketch}
    {fs : List (List Nat × NativeEff)} (hs : base.check app = .ok T)
    (hcf : conflictAt fs = none)
    (hinc : ∀ x ∈ fs, ∀ y ∈ fs, x.1 ≠ y.1 → Incomparable x.1 y.1)
    (hcert : ∀ x ∈ fs, Certified base app x) (hbase : base.program.refSites [] = [])
    (hfills : ∀ x ∈ fs, x.2.refSites [] = []) :
    ∃ s', materialize app base fs = .ok s' ∧ s'.check app = .ok T := by
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
  unfold materialize
  rw [hroot, hknown, hcf]
  dsimp only
  rw [happ]
  dsimp only
  have hsrc : s'.sourceCheck app = .ok T := by
    unfold Sketch.sourceCheck
    rw [hfault, hexp, hs']
  rw [hsrc]

/-! ## Construction invariant of `FillSet` (§7.4, F1) -/

namespace FillSet

/-- **The construction invariant of a `FillSet`**: its entries are `ConflictFree`, pairwise
`Incomparable` at distinct addresses, and every entry is `Certified` at `fs.base` and `fs.app`. -/
structure WellFormed (fs : FillSet) : Prop where
  conflictFree : ConflictFree fs.entries
  incomparable : ∀ x ∈ fs.entries, ∀ y ∈ fs.entries, x.1 ≠ y.1 → Incomparable x.1 y.1
  certified : ∀ x ∈ fs.entries, Certified fs.base fs.app x

/-- `FillSet.empty` satisfies `WellFormed`. -/
theorem empty_wf (app : SigApp) (base : Sketch) (doc : DocId := ⟨"", 0⟩) (revision : Nat := 0) :
    (empty app base doc revision).WellFormed :=
  { conflictFree := fun _ hx => by cases hx
    incomparable := fun _ hx => by cases hx
    certified := fun _ hx => by cases hx }

/-- `FillSet.ofDoc` satisfies `WellFormed`. -/
theorem ofDoc_wf (d : Doc) : (ofDoc d).WellFormed :=
  empty_wf d.session.app d.session.sketch d.id d.revision

/-- `FillSet.addOne` preserves `WellFormed`, and keeps `app`, `base`, `doc` and `revision`. -/
theorem addOne_wf {fs : FillSet} (hwf : fs.WellFormed) (p : List Nat) (q : NativeEff) :
    (fs.addOne p q).1.WellFormed ∧
      (fs.addOne p q).1.app = fs.app ∧
      (fs.addOne p q).1.base = fs.base ∧
      (fs.addOne p q).1.doc = fs.doc ∧
      (fs.addOne p q).1.revision = fs.revision := by
  unfold addOne
  cases hp : p.isEmpty with
  | true => exact ⟨hwf, rfl, rfl, rfl, rfl⟩
  | false =>
    rw [if_neg Bool.false_ne_true]
    cases hat : (Node.eff fs.base.program).at_ p with
    | none => exact ⟨hwf, rfl, rfl, rfl, rfl⟩
    | some n =>
      cases n with
      | effs _ | layer _ | layers _ | stmts _ | stmt _ | action _ => exact ⟨hwf, rfl, rfl, rfl, rfl⟩
      | eff sub =>
        dsimp only
        cases hfind1 : fs.entries.find? (fun x => decide (x.1 = p)) with
        | some existing =>
          dsimp only
          cases decide (existing.2 = q) <;> exact ⟨hwf, rfl, rfl, rfl, rfl⟩
        | none =>
          dsimp only
          cases hfind2 : fs.entries.find? (fun x => !incomparableB p x.1) with
          | some over => exact ⟨hwf, rfl, rfl, rfl, rfl⟩
          | none =>
            dsimp only
            cases hcert : certifiedB fs.base fs.app p q with
            | false =>
              rw [if_neg Bool.false_ne_true]
              exact ⟨hwf, rfl, rfl, rfl, rfl⟩
            | true =>
              rw [if_pos rfl]
              refine ⟨⟨?_, ?_, ?_⟩, rfl, rfl, rfl, rfl⟩
              · intro x hx y hy hxy
                have hno_p : ∀ z ∈ fs.entries, z.1 ≠ p := by
                  intro z hz heq
                  have hnone := List.find?_eq_none.mp hfind1 z hz
                  exact hnone (decide_eq_true heq)
                rcases List.mem_cons.mp hx with rfl | hx' <;>
                  rcases List.mem_cons.mp hy with rfl | hy'
                · rfl
                · exact absurd hxy.symm (hno_p y hy')
                · exact absurd hxy (hno_p x hx')
                · exact hwf.conflictFree x hx' y hy' hxy
              · intro x hx y hy hne
                have hinc_p : ∀ z ∈ fs.entries, Incomparable p z.1 := by
                  intro z hz
                  have hnone := List.find?_eq_none.mp hfind2 z hz
                  cases hincB : incomparableB p z.1 with
                  | false =>
                    exfalso
                    apply hnone
                    rw [hincB]
                    rfl
                  | true => exact incomparable_of_incomparableB hincB
                rcases List.mem_cons.mp hx with rfl | hx' <;>
                  rcases List.mem_cons.mp hy with rfl | hy'
                · exact absurd rfl hne
                · exact hinc_p y hy'
                · exact (hinc_p x hx').symm
                · exact hwf.incomparable x hx' y hy' hne
              · intro x hx
                rcases List.mem_cons.mp hx with rfl | hx'
                · exact certified_of_certifiedB hcert
                · exact hwf.certified x hx'

/-- **Construction invariant of `FillSet.add`**: every `FillSet` built from a `WellFormed` `FillSet`
(in particular `FillSet.empty` or `FillSet.ofDoc`) by `FillSet.add` is `ConflictFree`, pairwise
`Incomparable`, and `Certified` at its base.

Placement:
1. Concept: `initial-algebras-folds`; property: `typed-replacement`.
2. Question: the construction invariant for the proposed claim `workspace-fill-agreement`
   (role compatibility); consumer: `FillSet.materializeSketch`, `FillSet.materializeDoc`, and
   `Tools.Session.answer` (`fills.add`, `fills.materialize`).
3. Reach: any `WellFormed` `FillSet` and any batch of submitted fills `items`.
4. What it does not establish: absence of layer-reference faults across fills (checked by
   `Sketch.sourceCheck` in `materialize`).
5. Unlocks: R14 (`workspace-fill-agreement`, F1). -/
theorem add_wf {fs : FillSet} (hwf : fs.WellFormed) :
    ∀ (items : List (List Nat × NativeEff)),
      (fs.add items).1.WellFormed ∧
        (fs.add items).1.app = fs.app ∧
        (fs.add items).1.base = fs.base ∧
        (fs.add items).1.doc = fs.doc ∧
        (fs.add items).1.revision = fs.revision
  | [] => ⟨hwf, rfl, rfl, rfl, rfl⟩
  | (p, q) :: rest => by
    obtain ⟨hwf1, happ1, hbase1, hdoc1, hrev1⟩ := addOne_wf hwf p q
    obtain ⟨hwf2, happ2, hbase2, hdoc2, hrev2⟩ := add_wf hwf1 rest
    exact ⟨hwf2, happ2.trans happ1, hbase2.trans hbase1, hdoc2.trans hdoc1, hrev2.trans hrev1⟩

/-- Every `WellFormed` `FillSet` has `conflictAt fs.entries = none`. -/
theorem conflictAt_eq_none {fs : FillSet} (hwf : fs.WellFormed) :
    conflictAt fs.entries = none :=
  conflictAt_eq_none_of_conflictFree hwf.conflictFree

/-- Every `WellFormed` `FillSet` over a checked reference-free base whose entries are reference-free
materializes via `fs.materializeSketch` to a sketch of the base's type. -/
theorem materializeSketch_refFree {fs : FillSet} {T : EffTy} (hwf : fs.WellFormed)
    (hs : fs.base.check fs.app = .ok T) (hbase : fs.base.program.refSites [] = [])
    (hfills : ∀ x ∈ fs.entries, x.2.refSites [] = []) :
    ∃ s', fs.materializeSketch = .ok s' ∧ s'.check fs.app = .ok T :=
  materialize_refFree hs (conflictAt_eq_none hwf) hwf.incomparable hwf.certified hbase hfills

end FillSet

end Effect4.Program
