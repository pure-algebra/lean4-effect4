import Tools.Session
import Effect4.Laws.Program.Typing.PartsTable
import Effect4.Laws.Program.AddressMove
import Effect4.Laws.Program.Edit
import Effect4.Laws.Program.SourceTable
import Effect4.Laws.Program.PathFold
import Effect4.Laws.Program.ReferenceTyping

/-!
# Probe D: fixed-base fills compose

Slice D of the authoring review. Fills certified against one base sketch, at pairwise
incomparable addresses below the root, each of the focus's exact type, apply in any order and
keep the base's type. The proof composes existing laws through four new steps:

| Step | Statement | From |
| --- | --- | --- |
| D1 | `Table.typedAt_splice_outside`: a splice keeps the typed entry of an address outside it | list reasoning over `Table.splice` |
| D2 | `at_replaceAt_incomparable`: a replacement keeps the node at an incomparable address | `Path.prefix_cases`, `Node.at_replaceAt_disjoint` |
| D3 | `sigAt_fillAt`: a fill below the root keeps the signature of every address | `Node.replaceAt_cons_isBlock`, `Node.replaceAt_defs_main`, `Node.replaceAt_defs_body`, `Node.replaceAt_effs_head`, `Node.replaceAt_effs_tail`, `Node.replaceAt_layers_cons`, `defs_replaceAt_layers` |
| D4 | `focusAt_fill_incomparable`: an exact fill keeps the focus at an incomparable address | `Sketch.table_fill`, `Table.typedAt_table`, `Table.typedAt_table_of_focusAt`, `Sketch.focusAt_at`, D1, D2 |
| D5 | `fills_compose`: the claim | `Sketch.check_fill_kept`, D3, D4 |

Placement of D5: concept `initial-algebras-folds`, property `typed-replacement`; question: the
proposed claim `workspace-fill-agreement` (role compatibility), whose pointer D5 would be. D1 to
D4 are its steps. Reach: the raw sketch check (`Sketch.check`) at one application and one fixed
hole table; fills of the exact focus type; no layer reference is read by the raw check. It does
not establish source admission through references (control refMerge), fills that change a type
(control D), omissions (control omissions), nested addresses (control nested) or equal bytes
across orders (the materializer applies its fills in one canonical order). Consumer: slice D's
materializer, which promises that certified independent fills never conflict at merge.
Requirement R14.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace ProofScout.D

open Effect4 Effect4.Program Effect4.Store
open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing (HasTy check_complete check_sound effTy_sound)

/-- Two addresses are incomparable: neither stands at or below the other. -/
def Incomparable (a b : List Nat) : Prop := Table.under a b = false ∧ Table.under b a = false

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

/-- **D1.** -/
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

/-- **D2.** -/
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

/-- **D3.** -/
theorem sigAt_fillAt {s s' : Sketch} {app : SigApp} {p : List Nat} {q : NativeEff}
    (hp : p ≠ []) (h : s.fillAt p q = some s') (path : List Nat) :
    s'.sigAt app path = s.sigAt app path := by
  obtain ⟨p', hrep, rfl⟩ := Sketch.fillAt_some h
  obtain ⟨i, rest, rfl⟩ := List.exists_cons_of_ne_nil hp
  unfold Sketch.sigAt
  dsimp only
  rw [partAt_sig_replaceAt hrep path]

/-! ## D4: an exact fill keeps the focus at an incomparable address -/

/-- **D4.** -/
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

/-- Apply fills in order. -/
def applyFills (s : Sketch) : List (List Nat × NativeEff) → Option Sketch
  | [] => some s
  | (p, q) :: rest => (s.fillAt p q).bind fun s' => applyFills s' rest

/-- A fill certified against a sketch: below the root, at a focus that the sketch answers, typed
at the focus's type in its environment at the address's signature. -/
def Certified (s : Sketch) (app : SigApp) (x : List Nat × NativeEff) : Prop :=
  x.1 ≠ [] ∧ ∃ f, s.focusAt app x.1 = some f ∧ HasTy (s.sigAt app x.1) f.env x.2 f.ty

/-- **D5: fills certified against one base, at pairwise incomparable addresses, all apply, and
the result keeps the base's type.** -/
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

/-! ## The materializer: the base's address order, so the result is a function of the set -/

/-- The filling a set of fills gives an address: the first member at the address. -/
def lookup (fs : List (List Nat × NativeEff)) (a : List Nat) : Option NativeEff :=
  (fs.find? fun x => decide (x.1 = a)).map (·.2)

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

/-- A list of addresses with each address once, the last occurrence kept. -/
def uniq : List (List Nat) → List (List Nat)
  | [] => []
  | a :: l => if a ∈ l then uniq l else a :: uniq l

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

/-- The fills of a set, in the base's address order, each address once. -/
def ordered (base : Sketch) (fs : List (List Nat × NativeEff)) : List (List Nat × NativeEff) :=
  (uniq (Node.addresses (.eff base.program))).filterMap fun a => (lookup fs a).map fun q => (a, q)

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

/-- **The materializer's fills compose**: a conflict-free set of certified fills whose distinct
addresses are incomparable applies in the base's address order, and keeps the base's type. -/
theorem ordered_compose {app : SigApp} {T : EffTy} {base : Sketch}
    {fs : List (List Nat × NativeEff)} (hs : base.check app = .ok T)
    (hinc : ∀ x ∈ fs, ∀ y ∈ fs, x.1 ≠ y.1 → Incomparable x.1 y.1)
    (hcert : ∀ x ∈ fs, Certified base app x) :
    ∃ s', applyFills base (ordered base fs) = some s' ∧ s'.check app = .ok T := by
  refine fills_compose _ base hs ?_ (fun x hx => hcert x (ordered_mem hx))
  exact List.Pairwise.imp_of_mem (fun hx hy hne => hinc _ (ordered_mem hx) _ (ordered_mem hy) hne)
    (ordered_pairwise base fs)

/-- Why a fill set does not materialize. -/
inductive MaterializeRefusal
  | conflict (path : List Nat)
  | notApplicable
  | refused (why : TypeRefusal)

/-- The first address with two different fillings. -/
def conflictAt (fs : List (List Nat × NativeEff)) : Option (List Nat) :=
  (fs.find? fun x => fs.any fun y => decide (y.1 = x.1) && decide (y.2 ≠ x.2)).map (·.1)

/-- **Materialize**: refuse a conflict, apply the fills in the base's address order, and check
the result through its references. -/
def materialize (app : SigApp) (base : Sketch) (fs : List (List Nat × NativeEff)) :
    Except MaterializeRefusal Sketch :=
  match conflictAt fs with
  | some p => .error (.conflict p)
  | none =>
    match applyFills base (ordered base fs) with
    | none => .error .notApplicable
    | some s' =>
      match s'.sourceCheck app with
      | .ok _ => .ok s'
      | .error why => .error (.refused why)

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

/-- **The materializer reads a set**: two lists with the same members, neither with a located
conflict, materialize alike, whatever their order and repeats. -/
theorem materialize_congr {app : SigApp} {base : Sketch} {fs gs : List (List Nat × NativeEff)}
    (hmem : ∀ x, x ∈ fs ↔ x ∈ gs) (hf : conflictAt fs = none) (hg : conflictAt gs = none) :
    materialize app base fs = materialize app base gs := by
  unfold materialize
  rw [hf, hg, ordered_congr hmem (conflictFree_of_conflictAt hf)]

/-! ## Reference-free fills keep a reference-free program, so the materializer accepts them -/

/-- **A fill keeps a program free of references** when the filling holds none. -/
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

/-- **The materializer accepts a conflict-free set of certified reference-free fills at
incomparable addresses, and keeps the base's type.** -/
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
  unfold materialize
  rw [hcf]
  dsimp only
  rw [happ]
  dsimp only
  have hsrc : s'.sourceCheck app = .ok T := by
    unfold Sketch.sourceCheck
    rw [hfault, hexp, hs']
  rw [hsrc]

/-! ## Controls -/

def nat1 : NativeEff := .succeed (.lit (.nat 1))
def nat2 : NativeEff := .succeed (.lit (.nat 2))
def nat7 : NativeEff := .succeed (.lit (.nat 7))
def strA : NativeEff := .succeed (.lit (.str "a"))
def natTy : EffTy := .pure .nat
def keyA : ServiceKey := ⟨⟨127⟩, ⟨127⟩⟩
def keyB : ServiceKey := ⟨⟨128⟩, ⟨128⟩⟩
def appA : SigApp := { services := [(keyA, .string)] }
def appB : SigApp := { services := [(keyB, .nat)] }

def isOk {ε α : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

-- Green: two certified exact fills at incomparable holes materialize, in either order of
-- submission, with a repeat, to one sketch at the base's type.
def base2 : Sketch :=
  { program := .bind (Sketch.hole {} 0) (Sketch.hole {} 1),
    holes := [Row.hole "a" .nat, Row.hole "b" .nat] }
#guard base2.check {} = .ok natTy
def fillsLR : List (List Nat × NativeEff) := [([0], nat7), ([1], .succeed (.var 0))]
def fillsRL : List (List Nat × NativeEff) := [([1], .succeed (.var 0)), ([0], nat7), ([0], nat7)]
#guard ordered base2 fillsLR = ordered base2 fillsRL
#guard (materialize {} base2 fillsLR).toOption.map (·.program) =
  (materialize {} base2 fillsRL).toOption.map (·.program)
#guard (materialize {} base2 fillsLR).toOption.map (·.check {}) = some (.ok natTy)

-- Green: two different fillings at one address are a located conflict.
def clash : List (List Nat × NativeEff) := [([0], nat7), ([0], nat2), ([1], nat1)]
#guard conflictAt clash = some [0]
#guard (match materialize {} base2 clash with
  | .error (.conflict [0]) => true
  | _ => false)

-- Red: without the conflict check the lookup keeps the first filling, so the order of
-- submission would decide.
#guard lookup clash [0] != lookup clash.reverse [0]

-- Red (the additional review's control D): a fill that changes its focus's type is not
-- certified, and its merge with an independent edit refuses although each keeps the root type.
def baseD : Sketch := { program := .bind nat1 nat2 }
def readsFirst : NativeEff := .provideService keyB (.var 0) nat2
#guard (Checker.check (baseD.sigAt appB [0]) [] [0] strA) != .ok natTy
#guard (applyFills baseD [([0], strA)]).map (·.check appB) = some (.ok natTy)
#guard (applyFills baseD [([1], readsFirst)]).map (·.check appB) = some (.ok natTy)
#guard ((applyFills baseD [([0], strA), ([1], readsFirst)]).map (·.check appB)).map
  (fun r => r.toOption.isNone) = some true

-- Red (source references): each fill is exact and keeps the root type through the references,
-- and together they delete a layer that the other references.
def refBase : Sketch := { program := .bind (.provideLayer (.effect keyA strA) false nat1) nat2 }
def addRef : NativeEff := .provideLayer (.ref [0, 0]) false nat2
#guard (applyFills refBase [([0], nat7)]).map (·.sourceCheck appA) = some (.ok natTy)
#guard (applyFills refBase [([1], addRef)]).map (·.sourceCheck appA) = some (.ok natTy)
#guard (match materialize appA refBase [([0], nat7), ([1], addRef)] with
  | .error (.refused _) => true
  | _ => false)

-- Red (omissions): two omissions from one base append different rows at one ordinal, so the
-- second one's hole reads the first one's row.
def pairBase : Sketch := { program := .bind nat1 (.succeed (.lit (.str "s"))) }
#guard pairBase.check {} = .ok (.pure .string)
def omitL := pairBase.omitAt {} [0] (Row.hole "l" .nat)
def omitR := pairBase.omitAt {} [1] (Row.hole "r" .string)
#guard (omitL.map (·.program)) = some (.bind (Sketch.hole {} 0) (.succeed (.lit (.str "s"))))
#guard (omitR.map (·.program)) = some (.bind nat1 (Sketch.hole {} 0))
def merged (holes : RowTable) : Sketch :=
  { program := .bind (Sketch.hole {} 0) (Sketch.hole {} 0), holes }
-- With the left table the root's type moves from a string to a number ...
#guard (omitL.map fun l => (merged l.holes).check {}) = some (.ok natTy)
-- ... and with the right table the left hole reads the right one's row.
#guard (omitR.bind fun r => ((merged r.holes).focusAt {} [0]).map (·.ty)) = some (.pure .string)

-- Red (nested addresses): an ancestor's fill and a descendant's fill do not commute.
def nested : Sketch := { program := .bind (.bind nat1 nat2) nat7 }
#guard (applyFills nested [([0], nat7), ([0, 1], nat1)]).map (·.program) !=
  (applyFills nested [([0, 1], nat1), ([0], nat7)]).map (·.program)

end ProofScout.D
