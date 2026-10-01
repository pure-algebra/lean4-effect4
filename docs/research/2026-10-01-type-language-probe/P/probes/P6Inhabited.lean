import P5Fits

/-!
# Seat P, question 6: inhabitance at the new forms (type-language probe, 2026-10-01)

Research probe. Seat A's `inhabitedAlg` (`Program/Admission.lean` on `seat/I2`, row 127) over the
copy, with the record (named values, row 165 (a)), optional-field, map and T arms, and its
agreement with membership on the copy's `Fits`: `inhabited τ = true ↔ ∃ w v, Fits w v τ`
(`inhabited_iff_fits`). `int` is inhabited now (T's set: its image extends `nat`'s); `tuple` is
inhabited when every item is; `app` always is (a handle at any target, `fits_handle_fresh`).

**The record arm reads the canonical fields** (Codex's revision-2 finding, `RawDuplicates.lean`):
one Boolean per written field, sorted with the same `canonF` the membership arm uses, so a raw
record with a repeated name answers about the field membership keeps. A record is inhabited
when every canonical field is optional (absent is a member) or has an inhabited type; `record []`
is inhabited (`ctor 0 [list [], list []]`); a map always is (the empty map).

Completeness threads one world through the fields: each required field's witness is built in the
world the previous one grew, and every earlier witness is carried forward by `fits_map` (seat A's
fresh-key construction, n-ary); an optional field is left out of both lists, which the canonical
names' distinctness makes a skip (`namedFit_skip`).
-/

set_option autoImplicit false

namespace ProbeP

open Effect4 Effect4.Machine
open ProbeP.Field ProbeP.Ty
open Effect4.Program.Typed (CauseFits TableExtends tableInsert)

mutual
/-- Inhabitance as a fold (row 127): seat A's arms, plus a record arm on the canonical fields, a
map arm and T's. -/
def inhabited : Ty → Bool
  | .never | .var _ => false
  | .unit | .nat | .int | .string | .bool | .handle _ | .option _ | .list _ | .exitOf _ _
  | .causeOf _ | .fiberOf _ _ | .lit _ | .refOf _ | .deferredOf _ _ | .unknown => true
  | .prod a b => inhabited a && inhabited b
  | .except e a => inhabited e || inhabited a
  | .union l r => inhabited l || inhabited r
  | .record fs => (canonF (inhabitedFields fs)).all fun p => p.2.1 || p.2.2
  | .map _ _ => true
  | .tuple ts => (inhabitedItems ts).all id
  | .app _ _ | .null | .undefined | .number | .bytes => true
/-- The field-list companion: one Boolean per written field. -/
def inhabitedFields : List (String × Bool × Ty) → List (String × Bool × Bool)
  | [] => []
  | (n, o, t) :: rest => (n, o, inhabited t) :: inhabitedFields rest
/-- The item-list companion. -/
def inhabitedItems : List Ty → List Bool
  | [] => []
  | t :: rest => inhabited t :: inhabitedItems rest
end

/-- A field's inhabitance payload. -/
def inhPayload (c : Bool × Ty) : Bool × Bool := (c.1, inhabited c.2)

theorem inhabitedFields_eq_map (fs : List (String × Bool × Ty)) :
    inhabitedFields fs = fs.map (fun q => (q.1, inhPayload q.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [inhabitedFields, ih]
    rfl

/-- The record arm, read through the canonical fields. -/
theorem inhabited_record (fs : List (String × Bool × Ty)) :
    inhabited (.record fs) = (canonF fs).all fun q => q.2.1 || inhabited q.2.2 := by
  rw [inhabited, inhabitedFields_eq_map, canonBy_map, List.all_map]
  rfl

/-- The tuple arm. -/
theorem inhabited_tuple (ts : List Ty) : inhabited (.tuple ts) = ts.all inhabited := by
  have h : ∀ ts : List Ty, inhabitedItems ts = ts.map inhabited := by
    intro ts
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      rw [inhabitedItems, ih]
      rfl
  rw [inhabited, h, List.all_map]
  rfl

/-- The column check (row 127): the designed bottom, or a type with a member. -/
def admitColumn (t : Ty) : Bool := t.normalize == .never || inhabited t

/-! ## Sound: a member makes the fold answer `true` -/

/-- A record value fitting the named read: every field is optional or has a member. -/
theorem namedFit_inhabited (w : World) :
    ∀ (l : List (String × Bool × Ty)) (ns xs : List Val),
      NamedFit (l.map (fun q => (q.1, fitterOf w q.2))) ns xs →
      ∀ q ∈ l, q.2.1 = true ∨ ∃ x, Fits w x q.2.2
  | [], _, _, _ => fun _ hq => absurd hq List.not_mem_nil
  | (n, o, t) :: l, ns, xs, h => by
    intro q hq
    match ns, xs, h with
    | [], [], h =>
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inl h.1
      · exact namedFit_inhabited w l [] [] h.2 q hq
    | [], _ :: _, h => exact h.elim
    | v0 :: _, [], h => cases v0 <;> exact h.elim
    | v0 :: ns, x :: xs, h =>
      cases v0 with
      | str k =>
        simp only [List.map_cons, fitterOf, NamedFit] at h
        by_cases hk : k = n
        · rw [if_pos hk] at h
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inr ⟨x, h.1⟩
          · exact namedFit_inhabited w l ns xs h.2 q hq
        · rw [if_neg hk] at h
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl h.1
          · exact namedFit_inhabited w l (.str k :: ns) (x :: xs) h.2 q hq
      | _ => exact h.elim

/-- A tuple value: every item type has a member. -/
theorem itemsFit_inhabited (w : World) :
    ∀ (ts : List Ty) (xs : List Val), ItemsFit (ts.map (fun t x => Fits w x t)) xs →
      ∀ t ∈ ts, ∃ x, Fits w x t
  | [], _, _ => fun _ ht => absurd ht List.not_mem_nil
  | t :: ts, x :: xs, h => by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨x, h.1⟩
    · exact itemsFit_inhabited w ts xs h.2 u hu
  | _ :: _, [], h => h.elim

/-- **Sound against membership (proved).** arm: one per appended constructor. -/
theorem inhabited_of_fits (w : World) : ∀ (t : Ty) (v : Val), Fits w v t → inhabited t = true := by
  intro t
  induction t with
  | never => intro v h; exact h.elim
  | var _ => intro v h; exact h.elim
  | unit | nat | int | string | bool | handle | option | list | exitOf | causeOf | fiberOf | lit
  | refOf | deferredOf | unknown | map | app | null | undefined | number | bytes => intro _ _; rfl
  | tuple ts ih =>
    intro v h
    cases v
    case list xs =>
      rw [fits_tuple] at h
      rw [inhabited_tuple, List.all_eq_true]
      intro t ht
      obtain ⟨x, hx⟩ := itemsFit_inhabited w ts xs h t ht
      exact ih t ht x hx
    all_goals exact h.elim
  | prod a b iha ihb =>
    intro v h
    simp only [Fits] at h
    split at h
    · show (inhabited a && inhabited b) = true
      rw [iha _ h.1, ihb _ h.2]
      rfl
    · exact h.elim
  | except e a ihe iha =>
    intro v h
    simp only [Fits] at h
    split at h
    · show (inhabited e || inhabited a) = true
      rw [ihe _ h]
      rfl
    · show (inhabited e || inhabited a) = true
      rw [iha _ h, Bool.or_true]
    · exact h.elim
  | union l r ihl ihr =>
    intro v h
    show (inhabited l || inhabited r) = true
    rcases h with h | h
    · rw [ihl v h]
      rfl
    · rw [ihr v h, Bool.or_true]
  | record fs ih =>
    intro v h
    obtain ⟨ns, xs, _, hv⟩ := fits_record_inv w v fs h
    rw [inhabited_record, List.all_eq_true]
    intro q hq
    rcases namedFit_inhabited w (canonF fs) ns xs hv q hq with hopt | ⟨x, hx⟩
    · rw [hopt]
      rfl
    · rw [ih q (mem_canonBy hq) x hx, Bool.or_true]

/-! ## Complete: one world for every handle and every field, by fresh keys -/

/-- Every fiber, deferred and cell key from `n` on is undeclared. -/
structure FreshFrom (w : World) (n : Nat) : Prop where
  fiber : ∀ id : FiberId, n ≤ id.value → w.Γ id = none
  promise : ∀ key : DeferredKey, n ≤ key.index → w.«Π» key = none
  cell : ∀ key : RefKey, n ≤ key.index → w.Ρ key = none

theorem Grows.refl (w : World) : Grows w w :=
  ⟨Effect4.Program.Typed.table_refl _, Effect4.Program.Typed.table_refl _,
    Effect4.Program.Typed.table_refl _, fun _ _ h => h, fun _ h => h, rfl⟩

theorem Grows.trans {a b c : World} (hab : Grows a b) (hbc : Grows b c) : Grows a c :=
  ⟨Effect4.Program.Typed.table_trans _ _ _ hab.fiber hbc.fiber,
    Effect4.Program.Typed.table_trans _ _ _ hab.promise hbc.promise,
    Effect4.Program.Typed.table_trans _ _ _ hab.cell hbc.cell, fun i t h => hbc.alloc i t (hab.alloc i t h),
    fun sc h => hbc.scope sc (hab.scope sc h), hbc.service.trans hab.service⟩

theorem Grows.fits {w w' : World} (h : Grows w w') {t : Ty} {v : Val} (hv : Fits w v t) :
    Fits w' v t := fits_map h t v hv

def World.addFiber (w : World) (id : FiberId) (ty : Ty × Ty) : World := { w with Γ := tableInsert w.Γ id ty }
def World.addRef (w : World) (key : RefKey) (ty : Ty) : World := { w with Ρ := tableInsert w.Ρ key ty }
def World.addPromise (w : World) (key : DeferredKey) (ty : Ty × Ty) : World :=
  { w with «Π» := tableInsert w.«Π» key ty }
def World.allocExternal (w : World) (target : String) : World :=
  { w with allocated := w.allocated ++ [target] }
def World.allocScope (w : World) (sc : Nat) : World :=
  { w with scopeLive := fun j => decide (j = sc) || w.scopeLive j }

theorem FreshFrom.addFiber {w : World} {n : Nat} (h : FreshFrom w n) (ty : Ty × Ty) :
    Grows w (w.addFiber ⟨n⟩ ty) ∧ FreshFrom (w.addFiber ⟨n⟩ ty) (n + 1) := by
  refine ⟨⟨Effect4.Program.Typed.insert_extends _ _ _ (h.fiber ⟨n⟩ (Nat.le_refl n)),
    Effect4.Program.Typed.table_refl _, Effect4.Program.Typed.table_refl _,
    fun _ _ hx => hx, fun _ hs => hs, rfl⟩,
    ⟨fun id hid => ?_, fun key hk => h.promise key (Nat.le_of_succ_le hk),
      fun key hk => h.cell key (Nat.le_of_succ_le hk)⟩⟩
  have hne : id ≠ ⟨n⟩ := fun heq => by
    subst heq
    exact Nat.not_succ_le_self n hid
  show tableInsert w.Γ ⟨n⟩ ty id = none
  rw [Effect4.Program.Typed.insert_other _ _ _ _ hne]
  exact h.fiber id (Nat.le_of_succ_le hid)

theorem FreshFrom.addRef {w : World} {n : Nat} (h : FreshFrom w n) (ty : Ty) :
    Grows w (w.addRef ⟨n⟩ ty) ∧ FreshFrom (w.addRef ⟨n⟩ ty) (n + 1) := by
  refine ⟨⟨Effect4.Program.Typed.table_refl _, Effect4.Program.Typed.table_refl _,
    Effect4.Program.Typed.insert_extends _ _ _ (h.cell ⟨n⟩ (Nat.le_refl n)),
    fun _ _ hx => hx, fun _ hs => hs, rfl⟩, ⟨fun id hid => h.fiber id (Nat.le_of_succ_le hid),
    fun key hk => h.promise key (Nat.le_of_succ_le hk), fun key hk => ?_⟩⟩
  have hne : key ≠ ⟨n⟩ := fun heq => by
    subst heq
    exact Nat.not_succ_le_self n hk
  show tableInsert w.Ρ ⟨n⟩ ty key = none
  rw [Effect4.Program.Typed.insert_other _ _ _ _ hne]
  exact h.cell key (Nat.le_of_succ_le hk)

theorem FreshFrom.addPromise {w : World} {n : Nat} (h : FreshFrom w n) (types : Ty × Ty) :
    Grows w (w.addPromise ⟨n⟩ types) ∧ FreshFrom (w.addPromise ⟨n⟩ types) (n + 1) := by
  refine ⟨⟨Effect4.Program.Typed.table_refl _,
    Effect4.Program.Typed.insert_extends _ _ _ (h.promise ⟨n⟩ (Nat.le_refl n)),
    Effect4.Program.Typed.table_refl _, fun _ _ hx => hx, fun _ hs => hs, rfl⟩,
    ⟨fun id hid => h.fiber id (Nat.le_of_succ_le hid), fun key hk => ?_,
      fun key hk => h.cell key (Nat.le_of_succ_le hk)⟩⟩
  have hne : key ≠ ⟨n⟩ := fun heq => by
    subst heq
    exact Nat.not_succ_le_self n hk
  show tableInsert w.«Π» ⟨n⟩ types key = none
  rw [Effect4.Program.Typed.insert_other _ _ _ _ hne]
  exact h.promise key (Nat.le_of_succ_le hk)

theorem FreshFrom.allocExternal {w : World} {n : Nat} (h : FreshFrom w n) (target : String) :
    Grows w (w.allocExternal target) ∧ FreshFrom (w.allocExternal target) n :=
  ⟨⟨Effect4.Program.Typed.table_refl _, Effect4.Program.Typed.table_refl _,
      Effect4.Program.Typed.table_refl _, Effect4.Program.extends_append _ _, fun _ hs => hs, rfl⟩,
    ⟨h.fiber, h.promise, h.cell⟩⟩

theorem FreshFrom.allocScope {w : World} {n : Nat} (h : FreshFrom w n) (sc : Nat) :
    Grows w (w.allocScope sc) ∧ FreshFrom (w.allocScope sc) n ∧ (w.allocScope sc).scopeLive sc = true :=
  ⟨⟨Effect4.Program.Typed.table_refl _, Effect4.Program.Typed.table_refl _,
      Effect4.Program.Typed.table_refl _, fun _ _ hx => hx,
      fun sc' hs => by
        show (decide (sc' = sc) || w.scopeLive sc') = true
        rw [hs, Bool.or_true], rfl⟩,
    ⟨h.fiber, h.promise, h.cell⟩, by
      show (decide (sc = sc) || w.scopeLive sc) = true
      rw [decide_eq_true rfl, Bool.true_or]⟩

/-- The `handle` former at every target, in a world grown from any world with fresh keys. -/
theorem fits_handle_fresh (target : String) (w : World) (n : Nat) (hn : FreshFrom w n) :
    ∃ (w' : World) (n' : Nat) (v : Val), Grows w w' ∧ FreshFrom w' n' ∧
      Fits w' v (.handle target) := by
  cases hc : Effect4.Program.internalHandleTargets.contains target with
  | false =>
    have ht : Effect4.Program.externalHandleTarget target = true := by
      unfold Effect4.Program.externalHandleTarget
      rw [hc]
      rfl
    obtain ⟨hg, hf⟩ := hn.allocExternal target
    exact ⟨_, n, Val.handle HandleKind.external.byte w.allocated.length, hg, hf,
      ht, List.getElem?_concat_length⟩
  | true =>
    have hm : target ∈ Effect4.Program.internalHandleTargets := List.contains_iff_mem.mp hc
    simp only [Effect4.Program.internalHandleTargets, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · obtain ⟨hg, hf⟩ := hn.addRef .nat
      exact ⟨_, n + 1, Val.handle HandleKind.cell.byte n, hg, hf, rfl, .nat,
        Effect4.Program.Typed.insert_here _ _ _, subN_refl _, subN_refl _⟩
    · obtain ⟨hg, hf⟩ := hn.addPromise (.nat, .nat)
      exact ⟨_, n + 1, Val.handle HandleKind.promise.byte n, hg, hf, rfl, .nat, .nat,
        Effect4.Program.Typed.insert_here _ _ _, ⟨subN_refl _, subN_refl _⟩, ⟨subN_refl _, subN_refl _⟩⟩
    · obtain ⟨hg, hf, hlive⟩ := hn.allocScope 0
      exact ⟨_, n, Val.handle HandleKind.scope.byte 0, hg, hf, rfl, hlive⟩
    · have hkeys : (Val.context emptyCtx).keys = [] := by decide
      refine ⟨w, n, Val.context emptyCtx, Grows.refl w, hn, rfl, emptyCtx,
        ctxImage.ofVal_toVal emptyCtx, ?_, live_of_keys_nil hkeys⟩
      intro key sv sty hget _
      have hnone : emptyCtx.services.getV key = none := rfl
      rw [hnone] at hget
      cases hget

/-- The record case's induction: one world threaded through the canonical fields; an optional
field is left out of both lists, a required one gets a witness built in the grown world. -/
theorem namedFit_fresh (fs : List (String × Bool × Ty))
    (ih : ∀ p ∈ fs, inhabited p.2.2 = true → ∀ (w : World) (n : Nat), FreshFrom w n →
      ∃ (w' : World) (n' : Nat) (v : Val), Grows w w' ∧ FreshFrom w' n' ∧ Fits w' v p.2.2) :
    ∀ (l : List (String × Bool × Ty)), (∀ q ∈ l, q ∈ fs) → (l.map Prod.fst).Nodup →
      (∀ q ∈ l, (q.2.1 || inhabited q.2.2) = true) →
      ∀ (w : World) (n : Nat), FreshFrom w n →
      ∃ (w' : World) (n' : Nat) (ns xs : List Val), Grows w w' ∧ FreshFrom w' n' ∧
        (∀ k, .str k ∈ ns → k ∈ l.map Prod.fst) ∧
        NamedFit (l.map (fun q => (q.1, fitterOf w' q.2))) ns xs
  | [], _, _, _, w, n, hn => ⟨w, n, [], [], Grows.refl w, hn, fun _ h => absurd h List.not_mem_nil, trivial⟩
  | (m, o, t) :: l, hsub, hnd, hall, w, n, hn => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hsub' : ∀ q ∈ l, q ∈ fs := fun q hq => hsub q (List.mem_cons_of_mem _ hq)
    have hall' : ∀ q ∈ l, (q.2.1 || inhabited q.2.2) = true :=
      fun q hq => hall q (List.mem_cons_of_mem _ hq)
    cases o with
    | true =>
      obtain ⟨w', n', ns, xs, hg, hf, hnames, hv⟩ := namedFit_fresh fs ih l hsub' hnd.2 hall' w n hn
      refine ⟨w', n', ns, xs, hg, hf, fun k hk => List.mem_cons_of_mem _ (hnames k hk), ?_⟩
      refine namedFit_skip m true (fun x => Fits w' x t) _ ns xs hv rfl ?_
      intro k hk hkm
      exact hnd.1 (hkm ▸ hnames k hk)
    | false =>
      have hi : inhabited t = true := by
        have := hall (m, false, t) List.mem_cons_self
        simpa only [Bool.false_or] using this
      obtain ⟨w1, n1, x, hg1, hf1, hx⟩ := ih (m, false, t) (hsub _ List.mem_cons_self) hi w n hn
      obtain ⟨w2, n2, ns, xs, hg2, hf2, hnames, hv⟩ := namedFit_fresh fs ih l hsub' hnd.2 hall' w1 n1 hf1
      refine ⟨w2, n2, .str m :: ns, x :: xs, hg1.trans hg2, hf2, ?_, ?_⟩
      · intro k hk
        rcases List.mem_cons.mp hk with hk | hk
        · injection hk with hk
          rw [hk]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hnames k hk)
      · exact (namedFit_cons_eq m false (fun x => Fits w2 x t) _ ns xs x).mpr ⟨hg2.fits hx, hv⟩

/-- The tuple case's induction: one world threaded through the items. -/
theorem itemsFit_fresh (ts : List Ty)
    (ih : ∀ t ∈ ts, inhabited t = true → ∀ (w : World) (n : Nat), FreshFrom w n →
      ∃ (w' : World) (n' : Nat) (v : Val), Grows w w' ∧ FreshFrom w' n' ∧ Fits w' v t) :
    ∀ (l : List Ty), (∀ t ∈ l, t ∈ ts) → (∀ t ∈ l, inhabited t = true) →
      ∀ (w : World) (n : Nat), FreshFrom w n →
      ∃ (w' : World) (n' : Nat) (xs : List Val), Grows w w' ∧ FreshFrom w' n' ∧
        ItemsFit (l.map (fun t x => Fits w' x t)) xs
  | [], _, _, w, n, hn => ⟨w, n, [], Grows.refl w, hn, trivial⟩
  | t :: l, hsub, hall, w, n, hn => by
    obtain ⟨w1, n1, x, hg1, hf1, hx⟩ := ih t (hsub t List.mem_cons_self) (hall t List.mem_cons_self) w n hn
    obtain ⟨w2, n2, xs, hg2, hf2, hv⟩ := itemsFit_fresh ts ih l
      (fun u hu => hsub u (List.mem_cons_of_mem _ hu)) (fun u hu => hall u (List.mem_cons_of_mem _ hu)) w1 n1 hf1
    exact ⟨w2, n2, x :: xs, hg1.trans hg2, hf2, hg2.fits hx, hv⟩

/-- **One world for every handle and every field (proved).** arm: one per appended
constructor. -/
theorem fits_of_inhabited_fresh : ∀ (t : Ty), inhabited t = true → ∀ (w : World) (n : Nat),
    FreshFrom w n → ∃ (w' : World) (n' : Nat) (v : Val), Grows w w' ∧ FreshFrom w' n' ∧ Fits w' v t := by
  intro t
  induction t with
  | never => intro hi; exact Bool.noConfusion hi
  | int => intro _ w n hn; exact ⟨w, n, .nat 0, Grows.refl w, hn, rfl⟩
  | var _ => intro hi; exact Bool.noConfusion hi
  | null => intro _ w n hn; exact ⟨w, n, .none, Grows.refl w, hn, trivial⟩
  | undefined => intro _ w n hn; exact ⟨w, n, .unit, Grows.refl w, hn, trivial⟩
  | number => intro _ w n hn; exact ⟨w, n, .nat 0, Grows.refl w, hn, rfl⟩
  | bytes => intro _ w n hn; exact ⟨w, n, .bytes [], Grows.refl w, hn, trivial⟩
  | app name _ _ => intro _ w n hn; exact fits_handle_fresh name w n hn
  | tuple ts ih =>
    intro hi w n hn
    rw [inhabited_tuple, List.all_eq_true] at hi
    obtain ⟨w', n', xs, hg, hf, hv⟩ := itemsFit_fresh ts (fun t ht => ih t ht) ts (fun _ h => h) hi w n hn
    exact ⟨w', n', .list xs, hg, hf, (fits_tuple w' xs ts).mpr hv⟩
  | unit => intro _ w n hn; exact ⟨w, n, .unit, Grows.refl w, hn, trivial⟩
  | nat => intro _ w n hn; exact ⟨w, n, .nat 0, Grows.refl w, hn, trivial⟩
  | string => intro _ w n hn; exact ⟨w, n, .str "", Grows.refl w, hn, trivial⟩
  | bool => intro _ w n hn; exact ⟨w, n, .bool true, Grows.refl w, hn, trivial⟩
  | lit s => intro _ w n hn; exact ⟨w, n, .str s, Grows.refl w, hn, rfl⟩
  | option _ _ => intro _ w n hn; exact ⟨w, n, .none, Grows.refl w, hn, trivial⟩
  | unknown => intro _ w n hn; exact ⟨w, n, .unit, Grows.refl w, hn, live_of_keys_nil rfl⟩
  | list _ _ =>
    intro _ w n hn
    exact ⟨w, n, .list [], Grows.refl w, hn, fun x hx => nomatch hx⟩
  | exitOf a e _ _ =>
    intro _ w n hn
    refine ⟨w, n, Val.exitErr ⟨[]⟩, Grows.refl w, hn, ?_⟩
    have hc : causeImage.ofVal (causeImage.toVal ⟨[]⟩) = some ⟨[]⟩ := causeImage.ofVal_toVal ⟨[]⟩
    simp only [Fits, hc]
    intro _ hr
    nomatch hr
  | causeOf e _ =>
    intro _ w n hn
    refine ⟨w, n, Val.exitErr ⟨[]⟩, Grows.refl w, hn, ?_⟩
    have hc : Val.cause? (Val.exitErr ⟨[]⟩) = some ⟨[]⟩ := causeImage.ofVal_toVal ⟨[]⟩
    simp only [Fits, hc]
    intro _ hr
    nomatch hr
  | handle target => intro _ w n hn; exact fits_handle_fresh target w n hn
  | fiberOf a e _ _ =>
    intro _ w n hn
    obtain ⟨hg, hf⟩ := hn.addFiber (a, e)
    exact ⟨_, n + 1, Val.fiber ⟨n⟩, hg, hf, _, Effect4.Program.Typed.insert_here _ _ _,
      subN_refl _, subN_refl _⟩
  | refOf t _ =>
    intro _ w n hn
    obtain ⟨hg, hf⟩ := hn.addRef t
    exact ⟨_, n + 1, Val.cell ⟨n⟩, hg, hf, t, Effect4.Program.Typed.insert_here _ _ _,
      subN_refl _, subN_refl _⟩
  | deferredOf a e _ _ =>
    intro _ w n hn
    obtain ⟨hg, hf⟩ := hn.addPromise (a, e)
    exact ⟨_, n + 1, Val.promise ⟨n⟩, hg, hf, a, e, Effect4.Program.Typed.insert_here _ _ _,
      ⟨subN_refl _, subN_refl _⟩, ⟨subN_refl _, subN_refl _⟩⟩
  | prod a b iha ihb =>
    intro hi w n hn
    have hi' : (inhabited a && inhabited b) = true := hi
    obtain ⟨hia, hib⟩ := Bool.and_eq_true_iff.mp hi'
    obtain ⟨w1, n1, va, hg1, hf1, hva⟩ := iha hia w n hn
    obtain ⟨w2, n2, vb, hg2, hf2, hvb⟩ := ihb hib w1 n1 hf1
    exact ⟨w2, n2, .list [va, vb], hg1.trans hg2, hf2, hg2.fits hva, hvb⟩
  | except e a ihe iha =>
    intro hi w n hn
    have hi' : (inhabited e || inhabited a) = true := hi
    rcases Bool.or_eq_true_iff.mp hi' with hie | hia
    · obtain ⟨w', n', v, hg, hf, hv⟩ := ihe hie w n hn
      exact ⟨w', n', .ctor 0 [v], hg, hf, hv⟩
    · obtain ⟨w', n', v, hg, hf, hv⟩ := iha hia w n hn
      exact ⟨w', n', .ctor 1 [v], hg, hf, hv⟩
  | union l r ihl ihr =>
    intro hi w n hn
    have hi' : (inhabited l || inhabited r) = true := hi
    rcases Bool.or_eq_true_iff.mp hi' with hil | hir
    · obtain ⟨w', n', v, hg, hf, hv⟩ := ihl hil w n hn
      exact ⟨w', n', v, hg, hf, Or.inl hv⟩
    · obtain ⟨w', n', v, hg, hf, hv⟩ := ihr hir w n hn
      exact ⟨w', n', v, hg, hf, Or.inr hv⟩
  | record fs ih =>
    intro hi w n hn
    rw [inhabited_record, List.all_eq_true] at hi
    obtain ⟨w', n', ns, xs, hg, hf, _, hv⟩ := namedFit_fresh fs (fun p hp => ih p hp) (canonF fs)
      (fun q hq => mem_canonBy hq) (canonBy_names_nodup fs) hi w n hn
    exact ⟨w', n', .ctor 0 [.list ns, .list xs], hg, hf, (fits_record w' rfl fs).mpr hv⟩
  | map k t _ _ =>
    intro _ w n hn
    exact ⟨w, n, .list [], Grows.refl w, hn, rfl, fun e he => nomatch he⟩

/-- The empty world: no declaration, no allocation, no live scope, no service. -/
def emptyWorld : World := ⟨fun _ => none, fun _ => none, fun _ => none, fun _ => false, [], fun _ => none⟩

theorem emptyWorld_freshFrom : FreshFrom emptyWorld 0 :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **Inhabitance agrees with membership (proved)** on every type of the copy, the new forms
included: row 127's agreement theorem. -/
theorem inhabited_iff_fits (t : Ty) : inhabited t = true ↔ ∃ (w : World) (v : Val), Fits w v t := by
  constructor
  · intro hi
    obtain ⟨w', _, v, _, _, hv⟩ := fits_of_inhabited_fresh t hi emptyWorld 0 emptyWorld_freshFrom
    exact ⟨w', v, hv⟩
  · rintro ⟨w, v, h⟩
    exact inhabited_of_fits w t v h

/-- Closure: normalization keeps inhabitance (seat A's `inhabited_normalize`, at the new forms). -/
theorem inhabited_normalize (t : Ty) : inhabited t.normalize = inhabited t := by
  apply Bool.eq_iff_iff.mpr
  rw [inhabited_iff_fits, inhabited_iff_fits]
  constructor
  · rintro ⟨w, v, h⟩
    exact ⟨w, v, (fits_normalize w t v).mp h⟩
  · rintro ⟨w, v, h⟩
    exact ⟨w, v, (fits_normalize w t v).mpr h⟩

/-! ## The controls -/

/-- A record with a required field at `never`: canonical, not `never`, and empty. -/
def neverField : Ty := .record [("a", false, .never)]

/-- RED CONTROL turned refusal (proved): no member in any world, and the column check refuses it. -/
theorem neverField_empty (w : World) (v : Val) : ¬ Fits w v neverField :=
  fun h => absurd (inhabited_of_fits w _ v h) (by decide)

theorem admitColumn_neverField : admitColumn neverField = false := by decide +kernel

/-- `record []` is inhabited by `ctor 0 [list [], list []]` in every world. -/
theorem emptyRecord_fits (w : World) : Fits w (.ctor 0 [.list [], .list []]) (.record []) := by
  rw [fits_record w rfl]
  trivial

/-- An optional field at `never` does not empty the record: absent (from both lists) is a member. -/
theorem optionalNever_fits (w : World) :
    Fits w (.ctor 0 [.list [], .list []]) (.record [("a", true, .never)]) := by
  rw [fits_record w rfl]
  exact ⟨rfl, trivial⟩

/-- A map at an empty value type is inhabited by the empty map. -/
theorem emptyMap_fits (w : World) : Fits w (.list []) (.map .string .never) :=
  ⟨rfl, fun _ he => nomatch he⟩

/-- RED CONTROL (proved; Codex's `RawDuplicates`, on the copy): a fold over the **written**
fields disagrees with membership at a raw repeated name; the canonical read agrees. -/
def dupRecord : Ty := .record [("a", false, .nat), ("a", false, .never)]

def rawInhabited (fs : List (String × Bool × Ty)) : Bool := fs.all fun q => q.2.1 || inhabited q.2.2

theorem raw_fold_disagrees :
    rawInhabited [("a", false, .nat), ("a", false, .never)] = false ∧
      Fits emptyWorld (.ctor 0 [.list [.str "a"], .list [.nat 1]]) dupRecord ∧
      inhabited dupRecord = true := by
  refine ⟨by decide, ?_, by decide⟩
  have hc : canonF [("a", false, Ty.nat), ("a", false, Ty.never)] = [("a", false, .nat)] := by
    decide +kernel
  rw [dupRecord, fits_record emptyWorld rfl, hc]
  simp only [List.map_cons, List.map_nil, fitterOf]
  rw [namedFit_cons_eq]
  exact ⟨trivial, trivial⟩

#guard inhabited (.record []) && inhabited (.record [("a", true, .never)]) && !inhabited neverField
#guard inhabited (.map .string .never) && admitColumn (.record [("a", false, .nat)])
-- T's arms: `int` inhabited (its image extends `nat`'s), a tuple when every item is
#guard inhabited .int && inhabited .number && inhabited .null && inhabited (.app "Queue.Dequeue" [.never])
#guard inhabited (.tuple [.nat, .string, .bool]) && !inhabited (.tuple [.nat, .never, .bool])
#guard !admitColumn (.prod .never .nat) && !admitColumn (.except .never .never) && admitColumn .never

end ProbeP

#print axioms ProbeP.inhabited_record
#print axioms ProbeP.inhabited_of_fits
#print axioms ProbeP.Grows.refl
#print axioms ProbeP.Grows.trans
#print axioms ProbeP.FreshFrom.addRef
#print axioms ProbeP.FreshFrom.addPromise
#print axioms ProbeP.FreshFrom.allocExternal
#print axioms ProbeP.FreshFrom.allocScope
#print axioms ProbeP.fits_handle_fresh
#print axioms ProbeP.namedFit_fresh
#print axioms ProbeP.itemsFit_fresh
#print axioms ProbeP.fits_of_inhabited_fresh
#print axioms ProbeP.inhabited_iff_fits
#print axioms ProbeP.inhabited_normalize
#print axioms ProbeP.neverField_empty
#print axioms ProbeP.admitColumn_neverField
#print axioms ProbeP.emptyRecord_fits
#print axioms ProbeP.optionalNever_fits
#print axioms ProbeP.emptyMap_fits
#print axioms ProbeP.raw_fold_disagrees
