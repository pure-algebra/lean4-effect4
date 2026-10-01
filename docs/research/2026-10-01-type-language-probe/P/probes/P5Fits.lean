import P4Check
import Effect4.Laws.Program.Typed.Membership

/-!
# Seat P: the membership judgment `Fits` on the copy (type-language probe, 2026-10-01)

Research probe. A copy of `Fits` (`src/Effect4/Laws/Program/Typed/Membership.lean`) in the form
pass I2 leaves it (seat A's row 137: the handle arms compare declarations in the checker's
order `subN`; row 156: the scope arm reads presence), over `ProbeP.Ty`, with the record and map
arms, and the laws question 2 names: `fits_hasTy`, `fits_live`, `fits_map`, `fits_sub` (one arm
each), `fits_normalize` (row 137's law, with the record case), `fits_subN`, the join laws.

The world is a model of `Typed.World` with the tables `Fits` reads, over the copied type
language (`Typed.World`'s tables hold the tree's `Ty`, so they cannot hold the copy's): the
fiber, promise and cell declarations, scope presence, the external allocation table and the
static service table. Everything `Fits` reads that is not a type (`Val.keys`, `HandleKind`,
`causeImage`, `CauseFits`, `Val.context?`, the table order) is the tree's own definition.

**The record arm is the canonical read, as a fold**: one membership predicate per written field
(`fitters`, the field-list companion), sorted by the payload-polymorphic `canonF`, read
positionally against the value's arguments. An optional slot is `none` or `some x`.
-/

set_option autoImplicit false

namespace ProbeP

open Effect4 Effect4.Machine
open ProbeP.Field ProbeP.Ty
open Effect4.Program.Typed (CauseFits causeFits_map TableExtends)

/-! ## The checker's order on the copy (row 137's `Ty.subN`) -/

def subN (a b : Ty) : Bool := sub (normalize a) (normalize b)

theorem subN_refl (t : Ty) : subN t t = true := sub_refl _

theorem subN_trans {a b c : Ty} (hab : subN a b = true) (hbc : subN b c = true) : subN a c = true :=
  sub_trans _ _ _ hab hbc

theorem sub_le_subN {a b : Ty} (h : sub a b = true) : subN a b = true := sub_normalize_of_sub a b h

theorem subN_normalize_left (a b : Ty) : subN a.normalize b = subN a b := by
  unfold subN
  rw [normalize_idem]

theorem subN_normalize_right (a b : Ty) : subN a b.normalize = subN a b := by
  unfold subN
  rw [normalize_idem]

/-! ## The model world and the leaf predicates (copied, over the copy) -/

structure World where
  Γ : FiberId → Option (Ty × Ty)
  «Π» : DeferredKey → Option (Ty × Ty)
  Ρ : RefKey → Option Ty
  scopeLive : Nat → Bool
  allocated : List String
  serviceTy : ServiceKey → Option Ty

/-- Invariance in the checker's order (I2's `Equiv`). -/
def Equiv (declared t : Ty) : Prop := subN declared t = true ∧ subN t declared = true

def RefDeclared (w : World) (key : RefKey) (t : Ty) : Prop :=
  ∃ t', w.Ρ key = some t' ∧ Equiv t' t

def PromiseDeclared (w : World) (key : DeferredKey) (a e : Ty) : Prop :=
  ∃ a' e', w.«Π» key = some (a', e') ∧ Equiv a' a ∧ Equiv e' e

def FiberDeclared (w : World) (id : FiberId) (a e : Ty) : Prop :=
  ∃ fty, w.Γ id = some fty ∧ subN fty.1 a = true ∧ subN fty.2 e = true

def Live (w : World) (v : Val) : Prop :=
  ∀ h ∈ v.keys, match h with
  | .cell key => (w.Ρ key).isSome = true
  | .promise key => (w.«Π» key).isSome = true
  | .fiber id => (w.Γ id).isSome = true
  | _ => True

def HandleFits (w : World) (kind : UInt8) (index : Nat) (target : String) : Prop :=
  match HandleKind.ofByte? kind with
  | some .cell => target = Effect4.Program.NativeOp.refTarget ∧ RefDeclared w ⟨index⟩ .nat
  | some .promise =>
    target = Effect4.Program.NativeOp.deferredTarget ∧ PromiseDeclared w ⟨index⟩ .nat .nat
  | some .scope => target = Effect4.Program.Ty.scopeTarget ∧ w.scopeLive index = true
  | some .external => Effect4.Program.externalHandleTarget target = true ∧
      w.allocated[index]? = some target
  | _ => False

def FlatFits (w : World) (v : Val) : Ty → Prop
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .string => match v with | .str _ => True | _ => False
  | .handle target =>
    match v with | .handle kind index => HandleFits w kind index target | _ => False
  | _ => False

def ServicesFit (w : World) (services : Env.Ctx) : Prop :=
  ∀ key sv sty, services.getV key = some sv → w.serviceTy key = some sty → FlatFits w sv sty

/-! ## The record and map arms' value predicates -/

/-- One slot against one canonical field (`slotHasTy`'s proposition). -/
def slotFits (optional : Bool) (P : Val → Prop) (x : Val) : Prop :=
  match optional with
  | true =>
    match x with
    | .none => True
    | .some y => P y
    | _ => False
  | false => P x

/-- The arguments of a record value against the canonical field predicates, one for one. -/
def FieldsFit : List Val → List (String × Bool × (Val → Prop)) → Prop
  | [], [] => True
  | x :: xs, (_, o, P) :: ps => slotFits o P x ∧ FieldsFit xs ps
  | _, _ => False

/-- The entries of a map value: sorted pairs whose keys and values fit. -/
def EntriesFit (PK PV : Val → Prop) (es : List Val) : Prop :=
  sortedEntries es = true ∧ ∀ e ∈ es, match e with
    | .pair a x => PK a ∧ PV x
    | _ => False

mutual
/-- **The membership judgment**, I2's arms, plus the record arm (the canonical read) and the map
arm. -/
def Fits (w : World) (v : Val) : Ty → Prop
  | .never => False
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .int => False
  | .string => match v with | .str _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .handle target =>
    match v with
    | .handle kind index => HandleFits w kind index target
    | _ => target = Effect4.Program.Ty.contextTarget ∧
        ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w ctx.services ∧ Live w v
  | .option a =>
    match v with
    | .none => True
    | .some x => Fits w x a
    | _ => False
  | .list a =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ∀ id ∈ ids, Fits w (Val.fiber id) a
      | none => False
    | .list values => ∀ x ∈ values, Fits w x a
    | _ => False
  | .prod a b =>
    match v with
    | .list [x, y] => Fits w x a ∧ Fits w y b
    | _ => False
  | .except e a =>
    match v with
    | .ctor 0 [err] => Fits w err e
    | .ctor 1 [val] => Fits w val a
    | _ => False
  | .exitOf a e =>
    match v with
    | Val.exitOk x => Fits w x a
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => CauseFits (fun x => Fits w x e) c
      | none => False
    | _ => False
  | .causeOf e =>
    match Val.cause? v with
    | some c => CauseFits (fun x => Fits w x e) c
    | none => False
  | .fiberOf a e =>
    match v with
    | Value.fiber index => FiberDeclared w ⟨index⟩ a e
    | _ => False
  | .union l r => Fits w v l ∨ Fits w v r
  | .lit s => match v with | .str s' => s' = s | _ => False
  | .refOf t =>
    match v with
    | Value.cell index => RefDeclared w ⟨index⟩ t
    | _ => False
  | .deferredOf a e =>
    match v with
    | Value.promise index => PromiseDeclared w ⟨index⟩ a e
    | _ => False
  | .var _ => False
  | .unknown => Live w v
  | .record fs =>
    match v with
    | .ctor 0 vs => FieldsFit vs (canonF (fitters w fs))
    | _ => False
  | .map k t =>
    match v with
    | .list es => EntriesFit (fun a => Fits w a k) (fun x => Fits w x t) es
    | _ => False
/-- The field-list companion: one membership predicate per written field. -/
def fitters (w : World) : List (String × Bool × Ty) → List (String × Bool × (Val → Prop))
  | [] => []
  | (n, o, t) :: rest => (n, o, fun x => Fits w x t) :: fitters w rest
end

/-- A field's predicate. -/
def fitterOf (w : World) (c : Bool × Ty) : Bool × (Val → Prop) := (c.1, fun x => Fits w x c.2)

theorem fitters_eq_map (w : World) (fs : List (String × Bool × Ty)) :
    fitters w fs = fs.map (fun q => (q.1, fitterOf w q.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [fitters, ih]
    rfl

/-- **The record arm (R3.1)**: a record value is `ctor 0` of its slots, read in canonical order. -/
theorem fits_record (w : World) (vs : List Val) (fs : List (String × Bool × Ty)) :
    Fits w (.ctor 0 vs) (.record fs) ↔
      FieldsFit vs ((canonF fs).map (fun q => (q.1, fitterOf w q.2))) := by
  rw [Fits, fitters_eq_map, canonBy_map]

/-- Nothing else is a record value. -/
theorem fits_record_inv (w : World) (v : Val) (fs : List (String × Bool × Ty))
    (h : Fits w v (.record fs)) : ∃ vs, v = .ctor 0 vs ∧
      FieldsFit vs ((canonF fs).map (fun q => (q.1, fitterOf w q.2))) := by
  cases v
  case ctor i vs =>
    cases i
    case zero => exact ⟨vs, rfl, (fits_record w vs fs).mp h⟩
    case succ n => exact absurd h (by simp only [Fits]; exact not_false)
  all_goals exact absurd h (by simp only [Fits]; exact not_false)

/-! ## Membership implies the executable check -/

theorem slotFits_hasTy {o : Bool} {P : Val → Prop} {c : Val → Bool} (h : ∀ x, P x → c x = true)
    (x : Val) (hx : slotFits o P x) : slotHasTy o c x = true := by
  cases o
  · exact h x hx
  · unfold slotFits at hx
    unfold slotHasTy
    cases x
    case none => rfl
    case some y => exact h y hx
    all_goals exact hx.elim

theorem fieldsFit_hasTy :
    ∀ (vs : List Val) (ps : List (String × Bool × (Val → Prop))) (cs : List (String × Bool × (Val → Bool))),
      ps.map (fun p => (p.1, p.2.1)) = cs.map (fun p => (p.1, p.2.1)) →
      (∀ pc ∈ ps.zip cs, ∀ x, pc.1.2.2 x → pc.2.2.2 x = true) →
      FieldsFit vs ps → fieldsHasTy vs cs = true
  | [], [], [], _, _, _ => rfl
  | x :: xs, (n, o, P) :: ps, (m, p, c) :: cs, hh, hpt, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hh
    obtain ⟨⟨-, hop⟩, hrest⟩ := hh
    simp only [fieldsHasTy, Bool.and_eq_true]
    refine ⟨?_, fieldsFit_hasTy xs ps cs hrest (fun q hq => hpt q (List.mem_cons_of_mem _ hq)) h.2⟩
    rw [← hop]
    exact slotFits_hasTy (hpt ((n, o, P), (m, p, c)) List.mem_cons_self) x h.1
  | [], [], _ :: _, hh, _, _ => nomatch hh
  | [], _ :: _, [], hh, _, _ => nomatch hh
  | [], _ :: _, _ :: _, _, _, h => h.elim
  | _ :: _, [], [], _, _, h => h.elim
  | _ :: _, [], _ :: _, hh, _, _ => nomatch hh
  | _ :: _, _ :: _, [], hh, _, _ => nomatch hh

theorem causeFits_admitsP {member : Val → Prop} {m : Val → Bool}
    (h : ∀ x, member x → m x = true) (c : CauseV) (hc : CauseFits member c) :
    causeAdmitsP m c = true := by
  unfold causeAdmitsP
  rw [List.all_eq_true]
  intro r hr
  have hr' := hc r hr
  match r, hr' with
  | .fail err ann, ⟨v, hv, hm⟩ =>
    show (match Effect4.Program.valOfErr err with | some v => m v | none => false) = true
    rw [hv]
    exact h v hm
  | .die _ _, _ => rfl
  | .interrupt _ _, _ => rfl

/-- A list zipped with itself pairs each element with itself. -/
theorem mem_zip_self {α : Type} : ∀ {l : List α} {a b : α}, (a, b) ∈ l.zip l → a = b
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: xs, a, b, h => by
    rw [List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · simp only [Prod.mk.injEq] at h
      rw [h.1, h.2]
    · exact mem_zip_self h

/-- **Fits implies the shape check**, at the world's allocation table. arm: two. -/
theorem fits_hasTy (w : World) : ∀ (ty : Ty) (v : Val), Fits w v ty → hasTy v ty w.allocated = true := by
  intro ty
  induction ty with
  | never => intro v h; exact h.elim
  | unit =>
    intro v h
    simp only [Fits] at h
    split at h
    · rfl
    · exact h.elim
  | nat =>
    intro v h
    simp only [Fits] at h
    split at h
    · rfl
    · exact h.elim
  | int => intro v h; exact h.elim
  | string =>
    intro v h
    simp only [Fits] at h
    split at h
    · rfl
    · exact h.elim
  | bool =>
    intro v h
    simp only [Fits] at h
    split at h
    · rfl
    · exact h.elim
  | handle target =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i kind index
      simp only [HandleFits] at h
      simp only [hasTy]
      split at h
      · rename_i hk
        simp only [hk]
        exact beq_iff_eq.mpr h.1
      · rename_i hk
        simp only [hk]
        exact beq_iff_eq.mpr h.1
      · rename_i hk
        simp only [hk]
        exact beq_iff_eq.mpr h.1
      · rename_i hk
        simp only [hk]
        exact Bool.and_eq_true_iff.mpr ⟨h.1, beq_iff_eq.mpr h.2⟩
      · exact h.elim
    · obtain ⟨ht, ctx, hctx, _, _⟩ := h
      simp only [hasTy]
      rw [hctx]
      exact Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr ht, rfl⟩
  | option a ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · rfl
    · rename_i x
      simp only [hasTy]
      exact ih x h
    · exact h.elim
  | list a ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        simp only [hasTy, hids]
        exact List.all_eq_true.mpr fun id hid => ih _ (h id hid)
      · exact h.elim
    · rename_i values
      simp only [hasTy]
      exact List.all_eq_true.mpr fun x hx => ih x (h x hx)
    · exact h.elim
  | prod a b iha ihb =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i x y
      simp only [hasTy]
      exact Bool.and_eq_true_iff.mpr ⟨iha x h.1, ihb y h.2⟩
    · exact h.elim
  | except e a ihe iha =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i err
      simp only [hasTy]
      exact ihe err h
    · rename_i val
      simp only [hasTy]
      exact iha val h
    · exact h.elim
  | exitOf a e iha ihe =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i x
      simp only [hasTy]
      exact iha x h
    · rename_i written
      split at h
      · rename_i c hc
        simp only [hasTy, hc]
        exact causeFits_admitsP (fun x hx => ihe x hx) c h
      · exact h.elim
    · exact h.elim
  | causeOf e ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i c hc
      simp only [hasTy, hc]
      exact causeFits_admitsP (fun x hx => ih x hx) c h
    · exact h.elim
  | fiberOf a e _ _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · rfl
    · exact h.elim
  | union l r ihl ihr =>
    intro v h
    simp only [Fits] at h
    simp only [hasTy]
    exact Bool.or_eq_true_iff.mpr (h.imp (ihl v) (ihr v))
  | lit s =>
    intro v h
    simp only [Fits] at h
    split at h
    · simp only [hasTy]
      exact beq_iff_eq.mpr h
    · exact h.elim
  | refOf t _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · rfl
    · exact h.elim
  | deferredOf a e _ _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · rfl
    · exact h.elim
  | var _ => intro v h; exact h.elim
  | unknown => intro v _; rfl
  | record fs ih =>
    intro v h
    obtain ⟨vs, rfl, hv⟩ := fits_record_inv w v fs h
    rw [hasTy_record]
    refine fieldsFit_hasTy vs _ _ ?_ ?_ hv
    · simp only [List.map_map]
      rfl
    · intro pc hpc x hx
      rw [List.zip_map, List.mem_map] at hpc
      obtain ⟨⟨q1, q2⟩, hq, rfl⟩ := hpc
      have heq : q1 = q2 := mem_zip_self hq
      subst heq
      exact ih q1 (mem_canonBy (List.of_mem_zip hq).1) x hx
  | map k t ihk iht =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i es
      simp only [hasTy]
      unfold EntriesFit at h
      unfold entriesHasTy
      rw [Bool.and_eq_true, List.all_eq_true]
      refine ⟨h.1, fun e he => ?_⟩
      have := h.2 e he
      cases e
      case pair a x => exact Bool.and_eq_true_iff.mpr ⟨ihk a this.1, iht x this.2⟩
      all_goals exact this.elim
    · exact h.elim

/-! ## Membership implies declared liveness -/

theorem live_of_keys_nil {w : World} {v : Val} (h : v.keys = []) : Live w v := by
  intro k hk
  rw [h] at hk
  cases hk

theorem live_list {w : World} {values : List Val} (h : ∀ x ∈ values, Live w x) :
    Live w (.list values) := by
  intro k hk
  rw [Val.keys_list, List.mem_flatMap] at hk
  obtain ⟨x, hx, hkx⟩ := hk
  exact h x hx k hkx

theorem live_ctor {w : World} {i : Nat} {args : List Val} (h : ∀ x ∈ args, Live w x) :
    Live w (.ctor i args) := by
  intro k hk
  have hk' : k ∈ Val.keysList args := hk
  rw [Val.keysList_eq_flatMap, List.mem_flatMap] at hk'
  obtain ⟨x, hx, hkx⟩ := hk'
  exact h x hx k hkx

theorem live_ctor_one {w : World} {i : Nat} {x : Val} (h : Live w x) : Live w (.ctor i [x]) :=
  live_ctor fun y hy => by
    rw [List.mem_singleton] at hy
    subst hy
    exact h

theorem live_some {w : World} {x : Val} (h : Live w x) : Live w (.some x) := h

theorem live_pair {w : World} {a x : Val} (ha : Live w a) (hx : Live w x) : Live w (.pair a x) := by
  intro k hk
  have hk' : k ∈ Val.keys a ++ Val.keys x := hk
  rcases List.mem_append.mp hk' with h | h
  · exact ha k h
  · exact hx k h

theorem live_fiber {w : World} {index : Nat} {a e : Ty} (h : FiberDeclared w ⟨index⟩ a e) :
    Live w (Value.fiber index) := by
  obtain ⟨fty, hΓ, _⟩ := h
  intro k hk
  have hk' : k ∈ (Val.fiber ⟨index⟩).keys := hk
  rw [Val.keys_fiber, List.mem_singleton] at hk'
  subst hk'
  show (w.Γ ⟨index⟩).isSome = true
  rw [hΓ]
  rfl

theorem live_cell {w : World} {index : Nat} {t : Ty} (h : RefDeclared w ⟨index⟩ t) :
    Live w (Value.cell index) := by
  obtain ⟨t', hΡ, _⟩ := h
  intro k hk
  have hk' : k ∈ (Val.cell ⟨index⟩).keys := hk
  rw [Val.keys_cell, List.mem_singleton] at hk'
  subst hk'
  show (w.Ρ ⟨index⟩).isSome = true
  rw [hΡ]
  rfl

theorem live_promise {w : World} {index : Nat} {a e : Ty}
    (h : PromiseDeclared w ⟨index⟩ a e) : Live w (Value.promise index) := by
  obtain ⟨a', e', hPi, _⟩ := h
  intro k hk
  have hk' : k ∈ (Val.promise ⟨index⟩).keys := hk
  rw [Val.keys_promise, List.mem_singleton] at hk'
  subst hk'
  show (w.«Π» ⟨index⟩).isSome = true
  rw [hPi]
  rfl

theorem live_handle {w : World} {kind : UInt8} {index : Nat} {target : String}
    (h : HandleFits w kind index target) : Live w (.handle kind index) := by
  simp only [HandleFits] at h
  split at h
  · rename_i hk
    rw [HandleKind.ofByte?_exact hk]
    exact live_cell h.2
  · rename_i hk
    rw [HandleKind.ofByte?_exact hk]
    exact live_promise h.2
  · rename_i hk
    rw [HandleKind.ofByte?_exact hk]
    intro k hk'
    have hk'' : k ∈ (Val.scopeHandle index).keys := hk'
    rw [Val.keys_scopeHandle, List.mem_singleton] at hk''
    subst hk''
    trivial
  · rename_i hk
    rw [HandleKind.ofByte?_exact hk]
    intro k hk'
    have hk'' : k ∈ (Handle.ofCode (7, index)).toList := hk'
    have hcode : Handle.ofCode (7, index) = some (.external index) := rfl
    rw [hcode, Option.toList_some, List.mem_singleton] at hk''
    subst hk''
    trivial
  · exact h.elim

/-- A record value's slots are live when every canonical field's members are. -/
theorem fieldsFit_live {w : World} :
    ∀ (vs : List Val) (ps : List (String × Bool × (Val → Prop))),
      (∀ p ∈ ps, ∀ y, p.2.2 y → Live w y) → FieldsFit vs ps → ∀ x ∈ vs, Live w x
  | [], _, _, _ => fun _ hx => absurd hx List.not_mem_nil
  | x :: xs, (n, o, P) :: ps, hp, h => by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · have hP := hp (n, o, P) List.mem_cons_self
      cases o
      · exact hP z h.1
      · have h1 : slotFits true P z := h.1
        unfold slotFits at h1
        cases z
        case none => exact live_of_keys_nil rfl
        case some y => exact live_some (hP y h1)
        all_goals exact h1.elim
    · exact fieldsFit_live xs ps (fun q hq => hp q (List.mem_cons_of_mem _ hq)) h.2 z hz
  | _ :: _, [], _, h => h.elim

/-- **Membership implies declared liveness.** arm: two. -/
theorem fits_live (w : World) : ∀ (ty : Ty) (v : Val), Fits w v ty → Live w v := by
  intro ty
  induction ty with
  | never => intro v h; exact h.elim
  | unit =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | nat =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | int => intro v h; exact h.elim
  | string =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | bool =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | handle target =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_handle h
    · obtain ⟨_, _, _, _, hl⟩ := h
      exact hl
  | option a ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_of_keys_nil rfl
    · rename_i x
      exact ih x h
    · exact h.elim
  | list a ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        rw [Val.snapshot?_exact hids]
        intro k hk
        rw [Val.keys_fibers, List.mem_map] at hk
        obtain ⟨id, hid, rfl⟩ := hk
        exact ih _ (h id hid) (Handle.fiber id) (by rw [Val.keys_fiber]; exact List.mem_singleton_self _)
      · exact h.elim
    · exact live_list fun x hx => ih x (h x hx)
    · exact h.elim
  | prod a b iha ihb =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i x y
      refine live_list fun z hz => ?_
      rw [List.mem_cons, List.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact iha _ h.1
      · exact ihb _ h.2
    · exact h.elim
  | except e a ihe iha =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_ctor_one (ihe _ h)
    · exact live_ctor_one (iha _ h)
    · exact h.elim
  | exitOf a e iha _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_ctor_one (iha _ h)
    · rename_i written
      split at h
      · rename_i c hc
        refine live_ctor_one (live_of_keys_nil ?_)
        rw [Store.Image.ofVal_exact causeImage hc]
        exact Val.keys_causeImage c
      · exact h.elim
    · exact h.elim
  | causeOf e _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i c hc
      exact live_of_keys_nil (Effect4.Program.Typed.keys_of_cause hc)
    · exact h.elim
  | fiberOf a e _ _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_fiber h
    · exact h.elim
  | union l r ihl ihr =>
    intro v h
    simp only [Fits] at h
    exact h.elim (ihl v) (ihr v)
  | lit s =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | refOf t _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_cell h
    · exact h.elim
  | deferredOf a e _ _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_promise h
    · exact h.elim
  | var _ => intro v h; exact h.elim
  | unknown => intro v h; exact h
  | record fs ih =>
    intro v h
    obtain ⟨vs, rfl, hv⟩ := fits_record_inv w v fs h
    refine live_ctor (fieldsFit_live vs _ ?_ hv)
    intro p hp y hy
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact ih q (mem_canonBy hq) y hy
  | map k t ihk iht =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i es
      refine live_list fun e he => ?_
      have := h.2 e he
      cases e
      case pair a x => exact live_pair (ihk a this.1) (iht x this.2)
      all_goals exact this.elim
    · exact h.elim

/-! ## Membership under world growth -/

/-- A later world as membership reads it (`Grows`'s fields, I2). -/
structure Grows (w1 w2 : World) : Prop where
  fiber : TableExtends w1.Γ w2.Γ
  promise : TableExtends w1.«Π» w2.«Π»
  cell : TableExtends w1.Ρ w2.Ρ
  alloc : Effect4.Program.Extends w1.allocated w2.allocated
  scope : ∀ sc, w1.scopeLive sc = true → w2.scopeLive sc = true
  service : w2.serviceTy = w1.serviceTy

theorem isSome_extends {K A : Type} {t1 t2 : K → Option A} (ht : TableExtends t1 t2) {k : K}
    (h : (t1 k).isSome = true) : (t2 k).isSome = true := by
  cases hs : t1 k with
  | none => rw [hs] at h; cases h
  | some a => rw [ht k a hs]; rfl

section Map
variable {w1 w2 : World} (g : Grows w1 w2)
include g

theorem live_map {v : Val} (h : Live w1 v) : Live w2 v := by
  intro k hk
  have hk' := h k hk
  cases k with
  | cell key => exact isSome_extends g.cell hk'
  | promise key => exact isSome_extends g.promise hk'
  | fiber id => exact isSome_extends g.fiber hk'
  | scope _ => trivial
  | memoMap _ => trivial
  | external _ => trivial

theorem handleFits_map {kind : UInt8} {index : Nat} {target : String}
    (h : HandleFits w1 kind index target) : HandleFits w2 kind index target := by
  simp only [HandleFits] at h ⊢
  split at h
  · obtain ⟨ht, t', hs, hi⟩ := h
    exact ⟨ht, t', g.cell _ t' hs, hi⟩
  · obtain ⟨ht, a', e', hs, ha, he⟩ := h
    exact ⟨ht, a', e', g.promise _ (a', e') hs, ha, he⟩
  · exact ⟨h.1, g.scope index h.2⟩
  · exact ⟨h.1, g.alloc index target h.2⟩
  · exact h.elim

theorem flatFits_map {v : Val} {t : Ty} (h : FlatFits w1 v t) : FlatFits w2 v t := by
  cases t
  case unit => exact h
  case nat => exact h
  case bool => exact h
  case string => exact h
  case handle target =>
    simp only [FlatFits] at h ⊢
    split at h
    · exact handleFits_map g h
    · exact h.elim
  all_goals exact h.elim

theorem servicesFit_map {services : Env.Ctx} (h : ServicesFit w1 services) :
    ServicesFit w2 services :=
  fun key sv sty hget hty => flatFits_map g (h key sv sty hget (g.service ▸ hty))

end Map

theorem fieldsFit_map {ps qs : List (String × Bool × (Val → Prop))}
    (hh : ps.map (fun p => (p.1, p.2.1)) = qs.map (fun p => (p.1, p.2.1)))
    (hpt : ∀ pq ∈ ps.zip qs, ∀ x, pq.1.2.2 x → pq.2.2.2 x) :
    ∀ vs, FieldsFit vs ps → FieldsFit vs qs := by
  induction ps generalizing qs with
  | nil =>
    cases qs with
    | nil => intro vs h; exact h
    | cons q qs => simp only [List.map_nil, List.map_cons, reduceCtorEq] at hh
  | cons p ps ih =>
    cases qs with
    | nil => simp only [List.map_nil, List.map_cons, reduceCtorEq] at hh
    | cons q qs =>
      obtain ⟨n, o, P⟩ := p
      obtain ⟨m, o', Q⟩ := q
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hh
      obtain ⟨⟨-, hoo⟩, hrest⟩ := hh
      intro vs h
      cases vs with
      | nil => exact h.elim
      | cons x xs =>
        refine ⟨?_, ih hrest (fun pq hpq => hpt pq (List.mem_cons_of_mem _ hpq)) xs h.2⟩
        have hPQ := hpt ((n, o, P), (m, o', Q)) List.mem_cons_self
        subst hoo
        cases o
        · exact hPQ x h.1
        · have h1 := h.1
          unfold slotFits at h1 ⊢
          cases x
          case none => trivial
          case some y => exact hPQ y h1
          all_goals exact h1.elim

/-- Membership moves to a later world. arm: two. -/
theorem fits_map {w1 w2 : World} (g : Grows w1 w2) :
    ∀ (ty : Ty) (v : Val), Fits w1 v ty → Fits w2 v ty := by
  intro ty
  induction ty with
  | never => intro v h; exact h.elim
  | unit => intro v h; exact h
  | nat => intro v h; exact h
  | int => intro v h; exact h.elim
  | string => intro v h; exact h
  | bool => intro v h; exact h
  | handle target =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact handleFits_map g h
    · obtain ⟨ht, ctx, hctx, hs, hl⟩ := h
      simp only [Fits]
      exact ⟨ht, ctx, hctx, servicesFit_map g hs, live_map g hl⟩
  | option a ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · trivial
    · rename_i x
      exact ih x h
    · exact h.elim
  | list a ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        simp only [Fits, hids]
        exact fun id hid => ih _ (h id hid)
      · exact h.elim
    · rename_i values
      exact fun x hx => ih x (h x hx)
    · exact h.elim
  | prod a b iha ihb =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact ⟨iha _ h.1, ihb _ h.2⟩
    · exact h.elim
  | except e a ihe iha =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact ihe _ h
    · exact iha _ h
    · exact h.elim
  | exitOf a e iha ihe =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact iha _ h
    · rename_i written
      split at h
      · rename_i c hc
        simp only [Fits, hc]
        exact causeFits_map (fun x hx => ihe x hx) h
      · exact h.elim
    · exact h.elim
  | causeOf e ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i c hc
      simp only [Fits, hc]
      exact causeFits_map (fun x hx => ih x hx) h
    · exact h.elim
  | fiberOf a e _ _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · obtain ⟨fty, hs, ha, he⟩ := h
      exact ⟨fty, g.fiber _ fty hs, ha, he⟩
    · exact h.elim
  | union l r ihl ihr =>
    intro v h
    exact h.imp (ihl v) (ihr v)
  | lit s => intro v h; exact h
  | refOf t _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · obtain ⟨t', hs, hi⟩ := h
      exact ⟨t', g.cell _ t' hs, hi⟩
    · exact h.elim
  | deferredOf a e _ _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · obtain ⟨a', e', hs, ha, he⟩ := h
      exact ⟨a', e', g.promise _ (a', e') hs, ha, he⟩
    · exact h.elim
  | var _ => intro v h; exact h.elim
  | unknown => intro v h; exact live_map g h
  | record fs ih =>
    intro v h
    obtain ⟨vs, rfl, hv⟩ := fits_record_inv w1 v fs h
    rw [fits_record]
    refine fieldsFit_map ?_ ?_ vs hv
    · simp only [List.map_map]
      rfl
    · intro pq hpq x hx
      rw [List.zip_map, List.mem_map] at hpq
      obtain ⟨⟨q1, q2⟩, hq, rfl⟩ := hpq
      have heq : q1 = q2 := mem_zip_self hq
      subst heq
      exact ih q1 (mem_canonBy (List.of_mem_zip hq).1) x hx
  | map k t ihk iht =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i es
      refine ⟨h.1, fun e he => ?_⟩
      have := h.2 e he
      cases e
      case pair a x => exact ⟨ihk a this.1, iht x this.2⟩
      all_goals exact this.elim
    · exact h.elim

/-! ## Membership respects `sub` -/

/-- **Fits is closed under `sub`**, by `fun_induction sub`: two new cases (record, map); the
handle cases are I2's (`subN` through `sub_le_subN`). -/
theorem fits_sub (w : World) {a b : Ty} (hsub : sub a b = true) : ∀ v, Fits w v a → Fits w v b := by
  fun_induction sub a b
  case case1 => intro v h; exact h
  case case2 => intro v h; exact h.elim
  case case3 a1 a2 b _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    exact h.elim (iha h1 v) (ihb h2 v)
  case case4 a b1 b2 _ _ _ iha ihb =>
    intro v h
    exact (Bool.or_eq_true_iff.mp hsub).elim (fun hx => Or.inl (iha hx v h))
      (fun hx => Or.inr (ihb hx v h))
  case case5 => intro v h; exact fits_live w _ v h
  case case6 =>
    intro v h
    simp only [Fits] at h
    split at h
    · trivial
    · exact h.elim
  case case7 x y _ ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · trivial
    · rename_i z
      exact ih hsub z h
    · exact h.elim
  case case8 x y _ ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        simp only [Fits, hids]
        exact fun id hid => ih hsub _ (h id hid)
      · exact h.elim
    · exact fun z hz => ih hsub z (h z hz)
    · exact h.elim
  case case9 a1 a2 b1 b2 _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits] at h
    split at h
    · exact ⟨iha h1 _ h.1, ihb h2 _ h.2⟩
    · exact h.elim
  case case10 e1 a1 e2 a2 _ ihe iha =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits] at h
    split at h
    · exact ihe h1 _ h
    · exact iha h2 _ h
    · exact h.elim
  case case11 a1 e1 a2 e2 _ iha ihe =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits] at h
    split at h
    · exact iha h1 _ h
    · rename_i written
      split at h
      · rename_i c hc
        simp only [Fits, hc]
        exact causeFits_map (fun x hx => ihe h2 x hx) h
      · exact h.elim
    · exact h.elim
  case case12 e1 e2 _ ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i c hc
      simp only [Fits, hc]
      exact causeFits_map (fun x hx => ih hsub x hx) h
    · exact h.elim
  case case13 a1 e1 a2 e2 _ _ _ =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits] at h
    split at h
    · obtain ⟨fty, hs, ha, he⟩ := h
      exact ⟨fty, hs, subN_trans ha (sub_le_subN h1), subN_trans he (sub_le_subN h2)⟩
    · exact h.elim
  case case14 a1 a2 _ _ _ =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits] at h
    split at h
    · obtain ⟨t', hs, hl, hr⟩ := h
      exact ⟨t', hs, subN_trans hl (sub_le_subN h1), subN_trans (sub_le_subN h2) hr⟩
    · exact h.elim
  case case15 a1 e1 a2 e2 _ _ _ _ _ =>
    obtain ⟨h123, h4⟩ := Bool.and_eq_true_iff.mp hsub
    obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp h123
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
    intro v h
    simp only [Fits] at h
    split at h
    · obtain ⟨a', e', hs, ⟨ha1, ha2⟩, ⟨he1, he2⟩⟩ := h
      exact ⟨a', e', hs, ⟨subN_trans ha1 (sub_le_subN h1), subN_trans (sub_le_subN h2) ha2⟩,
        ⟨subN_trans he1 (sub_le_subN h3), subN_trans (sub_le_subN h4) he2⟩⟩
    · exact h.elim
  case case16 fs gs _ ih =>
    obtain ⟨hh, hall⟩ := Bool.and_eq_true_iff.mp hsub
    have hh' : heads (canonF fs) = heads (canonF gs) := of_decide_eq_true hh
    have hall' : ((canonF fs).zip (canonF gs)).all (fun pq => sub pq.1.2.2 pq.2.2.2) = true := by
      rw [← all_zip_attach (fun p q : String × Bool × Ty => sub p.2.2 q.2.2)]
      exact hall
    rw [List.all_eq_true] at hall'
    intro v h
    obtain ⟨vs, rfl, hv⟩ := fits_record_inv w v fs h
    rw [fits_record]
    refine fieldsFit_map ?_ ?_ vs hv
    · simp only [List.map_map]
      exact hh'
    · intro pq hpq x hx
      rw [List.zip_map, List.mem_map] at hpq
      obtain ⟨⟨q1, q2⟩, hq, rfl⟩ := hpq
      have hq1 : q1 ∈ canonF fs := (List.of_mem_zip hq).1
      have hq2 : q2 ∈ canonF gs := (List.of_mem_zip hq).2
      exact ih ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ (hall' (q1, q2) hq) x hx
  case case17 k1 v1 k2 v2 _ ihk _ ihv =>
    obtain ⟨hk12, hv⟩ := Bool.and_eq_true_iff.mp hsub
    obtain ⟨hk, _⟩ := Bool.and_eq_true_iff.mp hk12
    intro v h
    simp only [Fits] at h ⊢
    split at h
    · rename_i es
      refine ⟨h.1, fun e he => ?_⟩
      have := h.2 e he
      cases e
      case pair a x => exact ⟨ihk hk a this.1, ihv hv x this.2⟩
      all_goals exact this.elim
    · exact h.elim
  case case18 => exact Bool.noConfusion hsub

/-! ## Normalization and the checker's order (row 137, with the record and map cases) -/

theorem exists_mem_singleton_iff (P : Ty → Prop) (t : Ty) : (∃ x ∈ [t], P x) ↔ P t :=
  ⟨fun ⟨x, hx, hp⟩ => by rw [List.mem_singleton] at hx; subst hx; exact hp,
    fun hp => ⟨t, List.mem_singleton_self t, hp⟩⟩

theorem fits_ofMembers (w : World) (v : Val) :
    ∀ xs : List Ty, Fits w v (ofMembers xs) ↔ ∃ t ∈ xs, Fits w v t
  | [] => ⟨fun h => h.elim, fun ⟨_, hx, _⟩ => nomatch hx⟩
  | [x] => (exists_mem_singleton_iff (Fits w v) x).symm
  | x :: y :: ys => by
    have ih := fits_ofMembers w v (y :: ys)
    show (Fits w v x ∨ Fits w v (ofMembers (y :: ys))) ↔ _
    rw [ih]
    constructor
    · rintro (h | ⟨t, ht, hv⟩)
      · exact ⟨x, List.mem_cons_self, h⟩
      · exact ⟨t, List.mem_cons_of_mem x ht, hv⟩
    · rintro ⟨t, ht, hv⟩
      rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inl hv
      · exact Or.inr ⟨t, ht, hv⟩

/-- case: two (record and map are single members). -/
theorem fits_members (w : World) (v : Val) (t : Ty) :
    (∃ x ∈ t.members, Fits w v x) ↔ Fits w v t := by
  induction t with
  | never => exact ⟨fun ⟨_, hx, _⟩ => (nomatch hx), fun h => h.elim⟩
  | union a b iha ihb =>
    show (∃ x ∈ a.members ++ b.members, Fits w v x) ↔ (Fits w v a ∨ Fits w v b)
    rw [← iha, ← ihb]
    constructor
    · rintro ⟨x, hx, hv⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl ⟨x, hx, hv⟩
      · exact Or.inr ⟨x, hx, hv⟩
    · rintro (⟨x, hx, hv⟩ | ⟨x, hx, hv⟩)
      · exact ⟨x, List.mem_append_left _ hx, hv⟩
      · exact ⟨x, List.mem_append_right _ hx, hv⟩
  | _ => exact exists_mem_singleton_iff _ _

theorem fits_factors (w : World) (v : Val) (t : Ty) :
    (∃ x ∈ t.factors, Fits w v x) ↔ Fits w v t := by
  cases t with
  | never => exact exists_mem_singleton_iff _ _
  | _ => exact fits_members w v _

theorem fits_normalizeRow (w : World) (v : Val) (xs : List Ty) :
    (∃ t ∈ (normalizeRow xs).elems, Fits w v t) ↔ ∃ t ∈ xs, Fits w v t := by
  constructor
  · rintro ⟨t, ht, hv⟩
    exact ⟨t, ((mem_normalizeRow t xs).mp ht).1, hv⟩
  · rintro ⟨t, ht, hv⟩
    have ht' : t ∈ (Effect4.Row.normalize xs).elems := (Effect4.Row.mem_normalize t xs).mpr ht
    obtain ⟨u, hu, htu⟩ := Effect4.Row.antichain_coverage sub sub_refl sub_trans
      (Effect4.Row.normalize xs).elems t ht'
    exact ⟨u, hu, fits_sub w htu v hv⟩

theorem fits_prod_iff (w : World) (v : Val) (a b : Ty) :
    Fits w v (.prod a b) ↔ ∃ p q, v = .list [p, q] ∧ Fits w p a ∧ Fits w q b := by
  simp only [Fits]
  split
  · rename_i p q
    exact ⟨fun h => ⟨p, q, rfl, h.1, h.2⟩, fun ⟨p', q', he, h1, h2⟩ => by cases he; exact ⟨h1, h2⟩⟩
  · rename_i hne
    exact ⟨fun h => h.elim, fun ⟨p', q', he, _, _⟩ => absurd he (hne p' q')⟩

theorem fits_productMembers (w : World) (v : Val) (a b : Ty) :
    (∃ x ∈ productMembers a b, Fits w v x) ↔ Fits w v (.prod a b) := by
  rw [fits_prod_iff]
  constructor
  · rintro ⟨z, hz, hv⟩
    obtain ⟨x, hx, hz2⟩ := List.mem_flatMap.mp hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz2
    obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w v x y).mp hv
    exact ⟨p, q, rfl, (fits_factors w p a).mp ⟨x, hx, hp⟩, (fits_factors w q b).mp ⟨y, hy, hq⟩⟩
  · rintro ⟨p, q, rfl, hp, hq⟩
    obtain ⟨x, hx, hpx⟩ := (fits_factors w p a).mpr hp
    obtain ⟨y, hy, hqy⟩ := (fits_factors w q b).mpr hq
    exact ⟨.prod x y, List.mem_flatMap.mpr ⟨x, hx, List.mem_map.mpr ⟨y, hy, rfl⟩⟩,
      (fits_prod_iff w _ x y).mpr ⟨p, q, rfl, hpx, hqy⟩⟩

theorem causeFits_iff {m1 m2 : Val → Prop} (h : ∀ x, m1 x ↔ m2 x) (c : CauseV) :
    CauseFits m1 c ↔ CauseFits m2 c :=
  ⟨causeFits_map (fun x hx => (h x).mp hx), causeFits_map (fun x hx => (h x).mpr hx)⟩

theorem fiberDeclared_normalize (w : World) (id : FiberId) (a e : Ty) :
    FiberDeclared w id a.normalize e.normalize ↔ FiberDeclared w id a e := by
  unfold FiberDeclared
  simp only [subN_normalize_right]

theorem equiv_normalize (declared t : Ty) : Equiv declared t.normalize ↔ Equiv declared t := by
  unfold Equiv
  rw [subN_normalize_right, subN_normalize_left]

/-- new: the record case of `fits_normalize`. -/
theorem fits_normalize_record (w : World) (fs : List (String × Bool × Ty)) (v : Val)
    (ih : ∀ p ∈ fs, ∀ v, Fits w v (normalize p.2.2) ↔ Fits w v p.2.2) :
    Fits w v (normalize (.record fs)) ↔ Fits w v (.record fs) := by
  rw [normalize_record]
  cases v
  case ctor i vs =>
    cases i
    case zero =>
      rw [fits_record, fits_record,
        canonBy_of_ascending _ (ascending_map normPayload (canonBy_ascending fs)), List.map_map]
      have hmap : (canonF fs).map ((fun q => (q.1, fitterOf w q.2)) ∘ (fun q => (q.1, normPayload q.2))) =
          (canonF fs).map (fun q => (q.1, fitterOf w q.2)) := by
        apply List.map_congr_left
        intro q hq
        have hfun : (fun x => Fits w x (normalize q.2.2)) = fun x => Fits w x q.2.2 :=
          funext fun x => propext (ih q (mem_canonBy hq) x)
        simp only [Function.comp_apply, fitterOf, normPayload]
        rw [hfun]
      rw [hmap]
    case succ n => exact Iff.rfl
  all_goals exact Iff.rfl

/-- **Membership is invariant under normalization** (row 137's `fits_normalize`). case: two. -/
theorem fits_normalize (w : World) : ∀ (t : Ty) (v : Val), Fits w v t.normalize ↔ Fits w v t := by
  intro t
  induction t with
  | never => intro v; exact Iff.rfl
  | unknown => intro v; exact Iff.rfl
  | unit => intro v; exact Iff.rfl
  | nat => intro v; exact Iff.rfl
  | int => intro v; exact Iff.rfl
  | string => intro v; exact Iff.rfl
  | bool => intro v; exact Iff.rfl
  | handle _ => intro v; exact Iff.rfl
  | lit _ => intro v; exact Iff.rfl
  | var _ => intro v; exact Iff.rfl
  | union a b iha ihb =>
    intro v
    show Fits w v (ofMembers (normalizeRow (a.normalize.members ++ b.normalize.members)).elems) ↔
      (Fits w v a ∨ Fits w v b)
    rw [fits_ofMembers, fits_normalizeRow, ← iha, ← ihb, ← fits_members w v a.normalize,
      ← fits_members w v b.normalize]
    constructor
    · rintro ⟨x, hx, hv⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl ⟨x, hx, hv⟩
      · exact Or.inr ⟨x, hx, hv⟩
    · rintro (⟨x, hx, hv⟩ | ⟨x, hx, hv⟩)
      · exact ⟨x, List.mem_append_left _ hx, hv⟩
      · exact ⟨x, List.mem_append_right _ hx, hv⟩
  | prod a b iha ihb =>
    intro v
    show Fits w v (ofMembers (normalizeRow (productMembers a.normalize b.normalize)).elems) ↔
      Fits w v (.prod a b)
    rw [fits_ofMembers, fits_normalizeRow, fits_productMembers, fits_prod_iff, fits_prod_iff]
    constructor
    · rintro ⟨p, q, hv, hp, hq⟩
      exact ⟨p, q, hv, (iha p).mp hp, (ihb q).mp hq⟩
    · rintro ⟨p, q, hv, hp, hq⟩
      exact ⟨p, q, hv, (iha p).mpr hp, (ihb q).mpr hq⟩
  | option t ih =>
    intro v
    show Fits w v (.option t.normalize) ↔ Fits w v (.option t)
    simp only [Fits]
    split
    · exact Iff.rfl
    · exact ih _
    · exact Iff.rfl
  | list t ih =>
    intro v
    show Fits w v (.list t.normalize) ↔ Fits w v (.list t)
    simp only [Fits]
    split
    · split
      · exact forall₂_congr fun id _ => ih (Val.fiber id)
      · exact Iff.rfl
    · exact forall₂_congr fun x _ => ih x
    · exact Iff.rfl
  | except e a ihe iha =>
    intro v
    show Fits w v (.except e.normalize a.normalize) ↔ Fits w v (.except e a)
    simp only [Fits]
    split
    · exact ihe _
    · exact iha _
    · exact Iff.rfl
  | exitOf a e iha ihe =>
    intro v
    show Fits w v (.exitOf a.normalize e.normalize) ↔ Fits w v (.exitOf a e)
    simp only [Fits]
    split
    · exact iha _
    · split
      · exact causeFits_iff (fun x => ihe x) _
      · exact Iff.rfl
    · exact Iff.rfl
  | causeOf e ih =>
    intro v
    show Fits w v (.causeOf e.normalize) ↔ Fits w v (.causeOf e)
    simp only [Fits]
    split
    · exact causeFits_iff (fun x => ih x) _
    · exact Iff.rfl
  | fiberOf a e _ _ =>
    intro v
    show Fits w v (.fiberOf a.normalize e.normalize) ↔ Fits w v (.fiberOf a e)
    simp only [Fits]
    split
    · exact fiberDeclared_normalize w _ a e
    · exact Iff.rfl
  | refOf t _ =>
    intro v
    show Fits w v (.refOf t.normalize) ↔ Fits w v (.refOf t)
    simp only [Fits]
    split
    · unfold RefDeclared
      exact exists_congr fun t' => and_congr_right fun _ => equiv_normalize t' t
    · exact Iff.rfl
  | deferredOf a e _ _ =>
    intro v
    show Fits w v (.deferredOf a.normalize e.normalize) ↔ Fits w v (.deferredOf a e)
    simp only [Fits]
    split
    · unfold PromiseDeclared
      exact exists_congr fun a' => exists_congr fun e' => and_congr_right fun _ =>
        and_congr (equiv_normalize a' a) (equiv_normalize e' e)
    · exact Iff.rfl
  | record fs ih => exact fun v => fits_normalize_record w fs v (fun p hp v => ih p hp v)
  | map k t ihk iht =>
    intro v
    show Fits w v (.map k.normalize t.normalize) ↔ Fits w v (.map k t)
    have hk : (fun a => Fits w a k.normalize) = fun a => Fits w a k := funext fun a => propext (ihk a)
    have ht : (fun x => Fits w x t.normalize) = fun x => Fits w x t := funext fun x => propext (iht x)
    simp only [Fits]
    split
    · rw [hk, ht]
    · exact Iff.rfl

/-- **Membership is closed under the checker's order.** -/
theorem fits_subN (w : World) {a b : Ty} (h : subN a b = true) (v : Val) (hv : Fits w v a) :
    Fits w v b :=
  (fits_normalize w b v).mp (fits_sub w h v ((fits_normalize w a v).mpr hv))

theorem fits_join_left (w : World) (a b : Ty) (v : Val) (h : Fits w v a) : Fits w v (join a b) :=
  (fits_sub w (sub_normalize_union_left a b) v ((fits_normalize w a v).mpr h))

theorem fits_join_right (w : World) (a b : Ty) (v : Val) (h : Fits w v b) : Fits w v (join a b) :=
  (fits_sub w (sub_normalize_union_right a b) v ((fits_normalize w b v).mpr h))

/-! ## The boundary projection (R3.3): width at the row adapter, never inside a program

`sub` is exact: a wider record is not below a narrower one (`#guard`s in `P2Ty.lean`). The row
adapter, which receives rc.112's objects, projects the wider value onto the declared record. Its
relation is TypeScript's width-and-depth rule for readonly properties (`widthSub`, defined only
here) and its law is `fits_project`: a value of the wider record, projected, fits the declared
one. Bound: the projection recurses through record fields; under `option`, `list` and the other
heads the relation is `sub` (exact), so a record nested in a list is not projected. -/

/-- The order reads names only, even when the payload map reads the name. -/
theorem insertBy_mapName {β γ : Type} (f : String × β → γ) (p : String × β) (l : List (String × β)) :
    insertBy fieldKey (p.1, f p) (l.map (fun q => (q.1, f q))) =
      (insertBy fieldKey p l).map (fun q => (q.1, f q)) := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    rw [List.map_cons]
    unfold insertBy
    by_cases h1 : Effect4.Program.Ty.ltKey (fieldKey p.1) (fieldKey q.1) = true
    · rw [if_pos h1, if_pos h1]
      rfl
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : fieldKey p.1 = fieldKey q.1
      · rw [if_pos h2, if_pos h2]
        rfl
      · rw [if_neg h2, if_neg h2, ih]
        rfl

theorem canonBy_mapName {β γ : Type} (f : String × β → γ) (fs : List (String × β)) :
    canonF (fs.map (fun q => (q.1, f q))) = (canonF fs).map (fun q => (q.1, f q)) := by
  have step : ∀ (xs acc : List (String × β)),
      (xs.map (fun q => (q.1, f q))).foldl (fun a p => insertBy fieldKey p a)
          (acc.map (fun q => (q.1, f q))) =
        (xs.foldl (fun a p => insertBy fieldKey p a) acc).map (fun q => (q.1, f q)) := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons x xs ih =>
      intro acc
      simp only [List.map_cons, List.foldl_cons]
      rw [insertBy_mapName f x acc]
      exact ih (insertBy fieldKey x acc)
  exact step fs []

/-- The slot of a named field in a value laid out at a field list. -/
def slotOf (n : String) : List (String × Bool × Ty) → List Val → Option (Bool × Ty × Val)
  | (m, o, s) :: fs, x :: xs => if m = n then some (o, s, x) else slotOf n fs xs
  | _, _ => none

mutual
/-- The boundary's width-and-depth relation (TypeScript's readonly-property assignability),
used only by the row adapter. -/
def widthSub (a : Ty) : Ty → Bool
  | .record gs =>
    match a with
    | .record fs => widthFields fs gs
    | _ => false
  | b => sub a b
def widthFields (fs : List (String × Bool × Ty)) : List (String × Bool × Ty) → Bool
  | [] => true
  | (n, o, t) :: rest =>
    (match firstOf n fs with
     | some (o', s) => (o || !o') && widthSub s t
     | none => o) && widthFields fs rest
end

mutual
/-- **The boundary projection.** A value laid out at a record `a`, read at the declared record:
each declared field takes the slot of the source field of its name, projected; an optional
declared field the source lacks is `none`; the source's other fields are dropped. The declared
fields' values are produced in written order and placed by `canonF` (the fold's sort). -/
def project (a : Ty) (v : Val) : Ty → Val
  | .record gs =>
    match a, v with
    | .record fs, .ctor 0 vs => .ctor 0 ((canonF (projectNamed (canonF fs) vs gs)).map fun q => q.2.2)
    | _, _ => v
  | _ => v
def projectNamed (cf : List (String × Bool × Ty)) (vs : List Val) :
    List (String × Bool × Ty) → List (String × Bool × Val)
  | [] => []
  | (n, o, t) :: rest =>
    (n, o, match slotOf n cf vs with
      | some (o', s, x) =>
        match o, o', x with
        | true, true, .some y => .some (project s y t)
        | true, true, _ => .none
        | true, false, x => .some (project s x t)
        | false, _, x => project s x t
      | none => .none) :: projectNamed cf vs rest
end

/-- A declared field's projected slot. -/
def projSlot (cf : List (String × Bool × Ty)) (vs : List Val) (q : String × Bool × Ty) : Val :=
  match slotOf q.1 cf vs with
  | some (o', s, x) =>
    match q.2.1, o', x with
    | true, true, .some y => .some (project s y q.2.2)
    | true, true, _ => .none
    | true, false, x => .some (project s x q.2.2)
    | false, _, x => project s x q.2.2
  | none => .none

theorem projectNamed_eq_map (cf : List (String × Bool × Ty)) (vs : List Val)
    (gs : List (String × Bool × Ty)) :
    projectNamed cf vs gs = gs.map (fun q => (q.1, (q.2.1, projSlot cf vs q))) := by
  induction gs with
  | nil => rfl
  | cons q gs ih =>
    obtain ⟨n, o, t⟩ := q
    rw [projectNamed, ih]
    rfl

/-- A fitting value list answers each first-named field with a fitting slot. -/
theorem fieldsFit_slotOf (w : World) {n : String} {o' : Bool} {s : Ty} :
    ∀ (cf : List (String × Bool × Ty)) (vs : List Val),
      FieldsFit vs (cf.map (fun q => (q.1, fitterOf w q.2))) → firstOf n cf = some (o', s) →
      ∃ x, slotOf n cf vs = some (o', s, x) ∧ slotFits o' (fun y => Fits w y s) x
  | [], _, _, hf => nomatch hf
  | (m, o, t) :: cf, [], h, _ => h.elim
  | (m, o, t) :: cf, x :: xs, h, hf => by
    unfold firstOf at hf
    by_cases hm : m = n
    · rw [if_pos hm] at hf
      cases hf
      exact ⟨x, by rw [slotOf, if_pos hm], h.1⟩
    · rw [if_neg hm] at hf
      obtain ⟨y, hy, hfit⟩ := fieldsFit_slotOf w cf xs h.2 hf
      exact ⟨y, by rw [slotOf, if_neg hm]; exact hy, hfit⟩

theorem slotOf_none {n : String} : ∀ (cf : List (String × Bool × Ty)) (vs : List Val),
    firstOf n cf = none → slotOf n cf vs = none
  | [], _, _ => rfl
  | (_, _, _) :: _, [], _ => rfl
  | (m, o, t) :: cf, x :: xs, hf => by
    unfold firstOf at hf
    by_cases hm : m = n
    · rw [if_pos hm] at hf
      cases hf
    · rw [if_neg hm] at hf
      rw [slotOf, if_neg hm]
      exact slotOf_none cf xs hf

theorem fieldsFit_of_forall (w : World) (val : String × Bool × Ty → Val) :
    ∀ (l : List (String × Bool × Ty)), (∀ q ∈ l, slotFits q.2.1 (fun y => Fits w y q.2.2) (val q)) →
      FieldsFit (l.map val) (l.map (fun q => (q.1, fitterOf w q.2)))
  | [], _ => trivial
  | q :: l, h => ⟨h q List.mem_cons_self, fieldsFit_of_forall w val l (fun r hr => h r (List.mem_cons_of_mem _ hr))⟩

theorem widthFields_mem {fs : List (String × Bool × Ty)} :
    ∀ {gs : List (String × Bool × Ty)}, widthFields fs gs = true → ∀ q ∈ gs,
      (match firstOf q.1 fs with
       | some (o', s) => (q.2.1 || !o') && widthSub s q.2.2
       | none => q.2.1) = true
  | [], _, q, hq => absurd hq List.not_mem_nil
  | (n, o, t) :: rest, h, q, hq => by
    rw [widthFields, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h.1
    · exact widthFields_mem h.2 q hq

/-- **The boundary projection's law** (proved): a value of a record, projected onto any record
its relation allows, fits the declared record (the tree verifier's `fits_coerce` shape, on the
production-shaped judgment with worlds, handles and optional keys). -/
theorem fits_project (w : World) : ∀ (b a : Ty) (v : Val), widthSub a b = true → Fits w v a →
    Fits w (project a v b) b := by
  intro b
  induction b with
  | record gs ih =>
    intro a v hw hv
    cases a
    case record fs =>
      have hw' : widthFields fs gs = true := hw
      obtain ⟨vs, rfl, hvs⟩ := fits_record_inv w v fs hv
      show Fits w (.ctor 0 ((canonF (projectNamed (canonF fs) vs gs)).map fun q => q.2.2)) (.record gs)
      rw [fits_record, projectNamed_eq_map, canonBy_mapName (fun q => (q.2.1, projSlot (canonF fs) vs q)),
        List.map_map]
      refine fieldsFit_of_forall w _ (canonF gs) ?_
      intro q hq
      obtain ⟨n, o, t⟩ := q
      have hq' : (n, o, t) ∈ gs := mem_canonBy hq
      have hrel := widthFields_mem hw' (n, o, t) hq'
      have hfirst : firstOf n (canonF fs) = firstOf n fs := firstOf_canonBy fieldKey_injective n fs
      show slotFits o (fun y => Fits w y t) (projSlot (canonF fs) vs (n, o, t))
      unfold projSlot
      cases hf : firstOf n fs with
      | none =>
        rw [hf] at hrel
        have hnone := slotOf_none (canonF fs) vs (hfirst.trans hf)
        simp only at hrel
        rw [hnone, hrel]
        trivial
      | some os =>
        obtain ⟨o', s⟩ := os
        rw [hf] at hrel
        simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hrel
        obtain ⟨hflag, hws⟩ := hrel
        obtain ⟨x, hx, hfit⟩ := fieldsFit_slotOf w (canonF fs) vs hvs (hfirst.trans hf)
        rw [hx]
        have ihq := ih (n, o, t) hq'
        cases o <;> cases o'
        · exact ihq s x hws hfit
        · rcases hflag with hflag | hflag <;> exact absurd hflag (by decide)
        · exact ihq s x hws hfit
        · cases x
          case none => trivial
          case some y => exact ihq s y hws hfit
          all_goals exact hfit.elim
    all_goals exact absurd hw (by simp only [widthSub, Bool.false_eq_true, not_false_eq_true])
  | _ =>
    intro a v hw hv
    exact fits_sub w hw v hv

/-! ## The red controls, on the copy -/

/-- RED CONTROL (proved): width with positional values is unsound. The boundary relation holds,
the value fits the wider record, and the same value does not fit the narrower one; the projection
is what makes it fit. -/
theorem positional_width_unsound (w : World) :
    widthSub (.record [("id", false, .nat), ("name", false, .string)]) (.record [("id", false, .nat)]) = true ∧
      Fits w (.ctor 0 [.nat 7, .str "Ada"]) (.record [("id", false, .nat), ("name", false, .string)]) ∧
      ¬ Fits w (.ctor 0 [.nat 7, .str "Ada"]) (.record [("id", false, .nat)]) ∧
      Fits w (project (.record [("id", false, .nat), ("name", false, .string)]) (.ctor 0 [.nat 7, .str "Ada"])
        (.record [("id", false, .nat)])) (.record [("id", false, .nat)]) := by
  refine ⟨by decide +kernel, ?_, ?_, ?_⟩
  · rw [fits_record]
    exact ⟨trivial, trivial, trivial⟩
  · rw [fits_record]
    intro h
    exact h.2
  · exact fits_project w _ _ _ (by decide +kernel) (by rw [fits_record]; exact ⟨trivial, trivial, trivial⟩)

/-- The written-order read, as a check: the value's slots against the written fields. -/
def hasTyWritten (v : Val) (t : Ty) (al : List String) : Bool :=
  match t, v with
  | .record fs, .ctor 0 vs => fieldsHasTy vs (checkers fs al)
  | t, v => hasTy v t al

/-- RED CONTROL (proved): the written-order read is not invariant under normalization (the
verifier's `hasTyV_normalize_fails`, on the copy). -/
theorem written_order_not_invariant :
    hasTyWritten (.ctor 0 [.str "x", .nat 1]) (.record [("b", false, .nat), ("a", false, .string)]) [] = false ∧
      hasTyWritten (.ctor 0 [.str "x", .nat 1])
        (normalize (.record [("b", false, .nat), ("a", false, .string)])) [] = true := by
  decide +kernel

end ProbeP

#print axioms ProbeP.subN_trans
#print axioms ProbeP.sub_le_subN
#print axioms ProbeP.fits_record
#print axioms ProbeP.fits_record_inv
#print axioms ProbeP.fits_hasTy
#print axioms ProbeP.fits_live
#print axioms ProbeP.fits_map
#print axioms ProbeP.fits_sub
#print axioms ProbeP.fits_members
#print axioms ProbeP.fits_normalizeRow
#print axioms ProbeP.fits_productMembers
#print axioms ProbeP.fits_normalize_record
#print axioms ProbeP.fits_normalize
#print axioms ProbeP.fits_subN
#print axioms ProbeP.fits_join_left
#print axioms ProbeP.fits_join_right
#print axioms ProbeP.canonBy_mapName
#print axioms ProbeP.fieldsFit_slotOf
#print axioms ProbeP.fits_project
#print axioms ProbeP.positional_width_unsound
#print axioms ProbeP.written_order_not_invariant
