import Effect4.Laws.Program.Typed.Validity
import Effect4.Program.FoldOf

/-!
# Value membership in a typed world

`Fits w value type` follows the value encoding and checks capability declarations at each
handle leaf. A union uses one branch for both shape and declarations; products, results,
exits and fiber snapshots retain the declarations of their components.

A handle arm compares its declaration in the checker's order `Ty.subN` (both sides normalized):
invariant handles use it in both directions (`Equiv`), the covariant fiber handle in one. That
is row 96's D1 as amended by row 137: "exactly the declared type" means equal normal forms
(`Ty.subN_equiv_iff`), so membership is invariant under normalization (`fits_normalize`) and
closed under the checker's order and its join (`fits_subN`, `fits_join_left`,
`fits_join_right`); with the raw order it was neither (`E4-TYPED-CE-009`). The native cell and
deferred spellings require declarations at `nat` and `(nat, nat)`. `Live` reads the world's
declaration tables, and `unknown` requires `Live`. These are the D1–D4 rulings of decision
row 96.

The fold and laws belong here, below admission, so they depend on no retired value judgment.
The runtime admission check remains separate.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed
open Effect4.Machine Effect4.Program.Sched

/-- Invariance in the checker's order: subtyping both ways after normalizing, which is equality
of normal forms (`Ty.subN_equiv_iff`). -/
def Equiv (declared t : Ty) : Prop := Ty.subN declared t = true ∧ Ty.subN t declared = true

/-- A cell declared at a type related to `t` by subtyping in both directions. -/
def RefDeclared (w : World) (key : RefKey) (t : Ty) : Prop :=
  ∃ t', w.Ρ key = some t' ∧ Equiv t' t

/-- A deferred declared at columns related to `(a, e)` by subtyping in both directions. -/
def PromiseDeclared (w : World) (key : DeferredKey) (a e : Ty) : Prop :=
  ∃ a' e', w.«Π» key = some (a', e') ∧ Equiv a' a ∧ Equiv e' e

/-- A fiber declared at a type below `(a, e)` in the checker's order: the fiber handle is
covariant. -/
def FiberDeclared (w : World) (id : FiberId) (a e : Ty) : Prop :=
  ∃ fty, w.Γ id = some fty ∧ Ty.subN fty.answer a = true ∧ Ty.subN fty.error e = true

/-- Declared liveness: every cell, deferred and fiber handle the value names is declared in the
world's tables. This is the declaration evidence supplied by allocation postconditions;
no heap-length evidence is required here. -/
def Live (w : World) (v : Val) : Prop :=
  ∀ h ∈ v.keys, match h with
  | .cell key => (w.Ρ key).isSome = true
  | .promise key => (w.«Π» key).isSome = true
  | .fiber id => (w.Γ id).isSome = true
  | _ => True

/-- The reserved and external handle spellings (`Val.hasTy`'s `.handle` arm), with the native
cell and deferred spellings read as their declarations: `Ref.Ref<number>` is a cell declared at
`nat`, `Deferred.Deferred<number, number>` a deferred declared at `(nat, nat)`. -/
def HandleFits (w : World) (kind : UInt8) (index : Nat) (target : String) : Prop :=
  match HandleKind.ofByte? kind with
  | some .cell => target = NativeOp.refTarget ∧ RefDeclared w ⟨index⟩ .nat
  | some .promise => target = NativeOp.deferredTarget ∧ PromiseDeclared w ⟨index⟩ .nat .nat
  | some .scope => target = Ty.scopeTarget
  | some .external => externalHandleTarget target = true ∧
      w.state.externals.allocated[index]? = some target
  | _ => False

/-- Membership at a service's static type (decision row 90): the service table's types are
scalars and non-context handles (`nativeServiceTypes`, `nativeReservedServiceTypes`), so this
needs no recursion; `flatFits_fits` connects it to `Fits`. -/
def FlatFits (w : World) (v : Val) : Ty → Prop
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .string => match v with | .str _ => True | _ => False
  | .handle target =>
    match v with | .handle kind index => HandleFits w kind index target | _ => False
  | _ => False

/-- A context's services fit their keys' static types, read off the world's static service
table (shape A, decisions row 112). -/
def ServicesFit (w : World) (services : Env.Ctx) : Prop :=
  ∀ key sv sty, services.getV key = some sv → w.serviceTy key = some sty →
    FlatFits w sv sty

/-- Every typed failure of a cause has an image satisfying `member`; defects and interruptions
are outside the error column (`reasonAdmits`, `Program/ErrorImage.lean:31`). -/
def CauseFits (member : Val → Prop) (c : CauseV) : Prop :=
  ∀ r ∈ c.reasons, match r with
  | .fail e _ => ∃ v, valOfErr e = some v ∧ member v
  | .die _ _ | .interrupt _ _ => True

/-- **The membership judgment.** The arms and value shapes are `Val.hasTy`'s, one for one; the
handle leaves read the world's declaration tables; `unknown` requires declared liveness. -/
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
    | _ => target = Ty.contextTarget ∧
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

/-- The exit judgment is the value judgment at the reified exit (`reifyExitVal`,
`Machine/Stores.lean:1637`): an exit is a value of `Exit<A, E>`. -/
def FitsExit (w : World) (ty : EffTy) (ex : ExitV) : Prop :=
  Fits w (reifyExitVal ex) (.exitOf ty.answer ty.error)

/-- The cause judgment, at an error column. -/
abbrev FitsCause (w : World) (errTy : Ty) (c : CauseV) : Prop :=
  CauseFits (fun x => Fits w x errTy) c

/-! ## Exit and cause membership -/

/-- A successful exit fits exactly when its value fits the answer column. -/
theorem fitsExit_success_iff (w : World) (ty : EffTy) (v : Val) :
    FitsExit w ty (.success v) ↔ Fits w v ty.answer := Iff.rfl

/-- A failed exit fits exactly when its cause fits the error column. -/
theorem fitsExit_failure_iff (w : World) (ty : EffTy) (c : CauseV) :
    FitsExit w ty (.failure c) ↔ FitsCause w ty.error c := by
  unfold FitsExit
  simp only [reifyExitVal, Fits, Store.Image.ofVal_toVal]

/-- An exit whose failure carries no `Fail` reason: interruptions and defects only. Every
success is clean. The sanitized exit at a preempted skip is clean (`Cause.sanitize_clean`). -/
def cleanExit : ExitV → Bool
  | .success _ => true
  | .failure c => c.reasons.all fun r => r.tag != .fail

/-- Membership at the answer column gives membership of a successful exit. -/
theorem fitsExit_success (w : World) (ty : EffTy) (v : Val) (h : Fits w v ty.answer) :
    FitsExit w ty (.success v) := h

/-- A clean failure fits every effect type: only `Fail` reasons use the error column. -/
theorem fitsExit_of_clean (w : World) (ty : EffTy) (c : CauseV)
    (h : cleanExit (.failure c) = true) : FitsExit w ty (.failure c) := by
  have hall : ∀ r ∈ c.reasons, r.tag ≠ .fail := by
    intro r hr
    exact bne_iff_ne.mp (List.all_eq_true.mp h r hr)
  rw [fitsExit_failure_iff]
  intro r hr
  have hne := hall r hr
  cases r with
  | fail e ann => exact absurd rfl hne
  | die _ _ => trivial
  | interrupt _ _ => trivial

/-- At a `never` error column a failed exit is clean: no value fits `never`. -/
theorem cleanExit_of_never_fits (w : World) (ty : EffTy) (c : CauseV) (never : ty.error = .never)
    (h : FitsExit w ty (.failure c)) : cleanExit (.failure c) = true := by
  rw [fitsExit_failure_iff, never] at h
  unfold cleanExit
  rw [List.all_eq_true]
  intro r hr
  have hr' := h r hr
  cases r with
  | fail e ann =>
    obtain ⟨v, _, hv⟩ := hr'
    exact False.elim hv
  | die _ _ => rfl
  | interrupt _ _ => rfl

/-- A failed exit's membership depends only on the error column. -/
theorem fitsExit_failure_of_error {w : World} {tin tout : EffTy} {c : CauseV}
    (herr : tin.error = tout.error) (h : FitsExit w tin (.failure c)) : FitsExit w tout (.failure c) := by
  rw [fitsExit_failure_iff] at h ⊢
  rw [← herr]
  exact h

theorem causeFits_map {m1 m2 : Val → Prop} (hm : ∀ x, m1 x → m2 x) {c : CauseV}
    (h : CauseFits m1 c) : CauseFits m2 c := by
  intro r hr
  have hr' := h r hr
  cases r with
  | fail e ann =>
    obtain ⟨v, hv, h1⟩ := hr'
    exact ⟨v, hv, hm v h1⟩
  | die _ _ => trivial
  | interrupt _ _ => trivial

/-- A service's membership at a flat type is membership. -/
theorem flatFits_fits {w : World} {v : Val} {t : Ty} (h : FlatFits w v t) :
    Fits w v t := by
  cases t
  case unit => exact h
  case nat => exact h
  case bool => exact h
  case string => exact h
  case handle target =>
    simp only [FlatFits] at h
    split at h
    · exact h
    · exact h.elim
  all_goals exact h.elim

/-! ## The judgment is a fold (the census rule: every traversal is a fold)

`fold_of` (`Program/FoldOf.lean`) reads the hand recursion and emits its `TyAlgebra` with the
connector `Fits.eq_cata`, as it does for `Val.hasTy` (`Laws/Program/Folds/Ty.lean`). -/

fold_of Effect4.Program.Typed.Fits

/-! ## The valid direction: membership implies the shape check -/

/-- A cause whose failures fit also passes the shape check's cause fold. -/
theorem causeFits_admits {member : Val → Prop} {m : Val → Ty → Bool} {e : Ty}
    (h : ∀ x, member x → m x e = true) (c : CauseV) (hc : CauseFits member c) :
    causeAdmits m e c = true := by
  unfold causeAdmits
  rw [List.all_eq_true]
  intro r hr
  have hr' := hc r hr
  cases r with
  | fail err ann =>
    obtain ⟨v, hv, hm⟩ := hr'
    simp only [reasonAdmits, hv]
    exact h v hm
  | die _ _ => rfl
  | interrupt _ _ => rfl

/-- **Fits implies the shape check** at the world's own allocation table, at every type. -/
theorem fits_hasTy (w : World) : ∀ (ty : Ty) (v : Val), Fits w v ty →
    Val.hasTy v ty w.state.externals.allocated = true := by
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
      simp only [Val.hasTy]
      split at h
      · rename_i hk
        simp only [hk]
        exact beq_iff_eq.mpr h.1
      · rename_i hk
        simp only [hk]
        exact beq_iff_eq.mpr h.1
      · rename_i hk
        simp only [hk]
        exact beq_iff_eq.mpr h
      · rename_i hk
        simp only [hk]
        exact Bool.and_eq_true_iff.mpr ⟨h.1, beq_iff_eq.mpr h.2⟩
      · exact h.elim
    · obtain ⟨ht, ctx, hctx, _, _⟩ := h
      simp only [Val.hasTy]
      rw [hctx]
      exact Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr ht, rfl⟩
  | option a ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · rfl
    · rename_i x
      simp only [Val.hasTy]
      exact ih x h
    · exact h.elim
  | list a ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        simp only [Val.hasTy, hids]
        exact List.all_eq_true.mpr fun id hid => ih _ (h id hid)
      · exact h.elim
    · rename_i values
      simp only [Val.hasTy]
      exact List.all_eq_true.mpr fun x hx => ih x (h x hx)
    · exact h.elim
  | prod a b iha ihb =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i x y
      simp only [Val.hasTy]
      exact Bool.and_eq_true_iff.mpr ⟨iha x h.1, ihb y h.2⟩
    · exact h.elim
  | except e a ihe iha =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i err
      simp only [Val.hasTy]
      exact ihe err h
    · rename_i val
      simp only [Val.hasTy]
      exact iha val h
    · exact h.elim
  | exitOf a e iha ihe =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i x
      simp only [Val.hasTy]
      exact iha x h
    · rename_i written
      split at h
      · rename_i c hc
        simp only [Val.hasTy, hc]
        exact causeFits_admits (fun x hx => ihe x hx) c h
      · exact h.elim
    · exact h.elim
  | causeOf e ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i c hc
      simp only [Val.hasTy, hc]
      exact causeFits_admits (fun x hx => ih x hx) c h
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
    simp only [Val.hasTy]
    exact Bool.or_eq_true_iff.mpr (h.imp (ihl v) (ihr v))
  | lit s =>
    intro v h
    simp only [Fits] at h
    split at h
    · simp only [Val.hasTy]
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


/-! ## Declared liveness follows from membership -/

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

/-- A reified cause names no handle (`causeImage_handleFree`). -/
theorem keys_of_cause {v : Val} {c : CauseV} (h : Val.cause? v = some c) : v.keys = [] := by
  unfold Val.cause? at h
  split at h
  · rename_i written
    rw [Store.Image.ofVal_exact causeImage h]
    exact Val.keys_exitErr c
  · exact nomatch h

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

/-- **Membership implies declared liveness**, at every type. -/
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
      exact live_of_keys_nil (keys_of_cause hc)
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


/-! ## Membership under world extension -/

theorem isSome_extends {K A : Type} {t1 t2 : K → Option A} (ht : TableExtends t1 t2) {k : K}
    (h : (t1 k).isSome = true) : (t2 k).isSome = true := by
  cases hs : t1 k with
  | none => rw [hs] at h; cases h
  | some a => rw [ht k a hs]; rfl

section Map
variable {w1 w2 : World}
  (hΓ : TableExtends w1.Γ w2.Γ) (hPi : TableExtends w1.«Π» w2.«Π») (hRho : TableExtends w1.Ρ w2.Ρ)
  (halloc : Extends w1.state.externals.allocated w2.state.externals.allocated)
include hΓ hPi hRho

theorem live_map {v : Val} (h : Live w1 v) : Live w2 v := by
  intro k hk
  have hk' := h k hk
  cases k with
  | cell key => exact isSome_extends hRho hk'
  | promise key => exact isSome_extends hPi hk'
  | fiber id => exact isSome_extends hΓ hk'
  | scope _ => trivial
  | memoMap _ => trivial
  | external _ => trivial

omit hPi hRho in
theorem fiberDeclared_map {id : FiberId} {a e : Ty} (h : FiberDeclared w1 id a e) :
    FiberDeclared w2 id a e := by
  obtain ⟨fty, hs, ha, he⟩ := h
  exact ⟨fty, hΓ id fty hs, ha, he⟩

omit hΓ hPi in
theorem refDeclared_map {key : RefKey} {t : Ty} (h : RefDeclared w1 key t) :
    RefDeclared w2 key t := by
  obtain ⟨t', hs, hi⟩ := h
  exact ⟨t', hRho key t' hs, hi⟩

omit hΓ hRho in
theorem promiseDeclared_map {key : DeferredKey} {a e : Ty} (h : PromiseDeclared w1 key a e) :
    PromiseDeclared w2 key a e := by
  obtain ⟨a', e', hs, ha, he⟩ := h
  exact ⟨a', e', hPi key (a', e') hs, ha, he⟩

include halloc in
omit hΓ in
theorem handleFits_map {kind : UInt8} {index : Nat} {target : String}
    (h : HandleFits w1 kind index target) : HandleFits w2 kind index target := by
  simp only [HandleFits] at h ⊢
  split at h
  · exact ⟨h.1, refDeclared_map hRho h.2⟩
  · exact ⟨h.1, promiseDeclared_map hPi h.2⟩
  · exact h
  · exact ⟨h.1, halloc index target h.2⟩
  · exact h.elim

include halloc in
omit hΓ in
theorem flatFits_map {v : Val} {t : Ty} (h : FlatFits w1 v t) : FlatFits w2 v t := by
  cases t
  case unit => exact h
  case nat => exact h
  case bool => exact h
  case string => exact h
  case handle target =>
    simp only [FlatFits] at h ⊢
    split at h
    · exact handleFits_map hPi hRho halloc h
    · exact h.elim
  all_goals exact h.elim

include halloc in
omit hΓ in
/-- A context's services fit in a later world when every carrier the later world reads was the
earlier world's (the lookup agreement of decisions row 112; the world order gives it as an
equality of the two tables). -/
theorem servicesFit_map {services : Env.Ctx}
    (hsvc : ∀ key sty, w2.serviceTy key = some sty → w1.serviceTy key = some sty)
    (h : ServicesFit w1 services) : ServicesFit w2 services :=
  fun key sv sty hget hty => flatFits_map hPi hRho halloc (h key sv sty hget (hsvc key sty hty))

end Map

/-- Membership moves to a world whose declaration tables and allocation spellings extend
the old ones and whose service table agrees on every key it types. -/
theorem fits_map {w1 w2 : World}
    (hΓ : TableExtends w1.Γ w2.Γ) (hPi : TableExtends w1.«Π» w2.«Π») (hRho : TableExtends w1.Ρ w2.Ρ)
    (halloc : Extends w1.state.externals.allocated w2.state.externals.allocated)
    (hsvc : ∀ key sty, w2.serviceTy key = some sty → w1.serviceTy key = some sty) :
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
    · exact handleFits_map hPi hRho halloc h
    · obtain ⟨ht, ctx, hctx, hs, hl⟩ := h
      simp only [Fits]
      exact ⟨ht, ctx, hctx, servicesFit_map hPi hRho halloc hsvc hs, live_map hΓ hPi hRho hl⟩
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
    · exact fiberDeclared_map hΓ h
    · exact h.elim
  | union l r ihl ihr =>
    intro v h
    exact h.imp (ihl v) (ihr v)
  | lit s => intro v h; exact h
  | refOf t _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact refDeclared_map hRho h
    · exact h.elim
  | deferredOf a e _ _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact promiseDeclared_map hPi h
    · exact h.elim
  | var _ => intro v h; exact h.elim
  | unknown => intro v h; exact live_map hΓ hPi hRho h

/-- The world order fixes the service table, so a later world's lookups are the earlier one's. -/
theorem serviceTy_of_le {w w' : World} (ordered : w.le w') :
    ∀ key sty, w'.serviceTy key = some sty → w.serviceTy key = some sty :=
  fun _ _ h => le_serviceTy ordered ▸ h

/-- Membership is monotone under the host world order. -/
theorem fits_mono {w w' : World} (ordered : w.leHost w') {ty : Ty} {v : Val} (h : Fits w v ty) :
    Fits w' v ty :=
  fits_map ordered.1.2.1 ordered.1.2.2.1 ordered.1.2.2.2.1 ordered.2 (serviceTy_of_le ordered.1) ty v h

/-! ## Subsumption: membership respects the checker's subtyping -/

/-- **Fits is closed under `Ty.sub`.** By `fun_induction Ty.sub`, so the cases are `sub`'s own arms
(as `cata_admits_sub`, `Laws/Program/Admits.lean:36`). The handle arms move the raw step into the
checker's order (`Ty.sub_le_subN`) and compose there (`Ty.subN_trans`). -/
theorem fits_sub (w : World) {a b : Ty} (hsub : Ty.sub a b = true) : ∀ v, Fits w v a → Fits w v b := by
  fun_induction Ty.sub a b
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
      exact ⟨fty, hs, Ty.subN_trans ha (Ty.sub_le_subN h1), Ty.subN_trans he (Ty.sub_le_subN h2)⟩
    · exact h.elim
  case case14 a1 a2 _ _ _ =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits] at h
    split at h
    · obtain ⟨t', hs, hl, hr⟩ := h
      exact ⟨t', hs, Ty.subN_trans hl (Ty.sub_le_subN h1), Ty.subN_trans (Ty.sub_le_subN h2) hr⟩
    · exact h.elim
  case case15 a1 e1 a2 e2 _ _ _ _ _ =>
    obtain ⟨h123, h4⟩ := Bool.and_eq_true_iff.mp hsub
    obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp h123
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
    intro v h
    simp only [Fits] at h
    split at h
    · obtain ⟨a', e', hs, ⟨ha1, ha2⟩, ⟨he1, he2⟩⟩ := h
      exact ⟨a', e', hs,
        ⟨Ty.subN_trans ha1 (Ty.sub_le_subN h1), Ty.subN_trans (Ty.sub_le_subN h2) ha2⟩,
        ⟨Ty.subN_trans he1 (Ty.sub_le_subN h3), Ty.subN_trans (Ty.sub_le_subN h4) he2⟩⟩
    · exact h.elim
  case case16 => exact Bool.noConfusion hsub

/-! ## Normalization and the checker's order (decisions row 137)

`Fits` cannot see the spelling of a type, only its normal form: the union and product cases are
`hasTy_normalize`'s argument with `Prop` in place of `Bool` and `fits_sub` in place of
`hasTy_sub` (the antichain drops only members raw-below a kept one, and `productMembers`
distributes membership exactly), and the handle cases read declarations in `Ty.subN`, which is
blind to normalization on either side. So membership is closed under the checker's order and
under its join, the two closures every step that joins answers or enters an annotated loop
needs. -/

theorem exists_mem_singleton_iff (P : Ty → Prop) (t : Ty) : (∃ x ∈ [t], P x) ↔ P t :=
  ⟨fun ⟨x, hx, hp⟩ => by rw [List.mem_singleton] at hx; subst hx; exact hp,
    fun hp => ⟨t, List.mem_singleton_self t, hp⟩⟩

/-- Membership in a rebuilt union is membership in one of its listed members. -/
theorem fits_ofMembers (w : World) (v : Val) :
    ∀ xs : List Ty, Fits w v (Ty.ofMembers xs) ↔ ∃ t ∈ xs, Fits w v t
  | [] => ⟨fun h => h.elim, fun ⟨_, hx, _⟩ => nomatch hx⟩
  | [x] => (exists_mem_singleton_iff (Fits w v) x).symm
  | x :: y :: ys => by
    have ih := fits_ofMembers w v (y :: ys)
    show (Fits w v x ∨ Fits w v (Ty.ofMembers (y :: ys))) ↔ _
    rw [ih]
    constructor
    · rintro (h | ⟨t, ht, hv⟩)
      · exact ⟨x, List.mem_cons_self .., h⟩
      · exact ⟨t, List.mem_cons_of_mem x ht, hv⟩
    · rintro ⟨t, ht, hv⟩
      rcases List.mem_cons.mp ht with rfl | ht
      · exact Or.inl hv
      · exact Or.inr ⟨t, ht, hv⟩

/-- Membership in a type is membership in one of its union members. -/
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
  | unknown => exact exists_mem_singleton_iff _ _
  | unit => exact exists_mem_singleton_iff _ _
  | nat => exact exists_mem_singleton_iff _ _
  | int => exact exists_mem_singleton_iff _ _
  | string => exact exists_mem_singleton_iff _ _
  | bool => exact exists_mem_singleton_iff _ _
  | handle _ => exact exists_mem_singleton_iff _ _
  | option _ _ => exact exists_mem_singleton_iff _ _
  | list _ _ => exact exists_mem_singleton_iff _ _
  | prod _ _ _ _ => exact exists_mem_singleton_iff _ _
  | except _ _ _ _ => exact exists_mem_singleton_iff _ _
  | exitOf _ _ _ _ => exact exists_mem_singleton_iff _ _
  | causeOf _ _ => exact exists_mem_singleton_iff _ _
  | fiberOf _ _ _ _ => exact exists_mem_singleton_iff _ _
  | lit _ => exact exists_mem_singleton_iff _ _
  | refOf _ _ => exact exists_mem_singleton_iff _ _
  | deferredOf _ _ _ _ => exact exists_mem_singleton_iff _ _
  | var _ => exact exists_mem_singleton_iff _ _

/-- Membership in a type is membership in one of its product factors. -/
theorem fits_factors (w : World) (v : Val) (t : Ty) :
    (∃ x ∈ t.factors, Fits w v x) ↔ Fits w v t := by
  cases t with
  | never => exact exists_mem_singleton_iff _ _
  | _ => exact fits_members w v _

/-- The antichain keeps a member above every dropped one, so it keeps membership. -/
theorem fits_normalizeRow (w : World) (v : Val) (xs : List Ty) :
    (∃ t ∈ (Ty.normalizeRow xs).elems, Fits w v t) ↔ ∃ t ∈ xs, Fits w v t := by
  constructor
  · rintro ⟨t, ht, hv⟩
    exact ⟨t, ((Ty.mem_normalizeRow t xs).mp ht).1, hv⟩
  · rintro ⟨t, ht, hv⟩
    have ht' : t ∈ (Effect4.Row.normalize xs).elems := (Effect4.Row.mem_normalize t xs).mpr ht
    obtain ⟨u, hu, htu⟩ := Effect4.Row.antichain_coverage Ty.sub Ty.sub_refl Ty.sub_trans
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

/-- Distributing a product over its factors keeps membership exactly. -/
theorem fits_productMembers (w : World) (v : Val) (a b : Ty) :
    (∃ x ∈ Ty.productMembers a b, Fits w v x) ↔ Fits w v (.prod a b) := by
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

/-- The fiber arm reads its columns in `Ty.subN`, which normalizing the query does not move. -/
theorem fiberDeclared_normalize (w : World) (id : FiberId) (a e : Ty) :
    FiberDeclared w id a.normalize e.normalize ↔ FiberDeclared w id a e := by
  unfold FiberDeclared
  simp only [Ty.subN_normalize_right]

/-- Invariance in `Ty.subN` does not see the spelling of the query. -/
theorem equiv_normalize (declared t : Ty) : Equiv declared t.normalize ↔ Equiv declared t := by
  unfold Equiv
  rw [Ty.subN_normalize_right, Ty.subN_normalize_left]

/-- **Membership is invariant under normalization** (row 137; `E4-TYPED-CE-009`'s repair). -/
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
    show Fits w v (Ty.ofMembers (Ty.normalizeRow (a.normalize.members ++ b.normalize.members)).elems) ↔
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
    show Fits w v (Ty.ofMembers (Ty.normalizeRow (Ty.productMembers a.normalize b.normalize)).elems) ↔
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

/-- **Membership is closed under the checker's order.** -/
theorem fits_subN (w : World) {a b : Ty} (h : Ty.subN a b = true) (v : Val) (hv : Fits w v a) :
    Fits w v b :=
  (fits_normalize w b v).mp (fits_sub w h v ((fits_normalize w a v).mpr hv))

/-- **Membership is closed under the checker's join**, on the left. -/
theorem fits_join_left (w : World) (a b : Ty) (v : Val) (h : Fits w v a) : Fits w v (Ty.join a b) :=
  fits_subN w (Ty.subN_join_left a b) v h

/-- **Membership is closed under the checker's join**, on the right. -/
theorem fits_join_right (w : World) (a b : Ty) (v : Val) (h : Fits w v b) : Fits w v (Ty.join a b) :=
  fits_subN w (Ty.subN_join_right a b) v h


/-! ## Exit monotonicity and subsumption

An exit is a value: `FitsExit` is `Fits` at the reified exit. -/

theorem fitsExit_mono {w w' : World} (ordered : w.leHost w') {ty : EffTy} {ex : ExitV}
    (h : FitsExit w ty ex) : FitsExit w' ty ex :=
  fits_mono ordered h

/-- Exit subsumption, column by column. -/
theorem fitsExit_sub {w : World} {ty ty' : EffTy} (ha : Ty.sub ty.answer ty'.answer = true)
    (he : Ty.sub ty.error ty'.error = true) {ex : ExitV} (h : FitsExit w ty ex) :
    FitsExit w ty' ex := by
  cases ex with
  | success v =>
    rw [fitsExit_success_iff] at h ⊢
    exact fits_sub w ha v h
  | failure c =>
    rw [fitsExit_failure_iff] at h ⊢
    exact causeFits_map (fun x hx => fits_sub w he x hx) h

/-- Exit subsumption in the checker's order, column by column. -/
theorem fitsExit_subN {w : World} {ty ty' : EffTy} (ha : Ty.subN ty.answer ty'.answer = true)
    (he : Ty.subN ty.error ty'.error = true) {ex : ExitV} (h : FitsExit w ty ex) :
    FitsExit w ty' ex := by
  cases ex with
  | success v =>
    rw [fitsExit_success_iff] at h ⊢
    exact fits_subN w ha v h
  | failure c =>
    rw [fitsExit_failure_iff] at h ⊢
    exact causeFits_map (fun x hx => fits_subN w he x hx) h

/-! ## Products and fiber results -/

/-- The pair atom's value (`NativeAtom.eval .pair`, `Machine/Term.lean:374`) fits the product. -/
theorem fits_pair {w : World} {x y : Val} {a b : Ty} (hx : Fits w x a) (hy : Fits w y b) :
    Fits w (.list [x, y]) (.prod a b) :=
  ⟨hx, hy⟩

/-- `fst` (`Machine/Term.lean:375`) keeps the first column's fit, handle declarations included. -/
theorem fits_fst {w : World} {v r : Val} {a b : Ty} (h : Fits w v (.prod a b))
    (hr : NativeAtom.eval .fst [v] = some r) : Fits w r a := by
  simp only [Fits] at h
  split at h
  · rename_i x y
    have hx : NativeAtom.eval .fst [.list [x, y]] = some x := rfl
    rw [hx] at hr
    cases hr
    exact h.1
  · exact h.elim

/-- Awaiting a fiber whose handle fits `fiberOf a e`: whatever exit the await answers at the
fiber's declared type in a later world fits `(a, e)`. -/
theorem await_fits {w w' : World} {id : FiberId} {a e : Ty} {ty : EffTy} {ex : ExitV}
    (h : Fits w (Val.fiber id) (.fiberOf a e)) (ordered : w.leHost w')
    (declared : w'.Γ id = some ty) (hex : FitsExit w' ty ex) (req : Env.Requirement) :
    FitsExit w' ⟨a, e, req⟩ ex := by
  obtain ⟨fty, hs, ha, he⟩ := h
  have hs' := ordered.1.2.1 id fty hs
  rw [declared] at hs'
  cases hs'
  exact fitsExit_subN ha he hex


/-! ## The list arm reads one decoded element view

`Val.asList?` gives ordinary lists and admitted snapshots one decoded element view. The list
arm is exactly membership of every element it decodes. -/

theorem fits_list_iff (w : World) (v : Val) (a : Ty) :
    Fits w v (.list a) ↔ ∃ xs, Val.asList? v = some xs ∧ ∀ x ∈ xs, Fits w x a := by
  constructor
  · intro h
    simp only [Fits] at h
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        refine ⟨ids.map Val.fiber, ?_, fun x hx => ?_⟩
        · simp only [Val.asList?, hids, Option.map_some]
        · obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hx
          exact h id hid
      · exact h.elim
    · rename_i values
      exact ⟨values, rfl, h⟩
    · exact h.elim
  · rintro ⟨xs, hxs, h⟩
    simp only [Fits]
    split
    · rename_i p
      split
      · rename_i ids hids
        simp only [Val.asList?, hids, Option.map_some, Option.some.injEq] at hxs
        subst hxs
        exact fun id hid => h _ (List.mem_map_of_mem hid)
      · rename_i hnone
        simp only [Val.asList?, hnone, Option.map_none] at hxs
        cases hxs
    · rename_i values
      simp only [Val.asList?, Option.some.injEq] at hxs
      subst hxs
      exact h
    · rename_i hsnap hlist
      have hnone : Val.snapshot? v = none := by
        unfold Val.snapshot?
        split
        · rename_i p
          exact (hsnap p rfl).elim
        · rfl
      unfold Val.asList? at hxs
      split at hxs
      · rename_i values
        exact (hlist values rfl).elim
      · rw [hnone, Option.map_none] at hxs
        cases hxs


/-! ## The coarse heap reading from the strong one (TY-08)

`WorldValid.cells` types stored cells with the coarse check (`ValueOk`, `CompletionOk`), and the
typed state's generated predicates type them with `Fits` (`preds.HeapCell`, `preds.PromiseCell`,
`Typed/Assembly.lean`). The coarse reading follows from the strong one by `fits_hasTy`, so it can
be derived where the strong one holds. -/

/-- **The coarse heap column from the strong one (proved).** -/
theorem heapTable_of_fits {w : World}
    (h : Columns.Stores_refs (fun w key v => ∀ ty, w.Ρ key = some ty → Fits w v ty) w
      w.state.refs) : HeapTable w :=
  fun i v hv ty hty => fits_hasTy w ty v (h i v hv ty hty)

/-- **The coarse completion judgment from strong exit membership (proved).** The reference arm
needs nothing: since row 137 both judgments read a cell's declaration in `Ty.subN`. -/
theorem completionOk_of_fitsExit {w : World} {a e : Ty} {req : Env.Requirement} {ex : ExitV}
    (h : FitsExit w ⟨a, e, req⟩ ex) : CompletionOk w (a, e) (.ofExit ex) := by
  cases ex with
  | success v => exact fits_hasTy w a v ((fitsExit_success_iff w _ v).mp h)
  | failure c =>
    exact causeFits_admits (fun x hx => fits_hasTy w e x hx) c ((fitsExit_failure_iff w _ c).mp h)

/-! ## Term soundness (TY-07)

`evalTerm_hasTy` (`Laws/Program/Typed.lean`) is the coarse check's term law. This section is the
same law for membership: a term that types and evaluates over values fitting their types
evaluates to a value that fits the term's type (`evalTerm_fitsAll`; the `EnvTyped` form the
ledger names is `Typed/Admission.lean`'s `evalTerm_fits`). The atom table is discharged once per
scheme, as there (`atomFits`). Two things differ. The polymorphic schemes widen their bindings in
the order itself (`Ty.WidensSub`, `fits_instantiate_widens`), because membership reads
declarations at handles where the coarse check reads kinds. And `fst`/`snd` over a union of
products answer at `Ty.join`, which the checker's join closure covers (`projectProduct_fits`). -/

/-! ### Inversions at the scalar and value formers -/

theorem fits_unit_inv {w : World} {v : Val} (h : Fits w v .unit) : v = Val.unit := by
  simp only [Fits] at h
  split at h
  · rfl
  · exact h.elim

theorem fits_nat_inv {w : World} {v : Val} (h : Fits w v .nat) : ∃ n, v = Val.nat n := by
  simp only [Fits] at h
  split at h
  · exact ⟨_, rfl⟩
  · exact h.elim

theorem fits_bool_inv {w : World} {v : Val} (h : Fits w v .bool) : ∃ b, v = Val.bool b := by
  simp only [Fits] at h
  split at h
  · exact ⟨_, rfl⟩
  · exact h.elim

theorem fits_string_inv {w : World} {v : Val} (h : Fits w v .string) : ∃ s, v = Val.str s := by
  simp only [Fits] at h
  split at h
  · exact ⟨_, rfl⟩
  · exact h.elim

theorem fits_option_inv {w : World} {v : Val} {a : Ty} (h : Fits w v (.option a)) :
    v = Store.Val.none ∨ ∃ x, v = Store.Val.some x ∧ Fits w x a := by
  simp only [Fits] at h
  split at h
  · exact Or.inl rfl
  · rename_i x
    exact Or.inr ⟨x, rfl, h⟩
  · exact h.elim

/-! ### Values fitting an argument list -/

/-- Values fitting a list of types, position by position: an atom's arguments. -/
inductive FitsAll (w : World) : List Val → List Ty → Prop
  | nil : FitsAll w [] []
  | cons {v : Val} {t : Ty} {vs : List Val} {ts : List Ty} :
      Fits w v t → FitsAll w vs ts → FitsAll w (v :: vs) (t :: ts)

namespace FitsAll

variable {w : World}

theorem get? {vs : List Val} {tys : List Ty} (h : FitsAll w vs tys) {i : Nat} {v : Val} {t : Ty}
    (hv : vs[i]? = some v) (ht : tys[i]? = some t) : Fits w v t := by
  induction h generalizing i with
  | nil => cases hv
  | cons hvt _ ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hv ht
      subst hv
      subst ht
      exact hvt
    | succ i =>
      simp only [List.getElem?_cons_succ] at hv ht
      exact ih hv ht

theorem nil_inv {vs : List Val} (h : FitsAll w vs []) : vs = [] := by
  cases h
  rfl

theorem singleton_inv {vs : List Val} {t : Ty} (h : FitsAll w vs [t]) :
    ∃ v, vs = [v] ∧ Fits w v t := by
  cases h with
  | cons hv hrest =>
    cases hrest
    exact ⟨_, rfl, hv⟩

theorem pair_inv {vs : List Val} {a b : Ty} (h : FitsAll w vs [a, b]) :
    ∃ x y, vs = [x, y] ∧ Fits w x a ∧ Fits w y b := by
  cases h with
  | cons hx hrest =>
    cases hrest with
    | cons hy hrest' =>
      cases hrest'
      exact ⟨_, _, rfl, hx, hy⟩

theorem triple_inv {vs : List Val} {a b c : Ty} (h : FitsAll w vs [a, b, c]) :
    ∃ x y z, vs = [x, y, z] ∧ Fits w x a ∧ Fits w y b ∧ Fits w z c := by
  cases h with
  | cons hx hrest =>
    cases hrest with
    | cons hy hrest' =>
      cases hrest' with
      | cons hz hrest'' =>
        cases hrest''
        exact ⟨_, _, _, rfl, hx, hy, hz⟩

/-- Pointwise subsumption: the fixed-signature guard (`NativeAtom.monoApply`). -/
theorem sub {vs : List Val} {tys params : List Ty} (h : FitsAll w vs tys)
    (hlen : tys.length = params.length)
    (hall : (tys.zip params).all (fun (a, e) => a.sub e) = true) : FitsAll w vs params := by
  induction h generalizing params with
  | nil =>
    cases params with
    | nil => exact .nil
    | cons _ _ => exact absurd hlen (by simp only [List.length_cons, List.length_nil]; exact nofun)
  | cons hv _ ih =>
    cases params with
    | nil => exact absurd hlen (by simp only [List.length_cons, List.length_nil]; exact nofun)
    | cons p ps =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      exact .cons (fits_sub w hall.1 _ hv) (ih hlen hall.2)

/-- Values each below one type: the variadic guard. -/
theorem all_sub {vs : List Val} {tys : List Ty} (h : FitsAll w vs tys) {t : Ty}
    (hall : tys.all (·.sub t) = true) : ∀ v ∈ vs, Fits w v t := by
  induction h with
  | nil => intro v hv; cases hv
  | cons hv _ ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hsub, hrest⟩ := hall
    intro x hx
    cases hx with
    | head => exact fits_sub w hsub _ hv
    | tail _ hx => exact ih hrest x hx

end FitsAll

/-- An environment judged pointwise is an argument-list judgment (the bridge from `EnvTyped`). -/
theorem fitsAll_of_pointwise {w : World} :
    ∀ {tys : List Ty} {vs : List Val}, tys.length = vs.length →
      (∀ (i : Nat) (ty : Ty) (v : Val), tys[i]? = some ty → vs[i]? = some v → Fits w v ty) →
      FitsAll w vs tys
  | [], [], _, _ => .nil
  | [], _ :: _, hlen, _ => absurd hlen (by simp only [List.length_cons, List.length_nil]; exact nofun)
  | _ :: _, [], hlen, _ => absurd hlen (by simp only [List.length_cons, List.length_nil]; exact nofun)
  | t :: ts, v :: vs, hlen, h =>
    .cons (h 0 t v rfl rfl)
      (fitsAll_of_pointwise (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen)
        (fun i ty x hty hx => h (i + 1) ty x hty hx))

/-! ### Templates: membership is monotone in the bindings -/

/-- Membership moves along a widening of the bindings on a template whose parameters sit under
value formers only (`Ty.valueVars`): a parameter's binding moves up in raw `sub`, which
`fits_sub` carries, and every handle former's arguments are closed, so instantiation leaves
them alone (`Ty.instantiate_of_noVars`). -/
theorem fits_instantiate_widens {σ σ' : Ty.Subst} (hw : Ty.WidensSub σ σ') (w : World) :
    ∀ (t : Ty), Ty.valueVars t = true →
      ∀ v, Fits w v (Ty.instantiate σ t) → Fits w v (Ty.instantiate σ' t) := by
  intro t
  induction t with
  | var i =>
    intro _ v h
    change Fits w v ((σ.lookup i).getD .never) at h
    show Fits w v ((σ'.lookup i).getD .never)
    cases hi : σ.lookup i with
    | none =>
      rw [hi] at h
      exact h.elim
    | some u =>
      rw [hi] at h
      obtain ⟨u', hi', hsub⟩ := hw i u hi
      rw [hi']
      exact fits_sub w hsub v h
  | option a ih =>
    intro hv v h
    change Ty.valueVars a = true at hv
    change Fits w v (.option (Ty.instantiate σ a)) at h
    show Fits w v (.option (Ty.instantiate σ' a))
    rcases fits_option_inv h with rfl | ⟨x, rfl, hx⟩
    · trivial
    · exact ih hv x hx
  | list a ih =>
    intro hv v h
    change Ty.valueVars a = true at hv
    change Fits w v (.list (Ty.instantiate σ a)) at h
    show Fits w v (.list (Ty.instantiate σ' a))
    obtain ⟨xs, hxs, hall⟩ := (fits_list_iff w v _).mp h
    exact (fits_list_iff w v _).mpr ⟨xs, hxs, fun x hx => ih hv x (hall x hx)⟩
  | prod a b iha ihb =>
    intro hv v h
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hv
    change Fits w v (.prod (Ty.instantiate σ a) (Ty.instantiate σ b)) at h
    show Fits w v (.prod (Ty.instantiate σ' a) (Ty.instantiate σ' b))
    obtain ⟨p, q, rfl, hp, hq⟩ := (fits_prod_iff w v _ _).mp h
    exact (fits_prod_iff w _ _ _).mpr ⟨p, q, rfl, iha ha p hp, ihb hb q hq⟩
  | except e a ihe iha =>
    intro hv v h
    obtain ⟨he, ha⟩ := Bool.and_eq_true_iff.mp hv
    change Fits w v (.except (Ty.instantiate σ e) (Ty.instantiate σ a)) at h
    show Fits w v (.except (Ty.instantiate σ' e) (Ty.instantiate σ' a))
    simp only [Fits] at h
    split at h
    · exact ihe he _ h
    · exact iha ha _ h
    · exact h.elim
  | exitOf a e iha ihe =>
    intro hv v h
    obtain ⟨ha, he⟩ := Bool.and_eq_true_iff.mp hv
    change Fits w v (.exitOf (Ty.instantiate σ a) (Ty.instantiate σ e)) at h
    show Fits w v (.exitOf (Ty.instantiate σ' a) (Ty.instantiate σ' e))
    simp only [Fits] at h
    split at h
    · exact iha ha _ h
    · rename_i written
      split at h
      · rename_i c hc
        simp only [Fits, hc]
        exact causeFits_map (fun x hx => ihe he x hx) h
      · exact h.elim
    · exact h.elim
  | causeOf e ih =>
    intro hv v h
    change Ty.valueVars e = true at hv
    change Fits w v (.causeOf (Ty.instantiate σ e)) at h
    show Fits w v (.causeOf (Ty.instantiate σ' e))
    simp only [Fits] at h
    split at h
    · rename_i c hc
      simp only [Fits, hc]
      exact causeFits_map (fun x hx => ih hv x hx) h
    · exact h.elim
  | union l r ihl ihr =>
    intro hv v h
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hv
    exact h.imp (ihl hl v) (ihr hr v)
  | fiberOf a e _ _ =>
    intro hv v h
    obtain ⟨ha, he⟩ := Bool.and_eq_true_iff.mp hv
    change Fits w v (.fiberOf (Ty.instantiate σ a) (Ty.instantiate σ e)) at h
    show Fits w v (.fiberOf (Ty.instantiate σ' a) (Ty.instantiate σ' e))
    rw [Ty.instantiate_of_noVars σ a ha, Ty.instantiate_of_noVars σ e he] at h
    rw [Ty.instantiate_of_noVars σ' a ha, Ty.instantiate_of_noVars σ' e he]
    exact h
  | refOf a _ =>
    intro hv v h
    change Fits w v (.refOf (Ty.instantiate σ a)) at h
    show Fits w v (.refOf (Ty.instantiate σ' a))
    rw [Ty.instantiate_of_noVars σ a hv] at h
    rw [Ty.instantiate_of_noVars σ' a hv]
    exact h
  | deferredOf a e _ _ =>
    intro hv v h
    obtain ⟨ha, he⟩ := Bool.and_eq_true_iff.mp hv
    change Fits w v (.deferredOf (Ty.instantiate σ a) (Ty.instantiate σ e)) at h
    show Fits w v (.deferredOf (Ty.instantiate σ' a) (Ty.instantiate σ' e))
    rw [Ty.instantiate_of_noVars σ a ha, Ty.instantiate_of_noVars σ e he] at h
    rw [Ty.instantiate_of_noVars σ' a ha, Ty.instantiate_of_noVars σ' e he]
    exact h
  | never => intro _ v h; exact h
  | unit => intro _ v h; exact h
  | nat => intro _ v h; exact h
  | int => intro _ v h; exact h
  | string => intro _ v h; exact h
  | bool => intro _ v h; exact h
  | handle _ => intro _ v h; exact h
  | lit _ => intro _ v h; exact h
  | unknown => intro _ v h; exact h

/-- A list match puts every argument at its parameter's instance under the bindings of the
LAST step (the coarse `Fits.instantiate`'s twin): each guard holds at its own step
(`Ty.matchTemplate_sound`), and the later steps only widen (`Ty.matchTemplateArgs_widensSub`). -/
theorem FitsAll.instantiate {w : World} {join : Bool} :
    ∀ {σ₀ σ : Ty.Subst} {ps : List Ty}, (∀ p ∈ ps, Ty.valueVars p = true) →
      ∀ {vs : List Val} {tys : List Ty}, Ty.matchTemplateArgs σ₀ ps tys join = some σ →
        FitsAll w vs tys → FitsAll w vs (ps.map (Ty.instantiate σ))
  | _, _, [], _, _, [], _, .nil => .nil
  | _, _, [], _, _, _ :: _, hmatch, _ => nomatch hmatch
  | _, _, _ :: _, _, _, [], hmatch, _ => nomatch hmatch
  | σ₀, σ, p :: ps, hps, _, r :: rs, hmatch, .cons hv hfit => by
    simp only [Ty.matchTemplateArgs, Option.bind_eq_some_iff] at hmatch
    obtain ⟨σ₁, h₁, hrest⟩ := hmatch
    exact .cons
      (fits_instantiate_widens (Ty.matchTemplateArgs_widensSub hrest) w p
        (hps p List.mem_cons_self) _ (fits_sub w (Ty.matchTemplate_sound σ₀ p r σ₁ h₁) _ hv))
      (FitsAll.instantiate (fun q hq => hps q (List.mem_cons_of_mem p hq)) hrest hfit)

/-! ### Atom soundness, once per scheme -/

/-- The per-atom obligation for membership: at any argument types the atom accepts, values
fitting those types that evaluate evaluate to a value fitting the answer type. -/
def AtomFits (a : NativeAtom) : Prop :=
  ∀ (w : World) (tys : List Ty) (ty : Ty) (vs : List Val) (v : Val),
    a.typeOf tys = some ty → FitsAll w vs tys → NativeAtom.eval a vs = some v → Fits w v ty

theorem atomFits_of_mono {a : NativeAtom} {params : List Ty} {answer : Ty}
    (hs : (NativeAtom.spec a).scheme = .mono params answer)
    (hev : ∀ (w : World) (vs : List Val) (v : Val), FitsAll w vs params →
      NativeAtom.eval a vs = some v → Fits w v answer) : AtomFits a := by
  intro w tys ty vs v hty hfit hv
  simp only [NativeAtom.typeOf, hs, NativeAtom.Scheme.apply, NativeAtom.monoApply] at hty
  split at hty
  · next hguard =>
    cases hty
    exact hev w vs v (hfit.sub hguard.1 hguard.2) hv
  · exact nomatch hty

theorem atomFits_of_variadic {a : NativeAtom} {param answer : Ty}
    (hs : (NativeAtom.spec a).scheme = .variadic param answer)
    (hev : ∀ (w : World) (vs : List Val) (v : Val), (∀ x ∈ vs, Fits w x param) →
      NativeAtom.eval a vs = some v → Fits w v answer) : AtomFits a := by
  intro w tys ty vs v hty hfit hv
  simp only [NativeAtom.typeOf, hs, NativeAtom.Scheme.apply] at hty
  split at hty
  · next hall =>
    cases hty
    exact hev w vs v (hfit.all_sub hall) hv
  · exact nomatch hty

theorem atomFits_of_custom {a : NativeAtom} {tag : NativeAtom.CustomScheme}
    (hs : (NativeAtom.spec a).scheme = .custom tag)
    (hev : ∀ (w : World) (tys : List Ty) (ty : Ty) (vs : List Val) (v : Val),
      tag.apply tys = some ty → FitsAll w vs tys → NativeAtom.eval a vs = some v → Fits w v ty) :
    AtomFits a := by
  intro w tys ty vs v hty hfit hv
  simp only [NativeAtom.typeOf, hs, NativeAtom.Scheme.apply] at hty
  exact hev w tys ty vs v hty hfit hv

theorem atomFits_of_poly {a : NativeAtom} {params : List Ty} {answer : Ty} {join : Bool}
    (hs : (NativeAtom.spec a).scheme = .poly params answer join)
    (hvv : ∀ p ∈ params, Ty.valueVars p = true)
    (hev : ∀ (w : World) (σ : Ty.Subst) (vs : List Val) (v : Val),
      FitsAll w vs (params.map (Ty.instantiate σ)) → NativeAtom.eval a vs = some v →
        Fits w v (Ty.instantiate σ answer)) : AtomFits a := by
  intro w tys ty vs v hty hfit hv
  simp only [NativeAtom.typeOf, hs, NativeAtom.Scheme.apply] at hty
  obtain ⟨σ, hmatch, rfl⟩ := Option.map_eq_some_iff.mp hty
  exact hev w σ vs v (FitsAll.instantiate hvv hmatch hfit) hv

theorem atomFits_of_alts {a : NativeAtom} {alts : List (List Ty × Ty)}
    (hs : (NativeAtom.spec a).scheme = .alts alts)
    (hev : ∀ params answer, (params, answer) ∈ alts → ∀ (w : World) (vs : List Val) (v : Val),
      FitsAll w vs params → NativeAtom.eval a vs = some v → Fits w v answer) : AtomFits a := by
  intro w tys ty vs v hty hfit hv
  simp only [NativeAtom.typeOf, hs, NativeAtom.Scheme.apply] at hty
  obtain ⟨params, answer, hmem, heq⟩ := NativeAtom.findSome?_monoApply hty
  simp only [NativeAtom.monoApply] at heq
  split at heq
  · next hguard =>
    cases heq
    exact hev _ _ hmem w vs v (hfit.sub hguard.1 hguard.2) hv
  · exact nomatch heq

/-- A monomorphic atom of one of the evaluation shapes: its scalar answer is in the answer's
frame, which is membership at a scalar type. -/
theorem atomFits_of_shape {a : NativeAtom} (s : NativeAtom.Shape)
    (hs : (NativeAtom.spec a).scheme = .mono s.params s.answer) (hev : s.holds a) : AtomFits a := by
  refine atomFits_of_mono hs ?_
  intro w vs v hfit hv
  cases s with
  | nat1 | natTest =>
    obtain ⟨x, rfl, hx⟩ := hfit.singleton_inv
    obtain ⟨m, rfl⟩ := fits_nat_inv hx
    obtain ⟨_, he⟩ := hev m
    rw [he] at hv
    cases hv
    trivial
  | bool1 =>
    obtain ⟨x, rfl, hx⟩ := hfit.singleton_inv
    obtain ⟨b, rfl⟩ := fits_bool_inv hx
    obtain ⟨_, he⟩ := hev b
    rw [he] at hv
    cases hv
    trivial
  | nat2 | natRel =>
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨m, rfl⟩ := fits_nat_inv hx
    obtain ⟨k, rfl⟩ := fits_nat_inv hy
    obtain ⟨_, he⟩ := hev m k
    rw [he] at hv
    cases hv
    trivial
  | bool2 =>
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨p, rfl⟩ := fits_bool_inv hx
    obtain ⟨q, rfl⟩ := fits_bool_inv hy
    obtain ⟨_, he⟩ := hev p q
    rw [he] at hv
    cases hv
    trivial
  | strTest =>
    obtain ⟨x, y, rfl, hx, _⟩ := hfit.pair_inv
    obtain ⟨t, rfl⟩ := fits_string_inv hx
    obtain ⟨_, he⟩ := hev t y
    rw [he] at hv
    cases hv
    trivial
  | str2 =>
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    obtain ⟨s, rfl⟩ := fits_string_inv hx
    obtain ⟨t, rfl⟩ := fits_string_inv hy
    obtain ⟨_, he⟩ := hev s t
    rw [he] at hv
    cases hv
    trivial

/-! ### The projection and cause atoms -/

/-- Projecting a typed product, or a union of them, keeps membership: a direct product's
column fits its component, and a union's projections fit the join of the arms' projections. -/
theorem projectProduct_fits (w : World) (second : Bool) :
    ∀ (input output : Ty) (v r : Val), NativeAtom.projectProduct second input = some output →
      Fits w v input → NativeAtom.eval (if second then .snd else .fst) [v] = some r →
        Fits w r output := by
  intro input
  induction input with
  | never => intro output v r _ hv; exact hv.elim
  | prod a b _ _ =>
    intro output v r hproject hv hr
    simp only [NativeAtom.projectProduct] at hproject
    cases hproject
    obtain ⟨x, y, rfl, hx, hy⟩ := (fits_prod_iff w v a b).mp hv
    cases second
    · change NativeAtom.eval .fst [Val.list [x, y]] = some r at hr
      cases hr
      exact hx
    · change NativeAtom.eval .snd [Val.list [x, y]] = some r at hr
      cases hr
      exact hy
  | union a b iha ihb =>
    intro output v r hproject hv hr
    cases hleft : NativeAtom.projectProduct second a with
    | none => simp only [NativeAtom.projectProduct, hleft, Option.bind_eq_bind, Option.bind_none,
        reduceCtorEq] at hproject
    | some left =>
      cases hright : NativeAtom.projectProduct second b with
      | none => simp only [NativeAtom.projectProduct, hleft, hright,
          Option.bind_eq_bind, Option.bind_some, Option.bind_none, reduceCtorEq] at hproject
      | some right =>
        simp only [NativeAtom.projectProduct, hleft, hright, Option.bind_eq_bind,
          Option.bind_some] at hproject
        cases hproject
        rcases hv with ha | hb
        · exact fits_join_left w left right r (iha left v r hleft ha hr)
        · exact fits_join_right w left right r (ihb right v r hright hb hr)
  | _ => intro output v r hproject; simp only [NativeAtom.projectProduct, reduceCtorEq] at hproject

/-- A tag query answers a Boolean. -/
theorem queryTag_bool {tag : ReasonTag} {value answer : Val} (h : queryTag tag value = some answer) :
    ∃ b, answer = Val.bool b := by
  unfold queryTag at h
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨_, rfl⟩

/-- The reasons a cause-query input carries, each `Fail` with a payload in the error column. -/
theorem fits_queryReasons (w : World) (value : Val) (input error : Ty)
    (hinput : causeInputError? input = some error) (hfit : Fits w value input) :
    ∃ reasons, queryReasons? value = some reasons ∧
      CauseFits (fun x => Fits w x error) ⟨reasons⟩ := by
  unfold causeInputError? at hinput
  split at hinput
  · cases hinput
    change (match Val.cause? value with
      | some c => CauseFits (fun x => Fits w x error) c
      | none => False) at hfit
    cases hc : Val.cause? value with
    | none => rw [hc] at hfit; exact hfit.elim
    | some cause =>
      rw [hc] at hfit
      have hv := Val.cause?_exact hc
      subst value
      refine ⟨cause.reasons, ?_, hfit⟩
      change (Val.cause? (Val.exitErr cause)).map Cause.reasons = _
      rw [Val.cause?_exitErr]
      rfl
  · cases hinput
    simp only [Fits] at hfit
    split at hfit
    · exact ⟨[], rfl, fun _ hr => nomatch hr⟩
    · next written =>
      cases hc : causeImage.ofVal written with
      | none => rw [hc] at hfit; exact hfit.elim
      | some cause =>
        rw [hc] at hfit
        refine ⟨cause.reasons, ?_, hfit⟩
        change (causeImage.ofVal written).map Cause.reasons = _
        rw [hc]
        rfl
    · exact hfit.elim
  all_goals cases hinput

/-- The first `Fail` payload of reasons whose failures fit the error column fits it. -/
theorem fits_firstErrorValue {w : World} {error : Ty} {reasons : List (Reason Err Defect FiberId Ann)}
    (hc : CauseFits (fun x => Fits w x error) ⟨reasons⟩) {x : Val}
    (hx : (reasons.findSome? Reason.error?).bind valOfErr = some x) : Fits w x error := by
  obtain ⟨selected, hselected, hvalue⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨reason, hmem, hreason⟩ := List.exists_of_findSome?_eq_some hselected
  have hr := hc reason hmem
  cases reason with
  | fail actual annotations =>
    simp only [Reason.error?, Option.some.injEq] at hreason
    cases hreason
    obtain ⟨v, hv, hfit⟩ := hr
    rw [hvalue] at hv
    cases hv
    exact hfit
  | die defect annotations => cases hreason
  | interrupt fiber annotations => cases hreason

/-- The error query answers an option of the input's error column. -/
theorem queryError_fits (w : World) (value answer : Val) (input error : Ty)
    (hinput : causeInputError? input = some error) (hfit : Fits w value input)
    (h : queryError value = some answer) : Fits w answer (.option error) := by
  obtain ⟨reasons, hquery, hcause⟩ := fits_queryReasons w value input error hinput hfit
  unfold queryError at h
  rw [hquery] at h
  have h' := Option.some.inj h
  subst h'
  split
  · trivial
  · next extracted hfound => exact fits_firstErrorValue hcause hfound

/-! ### Every atom -/

/-- **Every atom keeps membership.** One line where a shape carries the argument; a short block
where the evaluation reads its argument's own frame (a projection, a cause query, an option, a
list); every polymorphic template's parameters sit under value formers (`decide`). -/
theorem atomFits (a : NativeAtom) : AtomFits a := by
  cases a with
  | succ => exact atomFits_of_shape .nat1 rfl (fun _ => ⟨_, rfl⟩)
  | pred => exact atomFits_of_shape .nat1 rfl (fun _ => ⟨_, rfl⟩)
  | isZero => exact atomFits_of_shape .natTest rfl (fun _ => ⟨_, rfl⟩)
  | boolNot => exact atomFits_of_shape .bool1 rfl (fun _ => ⟨_, rfl⟩)
  | add => exact atomFits_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩)
  | lt => exact atomFits_of_shape .natRel rfl (fun _ _ => ⟨_, rfl⟩)
  | boolOr => exact atomFits_of_shape .bool2 rfl (fun _ _ => ⟨_, rfl⟩)
  | boolAnd => exact atomFits_of_shape .bool2 rfl (fun _ _ => ⟨_, rfl⟩)
  | tagIs => exact atomFits_of_shape .strTest rfl (fun _ _ => ⟨_, rfl⟩)
  | mul => exact atomFits_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩)
  | natSub => exact atomFits_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩)
  | natDiv => exact atomFits_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩)
  | natMod => exact atomFits_of_shape .nat2 rfl (fun _ _ => ⟨_, rfl⟩)
  | strConcat => exact atomFits_of_shape .str2 rfl (fun _ _ => ⟨_, rfl⟩)
  | strings =>
    refine atomFits_of_variadic rfl ?_
    intro w vs v hall hv
    have hstr : ∀ x ∈ vs, ∃ s, x = Val.str s := fun x hx => fits_string_inv (hall x hx)
    change stringsAtom vs = some v at hv
    unfold stringsAtom at hv
    split at hv
    · cases hv
      exact (fits_list_iff w _ _).mpr ⟨vs, rfl, hall⟩
    · exact nomatch hv
  | eq =>
    refine atomFits_of_alts rfl ?_
    intro params answer hmem w vs v hfit hv
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hmem
    · obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
      obtain ⟨m, rfl⟩ := fits_nat_inv hx
      obtain ⟨n, rfl⟩ := fits_nat_inv hy
      cases hv
      trivial
    · obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
      obtain ⟨s, rfl⟩ := fits_string_inv hx
      obtain ⟨t, rfl⟩ := fits_string_inv hy
      cases hv
      trivial
  | pair =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    cases hv
    exact ⟨hx, hy⟩
  | fst =>
    refine atomFits_of_custom rfl ?_
    intro w tys ty vs v hty hfit hv
    simp only [NativeAtom.CustomScheme.apply, NativeAtom.projectRule] at hty
    split at hty
    · obtain ⟨x, rfl, hx⟩ := hfit.singleton_inv
      exact projectProduct_fits w false _ _ x v hty hx hv
    all_goals exact nomatch hty
  | snd =>
    refine atomFits_of_custom rfl ?_
    intro w tys ty vs v hty hfit hv
    simp only [NativeAtom.CustomScheme.apply, NativeAtom.projectRule] at hty
    split at hty
    · obtain ⟨x, rfl, hx⟩ := hfit.singleton_inv
      exact projectProduct_fits w true _ _ x v hty hx hv
    all_goals exact nomatch hty
  | causeIsFail | causeIsDie | causeIsInterrupt =>
    refine atomFits_of_custom rfl ?_
    intro w tys ty vs v hty hfit hv
    simp only [NativeAtom.CustomScheme.apply, NativeAtom.causeTestRule] at hty
    split at hty
    · obtain ⟨error, _, hanswer⟩ := Option.map_eq_some_iff.mp hty
      cases hanswer
      obtain ⟨x, rfl, _⟩ := hfit.singleton_inv
      obtain ⟨b, rfl⟩ := queryTag_bool hv
      trivial
    all_goals exact nomatch hty
  | causeError =>
    refine atomFits_of_custom rfl ?_
    intro w tys ty vs v hty hfit hv
    simp only [NativeAtom.CustomScheme.apply, NativeAtom.causeErrorRule] at hty
    split at hty
    · obtain ⟨error, hdomain, hanswer⟩ := Option.map_eq_some_iff.mp hty
      cases hanswer
      obtain ⟨x, rfl, hx⟩ := hfit.singleton_inv
      exact queryError_fits w x v _ error hdomain hx hv
    all_goals exact nomatch hty
  | isSome =>
    refine atomFits_of_mono rfl ?_
    intro w vs v hfit hv
    obtain ⟨x, rfl, hx⟩ := hfit.singleton_inv
    rcases fits_option_inv hx with rfl | ⟨y, rfl, _⟩
    · cases hv
      trivial
    · cases hv
      trivial
  | getOrElse =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
    rcases fits_option_inv hx with rfl | ⟨z, rfl, hz⟩
    · cases hv
      exact hy
    · cases hv
      exact hz
  | ite =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨c, x, y, rfl, hc, hx, hy⟩ := hfit.triple_inv
    obtain ⟨b, rfl⟩ := fits_bool_inv hc
    cases hv
    cases b
    · exact hy
    · exact hx
  | optSome =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨x, rfl, hx⟩ := hfit.singleton_inv
    cases hv
    exact hx
  | optNone =>
    refine atomFits_of_mono rfl fun w vs v hfit hv => ?_
    cases hfit.nil_inv
    cases hv
    trivial
  | listNil =>
    refine atomFits_of_mono rfl fun w vs v hfit hv => ?_
    cases hfit.nil_inv
    cases hv
    exact (fits_list_iff w _ _).mpr ⟨[], rfl, fun _ hx => nomatch hx⟩
  | listCons =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨x, xs, rfl, hx, hxs⟩ := hfit.pair_inv
    obtain ⟨elems, hl, helems⟩ := (fits_list_iff w xs _).mp hxs
    simp only [NativeAtom.eval, hl, Option.map_some, Option.some.injEq] at hv
    subst hv
    refine (fits_list_iff w _ _).mpr ⟨x :: elems, rfl, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact helems y hy
  | listGet =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨xs, i, rfl, hxs, hi⟩ := hfit.pair_inv
    obtain ⟨n, rfl⟩ := fits_nat_inv hi
    obtain ⟨elems, hl, helems⟩ := (fits_list_iff w xs _).mp hxs
    cases hn : elems[n]? with
    | none =>
      simp only [NativeAtom.eval, hl, hn, Option.map_some, Option.some.injEq] at hv
      subst hv
      trivial
    | some e =>
      simp only [NativeAtom.eval, hl, hn, Option.map_some, Option.some.injEq] at hv
      subst hv
      exact helems e (List.mem_of_getElem? hn)
  | listLength =>
    refine atomFits_of_mono rfl fun w vs v hfit hv => ?_
    obtain ⟨xs, rfl, hxs⟩ := hfit.singleton_inv
    obtain ⟨elems, hl, _⟩ := (fits_list_iff w xs _).mp hxs
    simp only [NativeAtom.eval, hl, Option.map_some, Option.some.injEq] at hv
    subst hv
    trivial
  | listAppend =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨xs, ys, rfl, hxs, hys⟩ := hfit.pair_inv
    obtain ⟨front, hf, hfront⟩ := (fits_list_iff w xs _).mp hxs
    obtain ⟨back, hb, hback⟩ := (fits_list_iff w ys _).mp hys
    simp only [NativeAtom.eval, hf, hb, Option.bind_some, Option.map_some, Option.some.injEq] at hv
    subst hv
    exact (fits_list_iff w _ _).mpr ⟨front ++ back, rfl,
      fun y hy => (List.mem_append.mp hy).elim (hfront y) (hback y)⟩

/-! ### Terms -/

/-- A literal's value fits its argument type under either const flag: a `str s` fits `lit s`
as it fits `string`. -/
theorem fits_lit (w : World) (const : Bool) (l : Lit) (v : Val) (h : l.toVal = some v) :
    Fits w v (litArgTy const l) := by
  cases l with
  | str s =>
    cases Option.some.inj h
    cases const
    · trivial
    · rfl
  | unit => cases Option.some.inj h; trivial
  | nat n => cases Option.some.inj h; trivial
  | bool b => cases Option.some.inj h; trivial

mutual
/-- **Term soundness for membership (TY-07, proved).** Under a signature whose atoms are the
native table's, a term that types and evaluates over values fitting their types evaluates to a
value that fits the term's type: the environment's fit at a variable, `fits_lit` at a literal,
`atomFits` at an application over the fitted argument values. -/
theorem evalTerm_fitsAll (sig : Signature NativeOp) (hatom : sig.atomOf = nativeAtomTy)
    (hconst : sig.constAtom = nativeConstAtom) (w : World) (t : Term) (env : List Val)
    (tys : List Ty) (ty : Ty) (v : Val) (hfit : FitsAll w env tys)
    (hty : termTy sig tys t = some ty) (hev : evalTerm env t = some v) : Fits w v ty := by
  cases t with
  | var i => exact hfit.get? hev hty
  | lit l =>
    have hty' : some (litArgTy false l) = some ty := hty
    cases hty'
    exact fits_lit w false l v hev
  | app atom args =>
    have hty' : (argsTy sig tys (sig.constAtom atom) args).bind (sig.atomOf atom) = some ty := hty
    obtain ⟨tl, hts, hatomTy⟩ := Option.bind_eq_some_iff.mp hty'
    rw [hatom] at hatomTy
    have hev' : (evalTerms env args).bind (nativeAtom atom) = some v := hev
    obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp hev'
    unfold nativeAtomTy at hatomTy
    obtain ⟨named, hname, hty2⟩ := Option.bind_eq_some_iff.mp hatomTy
    simp only [nativeAtom, hname, Option.bind_some] at hv
    exact atomFits named w tl ty vs v hty2
      (evalTerms_fitsAll sig hatom hconst w args env tys (sig.constAtom atom) tl vs hfit hts hvs) hv
termination_by structural t

/-- The list form: the values of typed arguments fit their argument types. -/
theorem evalTerms_fitsAll (sig : Signature NativeOp) (hatom : sig.atomOf = nativeAtomTy)
    (hconst : sig.constAtom = nativeConstAtom) (w : World) (ts : Terms) (env : List Val)
    (tys : List Ty) (const : Bool) (tl : List Ty) (vs : List Val) (hfit : FitsAll w env tys)
    (hty : argsTy sig tys const ts = some tl) (hev : evalTerms env ts = some vs) :
    FitsAll w vs tl := by
  cases ts with
  | nil =>
    have hty' : some ([] : List Ty) = some tl := hty
    have hev' : some ([] : List Val) = some vs := hev
    cases hty'
    cases hev'
    exact .nil
  | cons head tail =>
    rw [argsTy_cons] at hty
    obtain ⟨t1, ht1, hty'⟩ := Option.bind_eq_some_iff.mp hty
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp hty'
    cases hcons
    have hev2 : ((evalTerm env head).bind fun v =>
        (evalTerms env tail).bind fun rest => some (v :: rest)) = some vs := hev
    obtain ⟨v1, hv1, hev'⟩ := Option.bind_eq_some_iff.mp hev2
    obtain ⟨vrest, hvrest, hvcons⟩ := Option.bind_eq_some_iff.mp hev'
    cases hvcons
    refine .cons ?_ (evalTerms_fitsAll sig hatom hconst w tail env tys const rest vrest hfit hrest hvrest)
    rcases argTy_cases _ _ _ head t1 ht1 with ⟨value, rfl, rfl⟩ | ht1'
    · exact fits_lit w const value v1 hv1
    · exact evalTerm_fitsAll sig hatom hconst w head env tys t1 v1 hfit ht1' hv1
termination_by structural ts
end

/-! ## Inhabitance agrees with membership (decisions row 127; DI-67)

`inhabited` (`Program/Admission.lean`) is a `TyAlgebra` fold; the column check `admitColumn`
reads it. It agrees with `Fits` on every type (`inhabited_iff_fits`): soundness reads one member
(`inhabited_of_fits`, and DI-67's own statement over `Val.hasTy`, `inhabited_of_hasTy`);
completeness builds one world for every handle position at once, each declared at its own fresh
key (`fits_of_inhabited_fresh`). On the data fragment the witness needs no world
(`fits_of_inhabited_handleFree`). Closure under the raw order, the checker's order,
normalization and the join follows from membership's own (`inhabited_sub`, `inhabited_subN`,
`inhabited_normalize`, `inhabited_join`), so no second induction over the order is written.
`prod never nat` and `except never never` are canonical, not `never`, and empty
(E4-TYPED-CE-015): the column check refuses them (`admitColumn_prod_never_nat`,
`admitColumn_except_never_never`). -/

/-- **Sound against membership (proved).** A type with a member in some world is `inhabited`;
so refusing an `inhabited t = false` column never refuses a type with a member. -/
theorem inhabited_of_fits (w : World) : ∀ (t : Ty) (v : Val), Fits w v t → inhabited t = true := by
  intro t
  induction t with
  | never => intro v h; exact h.elim
  | int => intro v h; exact h.elim
  | var _ => intro v h; exact h.elim
  | unit | nat | string | bool | handle | option | list | exitOf | causeOf | fiberOf | lit
  | refOf | deferredOf | unknown => intro _ _; rfl
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

/-- **Sound against the coarse judgment (proved)**, DI-67's frozen statement: a type with a
value under some allocation table is `inhabited`. -/
theorem inhabited_of_hasTy :
    ∀ (t : Ty) (v : Val) (alloc : List String), Val.hasTy v t alloc = true → inhabited t = true := by
  intro t
  induction t with
  | never => intro v alloc h; exact Bool.noConfusion h
  | int => intro v alloc h; exact Bool.noConfusion h
  | var _ => intro v alloc h; exact Bool.noConfusion h
  | unit | nat | string | bool | handle | option | list | exitOf | causeOf | fiberOf | lit
  | refOf | deferredOf | unknown => intro _ _ _; rfl
  | prod a b iha ihb =>
    intro v alloc h
    simp only [Val.hasTy] at h
    split at h
    · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
      show (inhabited a && inhabited b) = true
      rw [iha _ _ h1, ihb _ _ h2]
      rfl
    · exact Bool.noConfusion h
  | except e a ihe iha =>
    intro v alloc h
    simp only [Val.hasTy] at h
    split at h
    · show (inhabited e || inhabited a) = true
      rw [ihe _ _ h]
      rfl
    · show (inhabited e || inhabited a) = true
      rw [iha _ _ h, Bool.or_true]
    · exact Bool.noConfusion h
  | union l r ihl ihr =>
    intro v alloc h
    simp only [Val.hasTy] at h
    show (inhabited l || inhabited r) = true
    rcases Bool.or_eq_true_iff.mp h with h | h
    · rw [ihl _ _ h]
      rfl
    · rw [ihr _ _ h, Bool.or_true]

/-! ### The data fragment: a witness that needs no world -/

/-- No handle, fiber, cell or deferred anywhere in the type: its members name no world entry. -/
def handleFreeAlg : TyAlgebra (fun _ => Bool) where
  ty_never := true
  ty_unit := true
  ty_nat := true
  ty_int := true
  ty_string := true
  ty_bool := true
  ty_handle _ := false
  ty_option a := a
  ty_list a := a
  ty_prod a b := a && b
  ty_except e a := e && a
  ty_exitOf a e := a && e
  ty_causeOf e := e
  ty_fiberOf _ _ := false
  ty_union l r := l && r
  ty_lit _ := true
  ty_refOf _ := false
  ty_deferredOf _ _ := false
  ty_var _ := true
  ty_unknown := true

/-- The data fragment (`handleFreeAlg`). -/
def handleFree (t : Ty) : Bool := cata_ty handleFreeAlg t

/-- **Complete on the data fragment (proved)**, with one witness for every world. -/
theorem fits_of_inhabited_handleFree :
    ∀ t : Ty, handleFree t = true → inhabited t = true → ∃ v : Val, ∀ w : World, Fits w v t := by
  intro t
  induction t with
  | never => intro _ hi; exact Bool.noConfusion hi
  | int => intro _ hi; exact Bool.noConfusion hi
  | var _ => intro _ hi; exact Bool.noConfusion hi
  | handle _ => intro hf _; exact Bool.noConfusion hf
  | fiberOf _ _ _ _ => intro hf _; exact Bool.noConfusion hf
  | refOf _ _ => intro hf _; exact Bool.noConfusion hf
  | deferredOf _ _ _ _ => intro hf _; exact Bool.noConfusion hf
  | unit => intro _ _; exact ⟨.unit, fun _ => trivial⟩
  | nat => intro _ _; exact ⟨.nat 0, fun _ => trivial⟩
  | string => intro _ _; exact ⟨.str "", fun _ => trivial⟩
  | bool => intro _ _; exact ⟨.bool true, fun _ => trivial⟩
  | lit s => intro _ _; exact ⟨.str s, fun _ => rfl⟩
  | option _ _ => intro _ _; exact ⟨.none, fun _ => trivial⟩
  | unknown => intro _ _; exact ⟨.unit, fun _ => live_of_keys_nil rfl⟩
  | list a _ =>
    intro _ _
    refine ⟨.list [], fun w => ?_⟩
    intro x hx
    nomatch hx
  | exitOf a e _ _ =>
    intro _ _
    exact ⟨Val.exitErr ⟨[]⟩, fun w =>
      (fitsExit_failure_iff w ⟨a, e, Env.Requirement.empty⟩ ⟨[]⟩).mpr (fun _ hr => nomatch hr)⟩
  | causeOf e _ =>
    intro _ _
    refine ⟨Val.exitErr ⟨[]⟩, fun w => ?_⟩
    have hc : Val.cause? (Val.exitErr ⟨[]⟩) = some ⟨[]⟩ := causeImage.ofVal_toVal ⟨[]⟩
    simp only [Fits, hc]
    intro _ hr
    nomatch hr
  | prod a b iha ihb =>
    intro hf hi
    have hf' : (handleFree a && handleFree b) = true := hf
    have hi' : (inhabited a && inhabited b) = true := hi
    obtain ⟨hfa, hfb⟩ := Bool.and_eq_true_iff.mp hf'
    obtain ⟨hia, hib⟩ := Bool.and_eq_true_iff.mp hi'
    obtain ⟨va, hva⟩ := iha hfa hia
    obtain ⟨vb, hvb⟩ := ihb hfb hib
    exact ⟨.list [va, vb], fun w => fits_pair (hva w) (hvb w)⟩
  | except e a ihe iha =>
    intro hf hi
    have hf' : (handleFree e && handleFree a) = true := hf
    have hi' : (inhabited e || inhabited a) = true := hi
    obtain ⟨hfe, hfa⟩ := Bool.and_eq_true_iff.mp hf'
    rcases Bool.or_eq_true_iff.mp hi' with hie | hia
    · obtain ⟨ve, hve⟩ := ihe hfe hie
      exact ⟨.ctor 0 [ve], fun w => hve w⟩
    · obtain ⟨va, hva⟩ := iha hfa hia
      exact ⟨.ctor 1 [va], fun w => hva w⟩
  | union l r ihl ihr =>
    intro hf hi
    have hf' : (handleFree l && handleFree r) = true := hf
    have hi' : (inhabited l || inhabited r) = true := hi
    obtain ⟨hfl, hfr⟩ := Bool.and_eq_true_iff.mp hf'
    rcases Bool.or_eq_true_iff.mp hi' with hil | hir
    · obtain ⟨v, hv⟩ := ihl hfl hil
      exact ⟨v, fun w => Or.inl (hv w)⟩
    · obtain ⟨v, hv⟩ := ihr hfr hir
      exact ⟨v, fun w => Or.inr (hv w)⟩


/-! ### Handles: one world for several, by fresh keys -/

/-- Every fiber, deferred and cell key from `n` on is undeclared. -/
structure FreshFrom (w : World) (n : Nat) : Prop where
  fiber : ∀ id : FiberId, n ≤ id.value → w.Γ id = none
  promise : ∀ key : DeferredKey, n ≤ key.index → w.«Π» key = none
  cell : ∀ key : RefKey, n ≤ key.index → w.Ρ key = none

/-- A later world as membership reads it: `fits_map`'s premises. -/
structure Grows (w w' : World) : Prop where
  fiber : TableExtends w.Γ w'.Γ
  promise : TableExtends w.«Π» w'.«Π»
  cell : TableExtends w.Ρ w'.Ρ
  alloc : Extends w.state.externals.allocated w'.state.externals.allocated
  service : w'.serviceTy = w.serviceTy

theorem Grows.refl (w : World) : Grows w w :=
  ⟨table_refl _, table_refl _, table_refl _, fun _ _ h => h, rfl⟩

theorem Grows.trans {a b c : World} (hab : Grows a b) (hbc : Grows b c) : Grows a c :=
  ⟨table_trans _ _ _ hab.fiber hbc.fiber, table_trans _ _ _ hab.promise hbc.promise,
    table_trans _ _ _ hab.cell hbc.cell, fun i t h => hbc.alloc i t (hab.alloc i t h),
    hbc.service.trans hab.service⟩

theorem Grows.fits {w w' : World} (h : Grows w w') {t : Ty} {v : Val} (hv : Fits w v t) :
    Fits w' v t :=
  fits_map h.fiber h.promise h.cell h.alloc
    (fun key sty hk => by rw [← h.service]; exact hk) t v hv

/-- Declaring fiber `n` keeps every earlier membership and frees the keys above it. -/
theorem FreshFrom.addFiber {w : World} {n : Nat} (h : FreshFrom w n) (ty : EffTy) :
    Grows w (w.addFiber ⟨n⟩ ty) ∧ FreshFrom (w.addFiber ⟨n⟩ ty) (n + 1) := by
  refine ⟨⟨insert_extends _ _ _ (h.fiber ⟨n⟩ (Nat.le_refl n)), table_refl _, table_refl _,
    fun _ _ hx => hx, rfl⟩, ⟨fun id hid => ?_, fun key hk => h.promise key (Nat.le_of_succ_le hk),
    fun key hk => h.cell key (Nat.le_of_succ_le hk)⟩⟩
  have hne : id ≠ ⟨n⟩ := fun heq => by
    subst heq
    exact Nat.not_succ_le_self n hid
  show tableInsert w.Γ ⟨n⟩ ty id = none
  rw [insert_other _ _ _ _ hne]
  exact h.fiber id (Nat.le_of_succ_le hid)

/-- Declaring cell `n`, likewise. -/
theorem FreshFrom.addRef {w : World} {n : Nat} (h : FreshFrom w n) (ty : Ty) :
    Grows w (w.addRef w.state ⟨n⟩ ty) ∧ FreshFrom (w.addRef w.state ⟨n⟩ ty) (n + 1) := by
  refine ⟨⟨table_refl _, table_refl _, insert_extends _ _ _ (h.cell ⟨n⟩ (Nat.le_refl n)),
    fun _ _ hx => hx, rfl⟩, ⟨fun id hid => h.fiber id (Nat.le_of_succ_le hid),
    fun key hk => h.promise key (Nat.le_of_succ_le hk), fun key hk => ?_⟩⟩
  have hne : key ≠ ⟨n⟩ := fun heq => by
    subst heq
    exact Nat.not_succ_le_self n hk
  show tableInsert w.Ρ ⟨n⟩ ty key = none
  rw [insert_other _ _ _ _ hne]
  exact h.cell key (Nat.le_of_succ_le hk)

/-- Declaring deferred `n`, likewise. -/
theorem FreshFrom.addPromise {w : World} {n : Nat} (h : FreshFrom w n) (types : Ty × Ty) :
    Grows w (w.addPromise w.state ⟨n⟩ types) ∧ FreshFrom (w.addPromise w.state ⟨n⟩ types) (n + 1) := by
  refine ⟨⟨table_refl _, insert_extends _ _ _ (h.promise ⟨n⟩ (Nat.le_refl n)), table_refl _,
    fun _ _ hx => hx, rfl⟩, ⟨fun id hid => h.fiber id (Nat.le_of_succ_le hid),
    fun key hk => ?_, fun key hk => h.cell key (Nat.le_of_succ_le hk)⟩⟩
  have hne : key ≠ ⟨n⟩ := fun heq => by
    subst heq
    exact Nat.not_succ_le_self n hk
  show tableInsert w.«Π» ⟨n⟩ types key = none
  rw [insert_other _ _ _ _ hne]
  exact h.promise key (Nat.le_of_succ_le hk)

/-- An external allocation at the end of the table. -/
def World.allocExternal (w : World) (target : String) : World :=
  { w with state := { w.state with externals :=
      { w.state.externals with allocated := w.state.externals.allocated ++ [target] } } }

theorem FreshFrom.allocExternal {w : World} {n : Nat} (h : FreshFrom w n) (target : String) :
    Grows w (w.allocExternal target) ∧ FreshFrom (w.allocExternal target) n :=
  ⟨⟨table_refl _, table_refl _, table_refl _, extends_append _ _, rfl⟩,
    ⟨h.fiber, h.promise, h.cell⟩⟩

/-- The `handle` former at every target, in a world grown from any world with fresh keys. -/
theorem fits_handle_fresh (target : String) (w : World) (n : Nat) (hn : FreshFrom w n) :
    ∃ (w' : World) (n' : Nat) (v : Val), Grows w w' ∧ FreshFrom w' n' ∧
      Fits w' v (.handle target) := by
  cases hc : internalHandleTargets.contains target with
  | false =>
    have ht : externalHandleTarget target = true := by
      unfold externalHandleTarget
      rw [hc]
      rfl
    obtain ⟨hg, hf⟩ := hn.allocExternal target
    exact ⟨_, n, Val.handle HandleKind.external.byte w.state.externals.allocated.length, hg, hf,
      ht, List.getElem?_concat_length⟩
  | true =>
    have hm : target ∈ internalHandleTargets := List.contains_iff_mem.mp hc
    simp only [internalHandleTargets, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl
    · obtain ⟨hg, hf⟩ := hn.addRef .nat
      exact ⟨_, n + 1, Val.handle HandleKind.cell.byte n, hg, hf, rfl, .nat, insert_here _ _ _,
        Ty.subN_refl _, Ty.subN_refl _⟩
    · obtain ⟨hg, hf⟩ := hn.addPromise (.nat, .nat)
      exact ⟨_, n + 1, Val.handle HandleKind.promise.byte n, hg, hf, rfl, .nat, .nat,
        insert_here _ _ _, ⟨Ty.subN_refl _, Ty.subN_refl _⟩, ⟨Ty.subN_refl _, Ty.subN_refl _⟩⟩
    · exact ⟨w, n, Val.handle HandleKind.scope.byte 0, Grows.refl w, hn,
        (rfl : Ty.scopeTarget = Ty.scopeTarget)⟩
    · have hkeys : (Val.context emptyCtx).keys = [] := by decide
      refine ⟨w, n, Val.context emptyCtx, Grows.refl w, hn, rfl, emptyCtx,
        ctxImage.ofVal_toVal emptyCtx, ?_, live_of_keys_nil hkeys⟩
      intro key sv sty hget _
      have hnone : emptyCtx.services.getV key = none := rfl
      rw [hnone] at hget
      cases hget

/-- **One world for several handles (proved).** An `inhabited` type has a member in a world grown
from any world whose keys are fresh from `n` on: each handle position is declared at its own
fresh key (`FreshFrom.addFiber`, `addRef`, `addPromise`) or allocated at the end of the external
table, and a product carries its first column's member into the world the second one grows
(`Grows.fits`). -/
theorem fits_of_inhabited_fresh : ∀ (t : Ty), inhabited t = true → ∀ (w : World) (n : Nat),
    FreshFrom w n → ∃ (w' : World) (n' : Nat) (v : Val), Grows w w' ∧ FreshFrom w' n' ∧ Fits w' v t := by
  intro t
  induction t with
  | never => intro hi; exact Bool.noConfusion hi
  | int => intro hi; exact Bool.noConfusion hi
  | var _ => intro hi; exact Bool.noConfusion hi
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
    exact ⟨w, n, Val.exitErr ⟨[]⟩, Grows.refl w, hn,
      (fitsExit_failure_iff w ⟨a, e, Env.Requirement.empty⟩ ⟨[]⟩).mpr (fun _ hr => nomatch hr)⟩
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
    obtain ⟨hg, hf⟩ := hn.addFiber ⟨a, e, Env.Requirement.empty⟩
    exact ⟨_, n + 1, Val.fiber ⟨n⟩, hg, hf, _, insert_here _ _ _, Ty.subN_refl _, Ty.subN_refl _⟩
  | refOf t _ =>
    intro _ w n hn
    obtain ⟨hg, hf⟩ := hn.addRef t
    exact ⟨_, n + 1, Val.cell ⟨n⟩, hg, hf, t, insert_here _ _ _, Ty.subN_refl _, Ty.subN_refl _⟩
  | deferredOf a e _ _ =>
    intro _ w n hn
    obtain ⟨hg, hf⟩ := hn.addPromise (a, e)
    exact ⟨_, n + 1, Val.promise ⟨n⟩, hg, hf, a, e, insert_here _ _ _,
      ⟨Ty.subN_refl _, Ty.subN_refl _⟩, ⟨Ty.subN_refl _, Ty.subN_refl _⟩⟩
  | prod a b iha ihb =>
    intro hi w n hn
    have hi' : (inhabited a && inhabited b) = true := hi
    obtain ⟨hia, hib⟩ := Bool.and_eq_true_iff.mp hi'
    obtain ⟨w1, n1, va, hg1, hf1, hva⟩ := iha hia w n hn
    obtain ⟨w2, n2, vb, hg2, hf2, hvb⟩ := ihb hib w1 n1 hf1
    exact ⟨w2, n2, .list [va, vb], hg1.trans hg2, hf2, fits_pair (hg2.fits hva) hvb⟩
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

/-- The initial world declares only the root fiber, so every key from 1 on is fresh. -/
theorem initialWorld_freshFrom (rootTy : EffTy) : FreshFrom (initialWorld rootTy) 1 := by
  refine ⟨fun id hid => ?_, fun _ _ => rfl, fun _ _ => rfl⟩
  have hne : id ≠ Api.root := fun heq => by
    subst heq
    exact Nat.lt_irrefl 0 hid
  show tableInsert (fun _ => none) Api.root rootTy id = none
  rw [insert_other _ _ _ _ hne]

/-- **Inhabitance agrees with membership (proved)**, on every type: the fold says `true` exactly
when some world has a member. Row 127's agreement theorem. -/
theorem inhabited_iff_fits (t : Ty) : inhabited t = true ↔ ∃ (w : World) (v : Val), Fits w v t := by
  constructor
  · intro hi
    obtain ⟨w', _, v, _, _, hv⟩ :=
      fits_of_inhabited_fresh t hi (initialWorld (EffTy.pure .unit)) 1 (initialWorld_freshFrom _)
    exact ⟨w', v, hv⟩
  · rintro ⟨w, v, h⟩
    exact inhabited_of_fits w t v h

/-- The agreement on the data fragment, with the witness world fixed (probe B's statement). -/
theorem inhabited_iff_handleFree (t : Ty) (hf : handleFree t = true) :
    inhabited t = true ↔ ∃ (w : World) (v : Val), Fits w v t := by
  constructor
  · intro hi
    obtain ⟨v, hv⟩ := fits_of_inhabited_handleFree t hf hi
    exact ⟨initialWorld (EffTy.pure .unit), v, hv _⟩
  · rintro ⟨w, v, h⟩
    exact inhabited_of_fits w t v h

/-! ### The handle witnesses -/

/-- A fiber declared at the columns, even `never, never` (a fiber that never completes). -/
theorem fiber_inhabited (a e : Ty) :
    Fits (initialWorld ⟨a, e, Env.Requirement.empty⟩) (Val.fiber Api.root) (.fiberOf a e) :=
  ⟨⟨a, e, Env.Requirement.empty⟩, rfl, Ty.subN_refl _, Ty.subN_refl _⟩

/-- A cell declared at the type. -/
theorem cell_inhabited (t : Ty) :
    Fits { initialWorld (EffTy.pure .unit) with Ρ := fun _ => some t } (Val.cell ⟨0⟩) (.refOf t) :=
  ⟨t, rfl, Ty.subN_refl _, Ty.subN_refl _⟩

/-- A deferred declared at the columns. -/
theorem promise_inhabited (a e : Ty) :
    Fits { initialWorld (EffTy.pure .unit) with «Π» := fun _ => some (a, e) } (Val.promise ⟨0⟩)
      (.deferredOf a e) :=
  ⟨a, e, rfl, ⟨Ty.subN_refl _, Ty.subN_refl _⟩, ⟨Ty.subN_refl _, Ty.subN_refl _⟩⟩

/-- Every `handle` target has a member in some world: the four internal spellings and an
external allocation (the types verifier's `handle_inhabited`). -/
theorem handle_inhabited (target : String) : ∃ (w : World) (v : Val), Fits w v (.handle target) :=
  (inhabited_iff_fits (.handle target)).mp rfl

/-! ### Closure: the raw order, the checker's order, normalization and the join -/

theorem inhabited_sub {a b : Ty} (hsub : Ty.sub a b = true) (h : inhabited a = true) :
    inhabited b = true := by
  obtain ⟨w, v, hv⟩ := (inhabited_iff_fits a).mp h
  exact inhabited_of_fits w b v (fits_sub w hsub v hv)

theorem inhabited_subN {a b : Ty} (hsub : Ty.subN a b = true) (h : inhabited a = true) :
    inhabited b = true := by
  obtain ⟨w, v, hv⟩ := (inhabited_iff_fits a).mp h
  exact inhabited_of_fits w b v (fits_subN w hsub v hv)

/-- Normalization keeps inhabitance (the checker's types are normal forms). -/
theorem inhabited_normalize (t : Ty) : inhabited t.normalize = inhabited t := by
  apply Bool.eq_iff_iff.mpr
  rw [inhabited_iff_fits, inhabited_iff_fits]
  constructor
  · rintro ⟨w, v, h⟩
    exact ⟨w, v, (fits_normalize w t v).mp h⟩
  · rintro ⟨w, v, h⟩
    exact ⟨w, v, (fits_normalize w t v).mpr h⟩

theorem inhabited_join (a b : Ty) : inhabited (Ty.join a b) = (inhabited a || inhabited b) :=
  inhabited_normalize (.union a b)

/-! ### The column check (rows 127 and 149) -/

/-- **The column check, read through membership (proved).** A column is admitted exactly when it
is the designed bottom or has a member in some world. -/
theorem admitColumn_iff (t : Ty) :
    admitColumn t = true ↔ t.normalize = .never ∨ ∃ (w : World) (v : Val), Fits w v t := by
  unfold admitColumn
  rw [Bool.or_eq_true, beq_iff_eq, inhabited_iff_fits]

/-- The column check is invariant under normalization. -/
theorem admitColumn_normalize (t : Ty) : admitColumn t.normalize = admitColumn t := by
  unfold admitColumn
  rw [Ty.normalize_idem, inhabited_normalize]

/-- **E4-TYPED-CE-015, the counterexample (proved):** `prod never nat` has no member in any
world, and it is canonical, not `never`. -/
theorem prod_never_nat_empty (w : World) (v : Val) : ¬ Fits w v (.prod .never .nat) :=
  fun h => absurd (inhabited_of_fits w _ v h) (by decide)

theorem except_never_never_empty (w : World) (v : Val) : ¬ Fits w v (.except .never .never) :=
  fun h => absurd (inhabited_of_fits w _ v h) (by decide)

/-- And none under any allocation table, in DI-67's own words. -/
theorem prod_never_nat_no_hasTy (v : Val) (alloc : List String) :
    Val.hasTy v (.prod .never .nat) alloc = false := by
  cases h : Val.hasTy v (.prod .never .nat) alloc with
  | false => rfl
  | true => exact absurd (inhabited_of_hasTy _ v alloc h) (by decide)

theorem except_never_never_no_hasTy (v : Val) (alloc : List String) :
    Val.hasTy v (.except .never .never) alloc = false := by
  cases h : Val.hasTy v (.except .never .never) alloc with
  | false => rfl
  | true => exact absurd (inhabited_of_hasTy _ v alloc h) (by decide)

/-- **E4-TYPED-CE-015, the repair at the column (proved):** the column check refuses both. -/
theorem admitColumn_prod_never_nat : admitColumn (.prod .never .nat) = false := by
  decide +kernel

theorem admitColumn_except_never_never : admitColumn (.except .never .never) = false := by
  decide +kernel

end Effect4.Program.Typed
