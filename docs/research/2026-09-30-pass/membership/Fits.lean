import Effect4.Laws.Program.Typed.Assembly
import Effect4.Program.FoldOf

/-!
# Research probe: one membership judgment over the actual value encoding

Seat MEMBERSHIP of the 2026-09-30 design-and-probing pass. Base `be15b062`. Research evidence,
outside the `Test` root; nothing here is imported by the tree.

`Fits w v ty` replaces `ValueOk w ty v ∧ HandlesFit w v ty` (`StrongValue`,
`src/Effect4/Laws/Program/Typed/Admission.lean:39-62`) by one recursion over the encoding
`Val.hasTy` reads (`src/Effect4/Program/Typed.lean:34-101`): the same arms, the same value
shapes, with the capability evidence (the world's declaration tables) checked at the leaf where
the handle sits. Shape and capability evidence therefore come from one derivation: a union
picks one branch for both, and a product, a Result, an exit and a snapshot recurse into their
payloads.
-/

set_option autoImplicit false

namespace Research.Pass.Membership
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched

/-- The typed world (`Laws/Program/Typed/World.lean:52`). -/
abbrev W := Effect4.Program.Typed.World

/-! ## Capability declarations, read from the world's tables

An invariant handle (`refOf`, `deferredOf`, and the native cell and deferred spellings) relates
its declared type to the static type through `inv`. Two readings are measured here:
`Equiv` (subtyping both ways, which is how `Ty.sub` states invariance, `Program/Ty.lean:452-453`)
and equality (how `HandlesFit` states it, `Typed/Admission.lean:41-42`). `Fits` takes `Equiv`;
`FitsEq` takes equality. -/

/-- The relation an invariant handle's declared type must bear to the static type. -/
abbrev Inv := Ty → Ty → Prop

/-- Invariance as `Ty.sub` reads it: subtyping both ways. -/
def Equiv (declared t : Ty) : Prop := declared.sub t = true ∧ t.sub declared = true

/-- A cell declared at a type `inv`-related to `t`. -/
def RefDeclared (w : W) (inv : Inv) (key : RefKey) (t : Ty) : Prop :=
  ∃ t', w.Ρ key = some t' ∧ inv t' t

/-- A deferred declared at columns `inv`-related to `(a, e)`. -/
def PromiseDeclared (w : W) (inv : Inv) (key : DeferredKey) (a e : Ty) : Prop :=
  ∃ a' e', w.«Π» key = some (a', e') ∧ inv a' a ∧ inv e' e

/-- A fiber declared at a type below `(a, e)`: the fiber handle is covariant. -/
def FiberDeclared (w : W) (id : FiberId) (a e : Ty) : Prop :=
  ∃ fty, w.Γ id = some fty ∧ fty.answer.sub a = true ∧ fty.error.sub e = true

/-- Declared liveness: every cell, deferred and fiber handle the value names is declared in the
world's tables. The table form, not the store-length form of `HandlesLive`: the two agree under
`WorldValid` (`live_iff_handlesLive` below), and only the table form follows from an allocation's
post (`storePost (.refMake _)` names `w'.Ρ key`, never the heap length). -/
def Live (w : W) (v : Val) : Prop :=
  ∀ h ∈ v.keys, match h with
  | .cell key => (w.Ρ key).isSome = true
  | .promise key => (w.«Π» key).isSome = true
  | .fiber id => (w.Γ id).isSome = true
  | _ => True

/-- The reserved and external handle spellings (`Val.hasTy`'s `.handle` arm), with the native
cell and deferred spellings read as their declarations: `Ref.Ref<number>` is a cell declared at
`nat`, `Deferred.Deferred<number, number>` a deferred declared at `(nat, nat)`. -/
def HandleFits (w : W) (inv : Inv) (kind : UInt8) (index : Nat) (target : String) : Prop :=
  match HandleKind.ofByte? kind with
  | some .cell => target = NativeOp.refTarget ∧ RefDeclared w inv ⟨index⟩ .nat
  | some .promise => target = NativeOp.deferredTarget ∧ PromiseDeclared w inv ⟨index⟩ .nat .nat
  | some .scope => target = Ty.scopeTarget
  | some .external => externalHandleTarget target = true ∧
      w.state.externals.allocated[index]? = some target
  | _ => False

/-- Membership at a service's static type (decision row 90): the service table's types are
scalars and non-context handles (`nativeServiceTypes`, `nativeReservedServiceTypes`), so this
needs no recursion; `flatFits_fits` connects it to `Fits`. -/
def FlatFits (w : W) (inv : Inv) (v : Val) : Ty → Prop
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .string => match v with | .str _ => True | _ => False
  | .handle target =>
    match v with | .handle kind index => HandleFits w inv kind index target | _ => False
  | _ => False

/-- A context's services fit their keys' static types. -/
def ServicesFit (w : W) (inv : Inv) (services : Env.Ctx) : Prop :=
  ∀ key sv sty, services.getV key = some sv → nativeServiceTy key = some sty →
    FlatFits w inv sv sty

/-- Every typed failure of a cause has an image satisfying `member`; defects and interruptions
are outside the error column (`reasonAdmits`, `Program/ErrorImage.lean:31`). -/
def CauseFits (member : Val → Prop) (c : CauseV) : Prop :=
  ∀ r ∈ c.reasons, match r with
  | .fail e _ => ∃ v, valOfErr e = some v ∧ member v
  | .die _ _ | .interrupt _ _ => True

/-- **The membership judgment.** The arms and value shapes are `Val.hasTy`'s, one for one; the
handle leaves read the world's declaration tables; `unknown` requires declared liveness. -/
def FitsInv (w : W) (inv : Inv) (v : Val) : Ty → Prop
  | .never => False
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .int => False
  | .string => match v with | .str _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .handle target =>
    match v with
    | .handle kind index => HandleFits w inv kind index target
    | _ => target = Ty.contextTarget ∧
        ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w inv ctx.services ∧ Live w v
  | .option a =>
    match v with
    | .none => True
    | .some x => FitsInv w inv x a
    | _ => False
  | .list a =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ∀ id ∈ ids, FitsInv w inv (Val.fiber id) a
      | none => False
    | .list values => ∀ x ∈ values, FitsInv w inv x a
    | _ => False
  | .prod a b =>
    match v with
    | .list [x, y] => FitsInv w inv x a ∧ FitsInv w inv y b
    | _ => False
  | .except e a =>
    match v with
    | .ctor 0 [err] => FitsInv w inv err e
    | .ctor 1 [val] => FitsInv w inv val a
    | _ => False
  | .exitOf a e =>
    match v with
    | Val.exitOk x => FitsInv w inv x a
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => CauseFits (fun x => FitsInv w inv x e) c
      | none => False
    | _ => False
  | .causeOf e =>
    match Val.cause? v with
    | some c => CauseFits (fun x => FitsInv w inv x e) c
    | none => False
  | .fiberOf a e =>
    match v with
    | Value.fiber index => FiberDeclared w ⟨index⟩ a e
    | _ => False
  | .union l r => FitsInv w inv v l ∨ FitsInv w inv v r
  | .lit s => match v with | .str s' => s' = s | _ => False
  | .refOf t =>
    match v with
    | Value.cell index => RefDeclared w inv ⟨index⟩ t
    | _ => False
  | .deferredOf a e =>
    match v with
    | Value.promise index => PromiseDeclared w inv ⟨index⟩ a e
    | _ => False
  | .var _ => False
  | .unknown => Live w v

/-- **The proposed judgment**: invariant handles read as `Ty.sub` reads them. -/
abbrev Fits (w : W) (v : Val) (ty : Ty) : Prop := FitsInv w Equiv v ty

/-- The same recursion with `HandlesFit`'s equality at invariant handles. -/
abbrev FitsEq (w : W) (v : Val) (ty : Ty) : Prop := FitsInv w (· = ·) v ty

/-- The exit judgment is the value judgment at the reified exit (`reifyExitVal`,
`Machine/Stores.lean:1637`): an exit is a value of `Exit<A, E>`. -/
def FitsExit (w : W) (ty : EffTy) (ex : ExitV) : Prop :=
  Fits w (reifyExitVal ex) (.exitOf ty.answer ty.error)

/-- The cause judgment, at an error column. -/
abbrev FitsCause (w : W) (errTy : Ty) (c : CauseV) : Prop :=
  CauseFits (fun x => Fits w x errTy) c

/-! ### Four basic facts every probe file uses -/

/-- A successful exit fits exactly when its value fits the answer column. -/
theorem fitsExit_success_iff (w : W) (ty : EffTy) (v : Val) :
    FitsExit w ty (.success v) ↔ Fits w v ty.answer := Iff.rfl

/-- A failed exit fits exactly when its cause fits the error column. -/
theorem fitsExit_failure_iff (w : W) (ty : EffTy) (c : CauseV) :
    FitsExit w ty (.failure c) ↔ FitsCause w ty.error c := by
  unfold FitsExit
  simp only [reifyExitVal, Fits, FitsInv, Store.Image.ofVal_toVal]

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
theorem flatFits_fitsInv {w : W} {inv : Inv} {v : Val} {t : Ty} (h : FlatFits w inv v t) :
    FitsInv w inv v t := by
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

/-! End of the shared block. -/


/-! ## The judgment is a fold (the census rule: every traversal is a fold)

`fold_of` (`Program/FoldOf.lean`) reads the hand recursion and emits its `TyAlgebra` with the
connector `Fits.eq_cata`, as it does for `Val.hasTy` (`Laws/Program/Folds/Ty.lean`). -/

fold_of Research.Pass.Membership.FitsInv

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
theorem fits_hasTy (w : W) (inv : Inv) : ∀ (ty : Ty) (v : Val), FitsInv w inv v ty →
    Val.hasTy v ty w.state.externals.allocated = true := by
  intro ty
  induction ty with
  | never => intro v h; exact h.elim
  | unit =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · rfl
    · exact h.elim
  | nat =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · rfl
    · exact h.elim
  | int => intro v h; exact h.elim
  | string =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · rfl
    · exact h.elim
  | bool =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · rfl
    · exact h.elim
  | handle target =>
    intro v h
    simp only [FitsInv] at h
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
    simp only [FitsInv] at h
    split at h
    · rfl
    · rename_i x
      simp only [Val.hasTy]
      exact ih x h
    · exact h.elim
  | list a ih =>
    intro v h
    simp only [FitsInv] at h
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
    simp only [FitsInv] at h
    split at h
    · rename_i x y
      simp only [Val.hasTy]
      exact Bool.and_eq_true_iff.mpr ⟨iha x h.1, ihb y h.2⟩
    · exact h.elim
  | except e a ihe iha =>
    intro v h
    simp only [FitsInv] at h
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
    simp only [FitsInv] at h
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
    simp only [FitsInv] at h
    split at h
    · rename_i c hc
      simp only [Val.hasTy, hc]
      exact causeFits_admits (fun x hx => ih x hx) c h
    · exact h.elim
  | fiberOf a e _ _ =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · rfl
    · exact h.elim
  | union l r ihl ihr =>
    intro v h
    simp only [FitsInv] at h
    simp only [Val.hasTy]
    exact Bool.or_eq_true_iff.mpr (h.imp (ihl v) (ihr v))
  | lit s =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · simp only [Val.hasTy]
      exact beq_iff_eq.mpr h
    · exact h.elim
  | refOf t _ =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · rfl
    · exact h.elim
  | deferredOf a e _ _ =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · rfl
    · exact h.elim
  | var _ => intro v h; exact h.elim
  | unknown => intro v _; rfl

#print axioms causeFits_admits
#print axioms fits_hasTy


/-! ## Declared liveness follows from membership -/

theorem live_of_keys_nil {w : W} {v : Val} (h : v.keys = []) : Live w v := by
  intro k hk
  rw [h] at hk
  cases hk

theorem live_list {w : W} {values : List Val} (h : ∀ x ∈ values, Live w x) :
    Live w (.list values) := by
  intro k hk
  rw [Val.keys_list, List.mem_flatMap] at hk
  obtain ⟨x, hx, hkx⟩ := hk
  exact h x hx k hkx

theorem live_ctor {w : W} {i : Nat} {args : List Val} (h : ∀ x ∈ args, Live w x) :
    Live w (.ctor i args) := by
  intro k hk
  have hk' : k ∈ Val.keysList args := hk
  rw [Val.keysList_eq_flatMap, List.mem_flatMap] at hk'
  obtain ⟨x, hx, hkx⟩ := hk'
  exact h x hx k hkx

theorem live_ctor_one {w : W} {i : Nat} {x : Val} (h : Live w x) : Live w (.ctor i [x]) :=
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

theorem live_fiber {w : W} {index : Nat} {a e : Ty} (h : FiberDeclared w ⟨index⟩ a e) :
    Live w (Value.fiber index) := by
  obtain ⟨fty, hΓ, _⟩ := h
  intro k hk
  have hk' : k ∈ (Val.fiber ⟨index⟩).keys := hk
  rw [Val.keys_fiber, List.mem_singleton] at hk'
  subst hk'
  show (w.Γ ⟨index⟩).isSome = true
  rw [hΓ]
  rfl

theorem live_cell {w : W} {inv : Inv} {index : Nat} {t : Ty} (h : RefDeclared w inv ⟨index⟩ t) :
    Live w (Value.cell index) := by
  obtain ⟨t', hΡ, _⟩ := h
  intro k hk
  have hk' : k ∈ (Val.cell ⟨index⟩).keys := hk
  rw [Val.keys_cell, List.mem_singleton] at hk'
  subst hk'
  show (w.Ρ ⟨index⟩).isSome = true
  rw [hΡ]
  rfl

theorem live_promise {w : W} {inv : Inv} {index : Nat} {a e : Ty}
    (h : PromiseDeclared w inv ⟨index⟩ a e) : Live w (Value.promise index) := by
  obtain ⟨a', e', hPi, _⟩ := h
  intro k hk
  have hk' : k ∈ (Val.promise ⟨index⟩).keys := hk
  rw [Val.keys_promise, List.mem_singleton] at hk'
  subst hk'
  show (w.«Π» ⟨index⟩).isSome = true
  rw [hPi]
  rfl

theorem live_handle {w : W} {inv : Inv} {kind : UInt8} {index : Nat} {target : String}
    (h : HandleFits w inv kind index target) : Live w (.handle kind index) := by
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
theorem fits_live (w : W) (inv : Inv) : ∀ (ty : Ty) (v : Val), FitsInv w inv v ty → Live w v := by
  intro ty
  induction ty with
  | never => intro v h; exact h.elim
  | unit =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | nat =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | int => intro v h; exact h.elim
  | string =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | bool =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | handle target =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact live_handle h
    · obtain ⟨_, _, _, _, hl⟩ := h
      exact hl
  | option a ih =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact live_of_keys_nil rfl
    · rename_i x
      exact ih x h
    · exact h.elim
  | list a ih =>
    intro v h
    simp only [FitsInv] at h
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
    simp only [FitsInv] at h
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
    simp only [FitsInv] at h
    split at h
    · exact live_ctor_one (ihe _ h)
    · exact live_ctor_one (iha _ h)
    · exact h.elim
  | exitOf a e iha _ =>
    intro v h
    simp only [FitsInv] at h
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
    simp only [FitsInv] at h
    split at h
    · rename_i c hc
      exact live_of_keys_nil (keys_of_cause hc)
    · exact h.elim
  | fiberOf a e _ _ =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact live_fiber h
    · exact h.elim
  | union l r ihl ihr =>
    intro v h
    simp only [FitsInv] at h
    exact h.elim (ihl v) (ihr v)
  | lit s =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact live_of_keys_nil rfl
    · exact h.elim
  | refOf t _ =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact live_cell h
    · exact h.elim
  | deferredOf a e _ _ =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact live_promise h
    · exact h.elim
  | var _ => intro v h; exact h.elim
  | unknown => intro v h; exact h

/-- Under `WorldValid`, declared liveness is exactly `HandlesLive` (store lengths). -/
theorem live_iff_handlesLive {rootTy : EffTy} {w : W} {m : RState} (valid : WorldValid rootTy w m)
    (v : Val) : Live w v ↔ HandlesLive w v := by
  constructor
  · intro h k hk
    have hk' := h k hk
    cases k with
    | cell key =>
      show key.index < w.state.refs.length
      rw [valid.state]
      exact (valid.heap key).mp hk'
    | promise key =>
      show key.index < w.state.deferreds.cells.length
      rw [valid.state]
      exact (valid.promises key).mp hk'
    | fiber id => exact hk'
    | scope _ => trivial
    | memoMap _ => trivial
    | external _ => trivial
  · intro h k hk
    have hk' := h k hk
    cases k with
    | cell key =>
      have hlt : key.index < m.state.refs.length := valid.state ▸ hk'
      exact (valid.heap key).mpr hlt
    | promise key =>
      have hlt : key.index < m.state.deferreds.cells.length := valid.state ▸ hk'
      exact (valid.promises key).mpr hlt
    | fiber id => exact hk'
    | scope _ => trivial
    | memoMap _ => trivial
    | external _ => trivial

#print axioms fits_live
#print axioms live_iff_handlesLive


/-! ## One transport lemma: world extension and a weaker invariance reading together -/

theorem isSome_extends {K A : Type} {t1 t2 : K → Option A} (ht : TableExtends t1 t2) {k : K}
    (h : (t1 k).isSome = true) : (t2 k).isSome = true := by
  cases hs : t1 k with
  | none => rw [hs] at h; cases h
  | some a => rw [ht k a hs]; rfl

section Map
variable {w1 w2 : W} {inv1 inv2 : Inv}
  (hΓ : TableExtends w1.Γ w2.Γ) (hPi : TableExtends w1.«Π» w2.«Π») (hRho : TableExtends w1.Ρ w2.Ρ)
  (halloc : Extends w1.state.externals.allocated w2.state.externals.allocated)
  (hinv : ∀ a b, inv1 a b → inv2 a b)
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

include hinv in
omit hΓ hPi in
theorem refDeclared_map {key : RefKey} {t : Ty} (h : RefDeclared w1 inv1 key t) :
    RefDeclared w2 inv2 key t := by
  obtain ⟨t', hs, hi⟩ := h
  exact ⟨t', hRho key t' hs, hinv _ _ hi⟩

include hinv in
omit hΓ hRho in
theorem promiseDeclared_map {key : DeferredKey} {a e : Ty} (h : PromiseDeclared w1 inv1 key a e) :
    PromiseDeclared w2 inv2 key a e := by
  obtain ⟨a', e', hs, ha, he⟩ := h
  exact ⟨a', e', hPi key (a', e') hs, hinv _ _ ha, hinv _ _ he⟩

include halloc hinv in
omit hΓ in
theorem handleFits_map {kind : UInt8} {index : Nat} {target : String}
    (h : HandleFits w1 inv1 kind index target) : HandleFits w2 inv2 kind index target := by
  simp only [HandleFits] at h ⊢
  split at h
  · exact ⟨h.1, refDeclared_map hRho hinv h.2⟩
  · exact ⟨h.1, promiseDeclared_map hPi hinv h.2⟩
  · exact h
  · exact ⟨h.1, halloc index target h.2⟩
  · exact h.elim

include halloc hinv in
omit hΓ in
theorem flatFits_map {v : Val} {t : Ty} (h : FlatFits w1 inv1 v t) : FlatFits w2 inv2 v t := by
  cases t
  case unit => exact h
  case nat => exact h
  case bool => exact h
  case string => exact h
  case handle target =>
    simp only [FlatFits] at h ⊢
    split at h
    · exact handleFits_map hPi hRho halloc hinv h
    · exact h.elim
  all_goals exact h.elim

include halloc hinv in
omit hΓ in
theorem servicesFit_map {services : Env.Ctx} (h : ServicesFit w1 inv1 services) :
    ServicesFit w2 inv2 services :=
  fun key sv sty hget hty => flatFits_map hPi hRho halloc hinv (h key sv sty hget hty)

end Map

/-- **Transport.** Membership moves to a world whose tables and allocation spellings extend the
old ones, and from a stronger invariance reading to a weaker one. -/
theorem fitsInv_map {w1 w2 : W} {inv1 inv2 : Inv}
    (hΓ : TableExtends w1.Γ w2.Γ) (hPi : TableExtends w1.«Π» w2.«Π») (hRho : TableExtends w1.Ρ w2.Ρ)
    (halloc : Extends w1.state.externals.allocated w2.state.externals.allocated)
    (hinv : ∀ a b, inv1 a b → inv2 a b) :
    ∀ (ty : Ty) (v : Val), FitsInv w1 inv1 v ty → FitsInv w2 inv2 v ty := by
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
    simp only [FitsInv] at h
    split at h
    · exact handleFits_map hPi hRho halloc hinv h
    · obtain ⟨ht, ctx, hctx, hs, hl⟩ := h
      simp only [FitsInv]
      exact ⟨ht, ctx, hctx, servicesFit_map hPi hRho halloc hinv hs, live_map hΓ hPi hRho hl⟩
  | option a ih =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · trivial
    · rename_i x
      exact ih x h
    · exact h.elim
  | list a ih =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        simp only [FitsInv, hids]
        exact fun id hid => ih _ (h id hid)
      · exact h.elim
    · rename_i values
      exact fun x hx => ih x (h x hx)
    · exact h.elim
  | prod a b iha ihb =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact ⟨iha _ h.1, ihb _ h.2⟩
    · exact h.elim
  | except e a ihe iha =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact ihe _ h
    · exact iha _ h
    · exact h.elim
  | exitOf a e iha ihe =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact iha _ h
    · rename_i written
      split at h
      · rename_i c hc
        simp only [FitsInv, hc]
        exact causeFits_map (fun x hx => ihe x hx) h
      · exact h.elim
    · exact h.elim
  | causeOf e ih =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · rename_i c hc
      simp only [FitsInv, hc]
      exact causeFits_map (fun x hx => ih x hx) h
    · exact h.elim
  | fiberOf a e _ _ =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact fiberDeclared_map hΓ h
    · exact h.elim
  | union l r ihl ihr =>
    intro v h
    exact h.imp (ihl v) (ihr v)
  | lit s => intro v h; exact h
  | refOf t _ =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact refDeclared_map hRho hinv h
    · exact h.elim
  | deferredOf a e _ _ =>
    intro v h
    simp only [FitsInv] at h
    split at h
    · exact promiseDeclared_map hPi hinv h
    · exact h.elim
  | var _ => intro v h; exact h.elim
  | unknown => intro v h; exact live_map hΓ hPi hRho h

/-- **Monotonicity under the host order** (the statement `M3bWorld.strongValue_mono` declares for
`StrongValue`, `Typed/Residual.lean:424-425`, a `#proof_wanted` at `:456`). -/
theorem fits_mono {w w' : W} (ordered : w.leHost w') {ty : Ty} {v : Val} (h : Fits w v ty) :
    Fits w' v ty :=
  fitsInv_map ordered.1.2.1 ordered.1.2.2.1 ordered.1.2.2.2.1 ordered.2 (fun _ _ hi => hi) ty v h

/-- The equality reading is stronger than the `Ty.sub` reading. -/
theorem fitsEq_fits {w : W} {ty : Ty} {v : Val} (h : FitsEq w v ty) : Fits w v ty :=
  fitsInv_map (table_refl _) (table_refl _) (table_refl _) (fun _ _ hi => hi)
    (fun a b hab => by
      subst hab
      exact ⟨Ty.sub_refl a, Ty.sub_refl a⟩) ty v h

#print axioms fitsInv_map
#print axioms fits_mono
#print axioms fitsEq_fits

/-! ## Subsumption: membership respects the checker's subtyping -/

/-- **Fits is closed under `Ty.sub`.** By `fun_induction Ty.sub`, so the cases are `sub`'s own arms
(as `cata_admits_sub`, `Laws/Program/Admits.lean:36`). The invariant arms use `Ty.sub_trans`. -/
theorem fits_sub (w : W) {a b : Ty} (hsub : Ty.sub a b = true) : ∀ v, Fits w v a → Fits w v b := by
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
  case case5 => intro v h; exact fits_live w Equiv _ v h
  case case6 =>
    intro v h
    simp only [Fits, FitsInv] at h
    split at h
    · trivial
    · exact h.elim
  case case7 x y _ ih =>
    intro v h
    simp only [Fits, FitsInv] at h
    split at h
    · trivial
    · rename_i z
      exact ih hsub z h
    · exact h.elim
  case case8 x y _ ih =>
    intro v h
    simp only [Fits, FitsInv] at h
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        simp only [Fits, FitsInv, hids]
        exact fun id hid => ih hsub _ (h id hid)
      · exact h.elim
    · exact fun z hz => ih hsub z (h z hz)
    · exact h.elim
  case case9 a1 a2 b1 b2 _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits, FitsInv] at h
    split at h
    · exact ⟨iha h1 _ h.1, ihb h2 _ h.2⟩
    · exact h.elim
  case case10 e1 a1 e2 a2 _ ihe iha =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits, FitsInv] at h
    split at h
    · exact ihe h1 _ h
    · exact iha h2 _ h
    · exact h.elim
  case case11 a1 e1 a2 e2 _ iha ihe =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits, FitsInv] at h
    split at h
    · exact iha h1 _ h
    · rename_i written
      split at h
      · rename_i c hc
        simp only [Fits, FitsInv, hc]
        exact causeFits_map (fun x hx => ihe h2 x hx) h
      · exact h.elim
    · exact h.elim
  case case12 e1 e2 _ ih =>
    intro v h
    simp only [Fits, FitsInv] at h
    split at h
    · rename_i c hc
      simp only [Fits, FitsInv, hc]
      exact causeFits_map (fun x hx => ih hsub x hx) h
    · exact h.elim
  case case13 a1 e1 a2 e2 _ _ _ =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits, FitsInv] at h
    split at h
    · obtain ⟨fty, hs, ha, he⟩ := h
      exact ⟨fty, hs, Ty.sub_trans _ _ _ ha h1, Ty.sub_trans _ _ _ he h2⟩
    · exact h.elim
  case case14 a1 a2 _ _ _ =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits, FitsInv] at h
    split at h
    · obtain ⟨t', hs, hl, hr⟩ := h
      exact ⟨t', hs, Ty.sub_trans _ _ _ hl h1, Ty.sub_trans _ _ _ h2 hr⟩
    · exact h.elim
  case case15 a1 e1 a2 e2 _ _ _ _ _ =>
    obtain ⟨h123, h4⟩ := Bool.and_eq_true_iff.mp hsub
    obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp h123
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
    intro v h
    simp only [Fits, FitsInv] at h
    split at h
    · obtain ⟨a', e', hs, ⟨ha1, ha2⟩, ⟨he1, he2⟩⟩ := h
      exact ⟨a', e', hs, ⟨Ty.sub_trans _ _ _ ha1 h1, Ty.sub_trans _ _ _ h2 ha2⟩,
        ⟨Ty.sub_trans _ _ _ he1 h3, Ty.sub_trans _ _ _ h4 he2⟩⟩
    · exact h.elim
  case case16 => exact Bool.noConfusion hsub

#print axioms fits_sub


/-! ## The connection to `StrongValue`

Under `WorldValid`, the equality reading `FitsEq` implies the old judgment, all three conjuncts.
With the `Ty.sub` reading the implication fails only at invariant handles declared at an
equivalent but different spelling (`Gaps.lean`'s `equivalent_spelling`). -/

theorem fitsEq_handlesFit {rootTy : EffTy} {w : W} {m : RState} (valid : WorldValid rootTy w m) :
    ∀ (ty : Ty) (v : Val), FitsEq w v ty → HandlesFit w v ty := by
  intro ty
  induction ty with
  | never => intro v h; exact h.elim
  | unit => intro v _; trivial
  | nat => intro v _; trivial
  | int => intro v _; trivial
  | string => intro v _; trivial
  | bool => intro v _; trivial
  | handle target =>
    intro v h
    simp only [FitsEq, FitsInv] at h
    intro _ ctx hctx
    split at h
    · exact nomatch hctx
    · obtain ⟨_, ctx0, hctx0, hs, _⟩ := h
      rw [hctx0] at hctx
      cases hctx
      intro key sv sty hget hty
      have hf : FitsInv w (· = ·) sv sty := flatFits_fitsInv (hs key sv sty hget hty)
      exact ⟨fits_hasTy w _ sty sv hf, (live_iff_handlesLive valid sv).mp (fits_live w _ sty sv hf)⟩
  | option a ih =>
    intro v h
    simp only [FitsEq, FitsInv] at h
    split at h
    · trivial
    · rename_i x
      exact ih x h
    · exact h.elim
  | list a ih =>
    intro v h
    simp only [FitsEq, FitsInv] at h
    split at h
    · trivial
    · rename_i values
      exact fun x hx => ih x (h x hx)
    · exact h.elim
  | prod a b _ _ =>
    intro v h
    simp only [FitsEq, FitsInv] at h
    split at h
    · trivial
    · exact h.elim
  | except e a _ _ => intro v _; trivial
  | exitOf a e _ _ => intro v _; trivial
  | causeOf e _ => intro v _; trivial
  | fiberOf a e _ _ =>
    intro v h
    simp only [FitsEq, FitsInv] at h
    split at h
    · rename_i index
      intro id hid
      have hid' : Handle.fiber id ∈ (Val.fiber ⟨index⟩).keys := hid
      rw [Val.keys_fiber, List.mem_singleton] at hid'
      cases hid'
      exact h
    · exact h.elim
  | union l r ihl ihr =>
    intro v h
    exact h.imp (ihl v) (ihr v)
  | lit _ => intro v _; trivial
  | refOf t _ =>
    intro v h
    simp only [FitsEq, FitsInv] at h
    split at h
    · rename_i index
      intro key hkey
      have hk' : Handle.cell key ∈ (Val.cell ⟨index⟩).keys := hkey
      rw [Val.keys_cell, List.mem_singleton] at hk'
      cases hk'
      obtain ⟨t', hs, rfl⟩ := h
      exact hs
    · exact h.elim
  | deferredOf a e _ _ =>
    intro v h
    simp only [FitsEq, FitsInv] at h
    split at h
    · rename_i index
      intro key hkey
      have hk' : Handle.promise key ∈ (Val.promise ⟨index⟩).keys := hkey
      rw [Val.keys_promise, List.mem_singleton] at hk'
      cases hk'
      obtain ⟨a', e', hs, rfl, rfl⟩ := h
      exact hs
    · exact h.elim
  | var _ => intro v h; exact h.elim
  | unknown => intro v h; exact (live_iff_handlesLive valid v).mp h

/-- **The equality reading implies the old judgment** under world validity. -/
theorem fitsEq_strongValue {rootTy : EffTy} {w : W} {m : RState} (valid : WorldValid rootTy w m)
    {ty : Ty} {v : Val} (h : FitsEq w v ty) : StrongValue w ty v :=
  ⟨fits_hasTy w _ ty v h, fitsEq_handlesFit valid ty v h,
    (live_iff_handlesLive valid v).mp (fits_live w _ ty v h)⟩

#print axioms fitsEq_handlesFit
#print axioms fitsEq_strongValue


/-! ## Exit monotonicity is value monotonicity

An exit is a value (`FitsExit` is `Fits` at the reified exit), so the second declared world
obligation, `M3bWorld.strongExit_mono` (`Typed/Residual.lean:427-428`, `#proof_wanted`), is
`fits_mono` at one type. -/

theorem fitsExit_mono {w w' : W} (ordered : w.leHost w') {ty : EffTy} {ex : ExitV}
    (h : FitsExit w ty ex) : FitsExit w' ty ex :=
  fits_mono ordered h

/-- Exit subsumption, column by column. -/
theorem fitsExit_sub {w : W} {ty ty' : EffTy} (ha : Ty.sub ty.answer ty'.answer = true)
    (he : Ty.sub ty.error ty'.error = true) {ex : ExitV} (h : FitsExit w ty ex) :
    FitsExit w ty' ex := by
  cases ex with
  | success v =>
    rw [fitsExit_success_iff] at h ⊢
    exact fits_sub w ha v h
  | failure c =>
    rw [fitsExit_failure_iff] at h ⊢
    exact causeFits_map (fun x hx => fits_sub w he x hx) h

/-! ## The pair program's steps (`host-answers-evidence/PathProbes.lean` §D)

What M6 needs to type `pair`, `fst` and the await, proved for `Fits`. `Gaps.lean`'s
`strongValue_no_fst` shows the `fst` step has no `StrongValue` counterpart. -/

/-- The pair atom's value (`NativeAtom.eval .pair`, `Machine/Term.lean:374`) fits the product. -/
theorem fits_pair {w : W} {x y : Val} {a b : Ty} (hx : Fits w x a) (hy : Fits w y b) :
    Fits w (.list [x, y]) (.prod a b) :=
  ⟨hx, hy⟩

/-- `fst` (`Machine/Term.lean:375`) keeps the first column's fit, handle declarations included. -/
theorem fits_fst {w : W} {v r : Val} {a b : Ty} (h : Fits w v (.prod a b))
    (hr : NativeAtom.eval .fst [v] = some r) : Fits w r a := by
  simp only [Fits, FitsInv] at h
  split at h
  · rename_i x y
    have hx : NativeAtom.eval .fst [.list [x, y]] = some x := rfl
    rw [hx] at hr
    cases hr
    exact h.1
  · exact h.elim

/-- Awaiting a fiber whose handle fits `fiberOf a e`: whatever exit the await answers at the
fiber's declared type in a later world (`fiberPost (.await _ .joinEffect)`,
`Typed/Residual.lean:154`) fits `(a, e)`. -/
theorem await_fits {w w' : W} {id : FiberId} {a e : Ty} {ty : EffTy} {ex : ExitV}
    (h : Fits w (Val.fiber id) (.fiberOf a e)) (ordered : w.leHost w')
    (declared : w'.Γ id = some ty) (hex : FitsExit w' ty ex) (req : Env.Requirement) :
    FitsExit w' ⟨a, e, req⟩ ex := by
  obtain ⟨fty, hs, ha, he⟩ := h
  have hs' := ordered.1.2.1 id fty hs
  rw [declared] at hs'
  cases hs'
  exact fitsExit_sub ha he hex

#print axioms fitsExit_mono
#print axioms fitsExit_sub
#print axioms fits_pair
#print axioms fits_fst
#print axioms await_fits


/-! ## The list arm reads one decoded element view

The contract's §4 `list` row asks for one shared decoded element view for ordinary lists and
admitted snapshots. `Val.asList?` (`Machine/Alphabets.lean:239`) is that view, and the list arm
is exactly membership of every element it decodes. -/

theorem fits_list_iff (w : W) (v : Val) (a : Ty) :
    Fits w v (.list a) ↔ ∃ xs, Val.asList? v = some xs ∧ ∀ x ∈ xs, Fits w x a := by
  constructor
  · intro h
    simp only [Fits, FitsInv] at h
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
    simp only [Fits, FitsInv]
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

#print axioms fits_list_iff

/-! ## Proof search with the `Effect4.TypedState` bank (task 4's measurement)

Four goals the migration produces, each closed by `aesop` over the bank. The first needs the
bank (`insert_extends`, `Typed/World.lean:764`): its red control makes no progress without it.
The third is `fits_mono` from its statement, given the one transport lemma as a rule. -/

theorem search_heap_extends (w : W) (cert : Ty) (hRho : w.Ρ ⟨0⟩ = none) :
    TableExtends w.Ρ (w.addRef w.state ⟨0⟩ cert).Ρ := by
  aesop (rule_sets := [Effect4.TypedState])

/-- Red control: without the bank the same search makes no progress. -/
example (w : W) (cert : Ty) (hRho : w.Ρ ⟨0⟩ = none) :
    TableExtends w.Ρ (w.addRef w.state ⟨0⟩ cert).Ρ := by
  fail_if_success aesop
  exact insert_extends _ _ _ hRho

theorem search_fiberDeclared_mono {w w' : W} (ordered : w.leHost w') {id : FiberId} {a e : Ty}
    (h : FiberDeclared w id a e) : FiberDeclared w' id a e := by
  aesop (add norm unfold [FiberDeclared, Effect4.Program.Typed.World.leHost,
    Effect4.Program.Typed.World.le]) (rule_sets := [Effect4.TypedState])

theorem search_fits_mono {w w' : W} (ordered : w.leHost w') {ty : Ty} {v : Val}
    (h : Fits w v ty) : Fits w' v ty := by
  aesop (add unsafe apply fitsInv_map)
    (add norm unfold [Effect4.Program.Typed.World.leHost, Effect4.Program.Typed.World.le])
    (rule_sets := [Effect4.TypedState])

/-- The value half of `settling_fork` (`Typed/Residual.lean:358`), found by search. -/
theorem search_fork_value {w : W} {id : FiberId} {cert : EffTy} (hid : w.Γ id = some cert) :
    FitsExit w (EffTy.pure (.fiberOf cert.answer cert.error)) (.success (Val.fiber id)) := by
  aesop (add norm unfold [FitsExit, Fits, FiberDeclared, reifyExitVal, EffTy.pure])
    (add norm simp [FitsInv, Ty.sub_refl]) (rule_sets := [Effect4.TypedState])

#print axioms search_heap_extends
#print axioms search_fiberDeclared_mono
#print axioms search_fits_mono
#print axioms search_fork_value

end Research.Pass.Membership
