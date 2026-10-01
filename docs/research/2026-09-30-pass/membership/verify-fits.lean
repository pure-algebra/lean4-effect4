import Effect4.Laws.Program.Typed.Assembly
import Effect4.Program.FoldOf

/-!
# Verifier probe: the proposed `Fits` on the allocation programs, up to the typed state

Adversarial verifier of seat MEMBERSHIP, 2026-09-30 pass. Base `be15b062`.

`verify-load.lean` proves that under today's `StrongValue`, `typedState_load` fails for
`Ref.make(5)`, for `Deferred.make()`, and for `Ref.make(5).flatMap(r => Ref.get(r))`, because
`bind`'s guard `unguard`s the fresh cell. The seat's `refProg_typedF` shows only that the loaded
code of `Ref.make(5)` is typed under `Fits`. This file asks the full question of the seat's
proposed judgment: is the M5 instance itself true, with the restated typed state?

Research files cannot import each other, so the seat's definitions are copied verbatim, by
exact line range (marked below; the assembled copy hashes to `19e38861d0d5b919`, sha256, first
16 hex digits). Nothing in the copied ranges is edited. The new declarations are in the last
two sections.
-/

set_option autoImplicit false

namespace Research.Pass.Membership.VerifyFits
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched
open Effect4.Program.Denote Effect4.Laws.Effects Contracts

-- copied: Fits.lean:24-218 (the shared block)
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

-- copied: Fits.lean:403-627 (declared liveness, fits_live)
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

-- copied: Fits.lean:866-972 (fits_sub)
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

-- copied: Walk.lean:219-543 (the restated program judgment, inversions, hook protocols)
/-! ## The two names the restated declarations read -/

/-- The old argument order, so the restated statements keep their spelling. -/
abbrev StrongValueF (w : W) (ty : Ty) (v : Val) : Prop := Fits w v ty

/-- The context's services at the `Ty.sub` reading. -/
abbrev ServicesFitE (w : W) (services : Env.Ctx) : Prop := ServicesFit w Equiv services

/-! ## The restated declarations (baseline segments, edited) -/

-- src/Effect4/Laws/Program/Typed/Admission.lean:77-80
/-- An evaluation environment typed pointwise at the corresponding static types. -/
def EnvTypedF (w : W) (env : List Ty) (vals : List Val) : Prop :=
  env.length = vals.length ∧
  ∀ (i : Nat) (ty : Ty) (v : Val), env[i]? = some ty → vals[i]? = some v → StrongValueF w ty v

-- src/Effect4/Laws/Program/Typed/Admission.lean:90-119
/-- D13 source admission at an addressed program node, under the source's row table
(`E4-SCHED-CE-014`: the empty table refused bodies that perform a host row). -/
def PointTypedF (src : ProgramSource) (w : W) (point : Point) (ty : EffTy) : Prop :=
  ∃ (e : NativeEff) (env : List Ty),
    Node.at_ (.eff src.program) point.path = some (.eff e) ∧
    Checker.check (nativeSignature src.table) env point.path e = .ok ty ∧
    EnvTypedF w env point.env

/-- Admitted bodies covering all six `Body` constructors. -/
inductive BodyTypedF (src : ProgramSource) (w : W) : Body → EffTy → Prop
  | at_ (p : Point) (ty : EffTy) (h : PointTypedF src w p ty) :
      BodyTypedF src w (.at_ p) ty
  | fin (name : FinName) (ex : ExitV) (ty : EffTy) (hex : FitsExit w ty ex) :
      BodyTypedF src w (.fin name ex) ty
  | raceCleanup (race : Nat) :
      BodyTypedF src w (.raceCleanup race) (EffTy.pure .unit)
  | acquireIn (p : Point) (ctx : Ctx) (ty : EffTy) (h : PointTypedF src w p ty) :
      BodyTypedF src w (.acquireIn p ctx) ty
  | release (p : Point) (prev : Ctx) (ty : EffTy) (h : PointTypedF src w p ty) :
      BodyTypedF src w (.release p prev) ty
  | layerBuild (p : Point) (m : MemoMapId) (scope : Nat) (ty : EffTy) (h : PointTypedF src w p ty) :
      BodyTypedF src w (.layerBuild p m scope) ty

/-- A strong value at the answer column is a strong successful exit. -/
theorem fitsExit_success (w : W) (ty : EffTy) (v : Val) (h : StrongValueF w ty.answer v) :
    FitsExit w ty (.success v) := h

-- src/Effect4/Laws/Program/Typed/Admission.lean:127-168
/-- A clean failure fits every effect type at every world: the error column constrains
`Fail` reasons only. -/
theorem fitsExit_of_clean (w : W) (ty : EffTy) (c : CauseV)
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

/-- At a `never` error column a strong failure is clean: no value has type `never`. -/
theorem cleanExit_of_never_fits (w : W) (ty : EffTy) (c : CauseV) (never : ty.error = .never)
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

-- src/Effect4/Laws/Program/Typed/Residual.lean:34-86
def storePreF (root : ProgramSource) (w : W) (op : SyncOp) (cert : StoreCert op) : Prop :=
  match op with
  | .refMake initial => cert.closed = true ∧ StrongValueF w cert initial
  | .refGet cell => ∃ ty, w.Ρ cell = some ty
  | .refSet cell v => ∃ ty, w.Ρ cell = some ty ∧ StrongValueF w ty v
  | .refGetAndSet cell v => ∃ ty, w.Ρ cell = some ty ∧ StrongValueF w ty v
  | .refSetAndGet cell v => ∃ ty, w.Ρ cell = some ty ∧ StrongValueF w ty v
  | .refUpdate cell _ | .refGetAndUpdate cell _ | .refUpdateAndGet cell _
  | .refUpdateSome cell _ | .refGetAndUpdateSome cell _ | .refUpdateSomeAndGet cell _
  | .refModify cell _ | .refModifySome cell _ => ∃ ty, w.Ρ cell = some ty
  | .deferredMake => cert.1.closed = true ∧ cert.2.closed = true
  | .deferredIsDone key | .deferredPoll key | .deferredAwaitCleanup key _ _ => (w.«Π» key).isSome = true
  | .deferredCompleteWith key _ => (w.«Π» key).isSome = true
  | .deferredInterruptWith key _ => (w.«Π» key).isSome = true
  | .clockNow | .sleepCancel _ _ => True
  | .scopeMake _ | .scopeAdd _ _ | .scopeRemove _ _ | .scopeIsClosed _ | .scopeFork _ _ => True
  | .memoFork _ | .memoComplete _ _ _ | .memoRelease _ _ => True
  -- the looked-up layer's own checked error type (decision row 90)
  | .memoGet layer _ => ∃ l lt, Node.at_ (.eff root.program) layer = some (.layer l) ∧
      Checker.checkLayer (nativeSignature root.table) layer l = .ok lt ∧ lt.error = cert
  | .memoBuild _ _ => cert.1.closed = true ∧ cert.2.closed = true

def storePostF (w' : W) (op : SyncOp) (cert : StoreCert op) (ans : Val) : Prop :=
  match op with
  | .refMake _ => ∃ key : RefKey, ans = Val.cell key ∧ w'.Ρ key = some cert
  | .refGet cell => ∃ ty, w'.Ρ cell = some ty ∧ StrongValueF w' ty ans
  | .refSet cell _ => ans = Val.cell cell
  | .refGetAndSet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValueF w' ty ans
  | .refSetAndGet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValueF w' ty ans
  | .refUpdate _ _ | .refUpdateSome _ _ => ans = Val.unit
  | .refGetAndUpdate cell _ | .refGetAndUpdateSome cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValueF w' ty ans
  | .refUpdateAndGet cell _ | .refUpdateSomeAndGet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValueF w' ty ans
  | .refModify _ _ | .refModifySome _ _ => ∃ n, ans = Val.nat n
  | .deferredMake => ∃ key : DeferredKey, ans = Val.promise key ∧ w'.«Π» key = some cert
  | .deferredIsDone _ => ∃ b, ans = Val.bool b
  | .deferredPoll _ => ∃ b, ans = Val.bool b
  | .deferredCompleteWith _ _ | .deferredInterruptWith _ _ | .deferredAwaitCleanup _ _ _ => ∃ b, ans = Val.bool b
  | .clockNow => ∃ n, ans = Val.nat n
  | .sleepCancel _ _ => ans = Val.unit
  | .scopeMake _ => ∃ sc, ans = Val.scopeHandle sc
  | .scopeAdd _ _ | .scopeRemove _ _ => ∃ b, ans = Val.bool b
  | .scopeIsClosed _ => ∃ b, ans = Val.bool b
  | .scopeFork _ _ => ∃ sc, ans = Val.scopeHandle sc
  | .memoFork _ => ∃ id, ans = Val.memoMap id
  | .memoGet _ _ => ans = Val.unit ∨ ∃ cell owner, Val.memoHit? ans = some (cell, owner) ∧
      w'.«Π» cell = some (.handle Ty.contextTarget, cert)
  | .memoBuild _ _ => ∃ sc, ans = Val.scopeHandle sc
  | .memoComplete _ _ _ | .memoRelease _ _ => ans = Val.unit

def Ψ_SF (root : ProgramSource) : Protocol W StoreSig where
  Cert := StoreCert
  pre := storePreF root
  post := storePostF

-- src/Effect4/Laws/Program/Typed/Residual.lean:116-259
def fiberPreF (root : ProgramSource) (w : W) (op : FiberOp) (cert : FiberCert op) : Prop :=
  match op with
  | .getId | .yieldNow _ | .ambientScope | .sync _ => True
  -- the context set keeps every service at its key's type (decision row 90)
  | .setContext ctx => ServicesFitE w ctx.services
  | .getContext => cert = .handle Ty.contextTarget
  | .await target _ => (w.Γ target).isSome = true
  | .awaitAll targets | .awaitAllFailFast targets =>
    ∃ a e, cert = .list (.exitOf a e) ∧ ∀ t ∈ targets, ∃ fty, w.Γ t = some fty ∧
      fty.answer.sub a = true ∧ fty.error.sub e = true
  | .raceAll entrants _ => ∀ p ∈ entrants, ∃ ty, PointTypedF root w p ty ∧
      ty.answer.sub cert.answer = true ∧ ty.error.sub cert.error = true
  | .async register _ => asyncPre root w register cert
  | .suspend _ | .interrupt _ | .interruptAs _ _ | .interruptScoped _ | .interruptAll _ _
  | .runIn _ _ | .awaitNewChildren _ => True
  | .guard_ _ | .unguard _ | .finishFinalizer _ | .scopeExit _ _ _ | .construction
  | .closeScope _ _ | .foreignRelease _ _ | .closeWalk _ _ _ | .closeIter _ _ _
  | .raceRegister _ | .cancelRace _ | .dropObservers _ | .frontier _ _ => True
  | .snapshotChildren => cert = .list (.fiberOf .unknown .unknown)
  | .scoped body => PointTypedF root w body cert
  | .mask _ body => BodyTypedF root w body cert
  | .forkScoped child _ _ => PointTypedF root w child cert
  | .fork body _ _ => BodyTypedF root w body cert
  | .forkIn child _ _ _ => PointTypedF root w child cert
  | .gen p => PointTypedF root w p cert
  | .loop p _ => PointTypedF root w p cert
  | .refuse _ => False

def fiberPostF (w' : W) (op : FiberOp) (cert : FiberCert op) (ans : op.answer) : Prop :=
  match op with
  | .getId => ∃ (id : FiberId), ans = Val.nat id.value
  | .getContext | .awaitAll _ | .awaitAllFailFast _ | .snapshotChildren => StrongValueF w' cert ans
  | .setContext _ | .yieldNow _ | .interrupt _ | .interruptAs _ _ | .interruptScoped _
  | .interruptAll _ _ | .runIn _ _ | .cancelRace _ | .dropObservers _
  | .foreignRelease _ _ | .closeWalk _ _ _ | .awaitNewChildren _ => ans = Val.unit
  | .ambientScope => ∃ sc, ans = Val.scopeHandle sc
  | .sync value => ans = value
  | .await target mode => match mode with
    | .joinEffect => ∃ ty, w'.Γ target = some ty ∧ FitsExit w' ty ans
    | .awaitValue => ∃ ty, w'.Γ target = some ty ∧ StrongValueF w' ty.answer ans
  | .fork _ _ _ | .forkIn _ _ _ _ => ∃ id : FiberId, ans = Val.fiber id ∧ w'.Γ id = some cert
  | .forkScoped _ _ _ => ∃ id : FiberId, ans = .success (Val.fiber id) ∧ w'.Γ id = some cert
  | .mask _ _ | .scoped _ | .raceAll _ _ | .raceRegister _ | .async _ _ | .gen _ | .loop _ _ =>
    FitsExit w' cert ans
  | .unguard ex | .finishFinalizer ex | .closeScope _ ex | .scopeExit _ _ ex | .closeIter _ _ ex => ans = ex
  | .guard_ kind => match ans with
    | none => True
    | some ex => kind.hasExitArm ex = true ∧ FitsExit w' cert ex
  -- a live frontier is never answered (fuel exhaustion is not an exit)
  | .frontier _ _ => False
  -- the completed exits a callback reads, each at its fiber's declared type
  | .construction => ∀ p ∈ ans, ∃ ty, w'.Γ p.1 = some ty ∧ FitsExit w' ty p.2
  | .suspend _ | .refuse _ => True

def Ψ_FF (root : ProgramSource) : Protocol W FiberSig where
  Cert := FiberCert
  pre := fiberPreF root
  post := fiberPostF

/-! ## The program judgment -/

/-- The one typing of a reference program at an effect type. Store and fiber operations follow
`Ψ_SF` and `Ψ_FF`: a certificate, its precondition, and a continuation for every answer the
postcondition admits at every later world. The fiber arm excludes the four control markers,
which have their own arms. A guard's body is typed at the guard's certified intermediate type
`mid`; the saved arm runs on the exits the guard row admits at `mid`, and an exit the arm does
not take must fit the outer type. `unguard` and `finishFinalizer` carry an exit at the current
type and type no continuation: the reference machine never resumes one (`evaluateFiberR`
hands the payload to `deliverR`; `popR`'s answer glue passes it to the next frame).
`scopeExit` carries its exit and keeps its continuation. -/
inductive TypedProgF (root : ProgramSource) : W → EffTy → RProgram → Prop
  | pure {w : W} {ty : EffTy} {ex : ExitV} (exit : FitsExit w ty ex) :
      TypedProgF root w ty (.pure ex)
  | store {w : W} {ty : EffTy} {op : SyncOp} {k : Val → RProgram}
      (cert : (Ψ_SF root).Cert op) (pre : (Ψ_SF root).pre w op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, (Ψ_SF root).post w' op cert ans → TypedProgF root w' ty (k ans)) :
      TypedProgF root w ty (.vis (.inl op) k)
  | fiber {w : W} {ty : EffTy} {op : FiberOp} {k : op.answer → RProgram}
      (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ ex, op ≠ .unguard ex)
      (notFinish : ∀ ex, op ≠ .finishFinalizer ex)
      (notScopeExit : ∀ prev sc ex, op ≠ .scopeExit prev sc ex)
      (cert : (Ψ_FF root).Cert op) (pre : (Ψ_FF root).pre w op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, (Ψ_FF root).post w' op cert ans →
        TypedProgF root w' ty (k ans)) :
      TypedProgF root w ty (.vis (.inr op) k)
  | guard {w : W} {ty : EffTy} {kind : GuardKind} {k : Option ExitV → RProgram}
      (mid : EffTy) (body : TypedProgF root w mid (k none))
      (run : ∀ w', w.leHost w' → ∀ ex, fiberPostF w' (.guard_ kind) mid (some ex) →
        TypedProgF root w' ty (k (some ex)))
      (skip : ∀ w', w.leHost w' → ∀ ex, FitsExit w' mid ex → kind.hasExitArm ex = false →
        FitsExit w' ty ex) :
      TypedProgF root w ty (.vis (.inr (.guard_ kind)) k)
  | unguard {w : W} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : FitsExit w ty ex) : TypedProgF root w ty (.vis (.inr (.unguard ex)) k)
  | finishFinalizer {w : W} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : FitsExit w ty ex) : TypedProgF root w ty (.vis (.inr (.finishFinalizer ex)) k)
  | scopeExit {w : W} {ty : EffTy} {prev : Ctx} {sc : Nat} {ex : ExitV} {k : ExitV → RProgram}
      (payload : FitsExit w ty ex)
      (next : ∀ w', w.leHost w' → ∀ ans, TypedProgF root w' ty (k ans)) :
      TypedProgF root w ty (.vis (.inr (.scopeExit prev sc ex)) k)

namespace TypedProgF

theorem pure_inv {root : ProgramSource} {w : W} {ty : EffTy} {ex : ExitV}
    (h : TypedProgF root w ty (.pure ex)) : FitsExit w ty ex := by
  cases h with
  | pure exit => exact exit

theorem store_inv {root : ProgramSource} {w : W} {ty : EffTy} {op : SyncOp} {k : Val → RProgram}
    (h : TypedProgF root w ty (.vis (.inl op) k)) :
    ∃ cert : (Ψ_SF root).Cert op, (Ψ_SF root).pre w op cert ∧
      ∀ w', w.leHost w' → ∀ ans, (Ψ_SF root).post w' op cert ans → TypedProgF root w' ty (k ans) := by
  cases h with
  | store cert pre next => exact ⟨cert, pre, next⟩

/-- A guard's typing is exactly the saved frame's arrow (`Contracts.FrameAccepts.resume`) at
`mid`, with the body typed at `mid`. -/
theorem guard_inv {root : ProgramSource} {w : W} {ty : EffTy} {kind : GuardKind}
    {k : Option ExitV → RProgram} (h : TypedProgF root w ty (.vis (.inr (.guard_ kind)) k)) :
    ∃ mid : EffTy, TypedProgF root w mid (k none) ∧
      (∀ w', w.leHost w' → ∀ ex, fiberPostF w' (.guard_ kind) mid (some ex) →
        TypedProgF root w' ty (k (some ex))) ∧
      (∀ w', w.leHost w' → ∀ ex, FitsExit w' mid ex → kind.hasExitArm ex = false →
        FitsExit w' ty ex) := by
  cases h with
  | fiber notGuard _ _ _ _ _ _ => exact absurd rfl (notGuard kind)
  | guard mid body run skip => exact ⟨mid, body, run, skip⟩

end TypedProgF

/-- FR-09's marker payload inversion: a typed `unguard` carries an exit at the current type. -/
theorem unguard_payload_invF (root : ProgramSource) (w : W) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : TypedProgF root w ty (.vis (.inr (.unguard ex)) k)) :
    FitsExit w ty ex := by
  cases h with
  | fiber _ notUnguard _ _ _ _ _ => exact absurd rfl (notUnguard ex)
  | unguard payload => exact payload

theorem finishFinalizer_payload_invF (root : ProgramSource) (w : W) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : TypedProgF root w ty (.vis (.inr (.finishFinalizer ex)) k)) :
    FitsExit w ty ex := by
  cases h with
  | fiber _ _ notFinish _ _ _ _ => exact absurd rfl (notFinish ex)
  | finishFinalizer payload => exact payload

-- src/Effect4/Laws/Program/Typed/Residual.lean:261-308
/-! ## Interpreter hook contracts -/

/-! The recursive hook contracts use mutually inductive step witnesses. This is the
strictly positive form of the brief's existential resume clause: the resume constructor
stores its intermediate type and the next protocol witness. No new program syntax is
stored, and no termination theorem for arbitrary source code is asserted. -/
mutual
  inductive IteratorProtocolF (root : ProgramSource) (w : W) : EffTy → EffTy → EffName → Prop
    | step {tin tout : EffTy} {name : EffName}
        (errors : tin.error = tout.error)
        (next : ∀ v, StrongValueF w tin.answer v →
          IteratorAnswerF root w tout ((interpR root.program).iterNext name v).2) :
        IteratorProtocolF root w tin tout name
  inductive IteratorAnswerF (root : ProgramSource) (w : W) :
      EffTy → IterStep EffName EffThunk Val Err Defect FiberId Ann RProgram → Prop
    | done {tout : EffTy} (result : Val) (typed : FitsExit w tout (.success result)) :
        IteratorAnswerF root w tout (.done result)
    | halt {tout : EffTy} (cause : CauseV) (typed : FitsExit w tout (.failure cause)) :
        IteratorAnswerF root w tout (.halt cause)
    | resume {tout : EffTy} (code : RProgram) (name : EffName) (tin : EffTy)
        (typed : TypedProgF root w tin code) (tail : IteratorProtocolF root w tin tout name) :
        IteratorAnswerF root w tout (.resume code name)
end

mutual
  inductive LoopProtocolF (root : ProgramSource) (w : W) : EffTy → EffTy → EffName → Val → Prop
    | step {tin tout : EffTy} {name : EffName} {cursor : Val}
        (errors : tin.error = tout.error)
        (next : ∀ v, StrongValueF w tin.answer v →
          LoopAnswerF root w tout name ((interpR root.program).loopResume name cursor v)) :
        LoopProtocolF root w tin tout name cursor
  inductive LoopAnswerF (root : ProgramSource) (w : W) :
      EffTy → EffName → LoopNext Val RProgram → Prop
    | continue {tout : EffTy} {name : EffName} (cursor : Val) (body : RProgram) (tin : EffTy)
        (typed : TypedProgF root w tin body) (tail : LoopProtocolF root w tin tout name cursor) :
        LoopAnswerF root w tout name (.continue cursor body)
    | finish {tout : EffTy} {name : EffName} (code : RProgram) (typed : TypedProgF root w tout code) :
        LoopAnswerF root w tout name (.finish code)
end

/-- The three named hook arrows (slice 5 brief §3.3 as amended 2026-09-23). The async clause
types the cancellation only for an incoming failure that is itself typed at the frame's
type, the evidence `popR` holds at that arm (`E4-SCHED-CE-010`). -/
def frameProtocolsF (root : ProgramSource) : Contracts.FrameProtocols where
  asyncFinalizer w tin tout name := tin = tout ∧ ∀ cause, FitsExit w tin (.failure cause) →
    cause.hasInterrupts = true → TypedProgF root w tout ((interpR root.program).cancelThenFail name cause)
  iterator := IteratorProtocolF root
  loop := LoopProtocolF root

-- copied: Walk.lean:892-932 (the restated bundle and typed state)
-- src/Effect4/Laws/Program/Typed/Assembly.lean:33-73
/-- A completion at an effect type: an exit strongly, a reference completion through the
heap table. -/
def CompletionStrongF (w : W) (ty : EffTy) : Completion Val Err Defect FiberId Ann → Prop
  | .ofExit ex => FitsExit w ty ex
  | .ofRefGet cell => ∃ t, w.Ρ cell = some t ∧ t.sub ty.answer = true

/-- A capture's release is admitted: its path addresses an `acquireRelease` the checker types
under an environment its values fit, extended by the acquired value, and its context's
services are typed. -/
def CaptureTypedF (root : ProgramSource) (w : W) (c : Capture) : Prop :=
  ∃ (acquire release : NativeEff) (env : List Ty) (t a : EffTy),
    Node.at_ (.eff root.program) c.path = some (.eff (.acquireRelease acquire release)) ∧
    Checker.check (nativeSignature root.table) env c.path (.acquireRelease acquire release) = .ok t ∧
    Checker.check (nativeSignature root.table) env (c.path ++ [0]) acquire = .ok a ∧
    EnvTypedF w (env ++ [a.answer]) c.env ∧ ServicesFitE w c.ctx.services

/-- The generated bundle, instantiated with the strong judgments. -/
def predsF (root : ProgramSource) : Preds W where
  SavedOk w e x := ∀ ty, expectOf w e = some ty →
    Contracts.SavedOk (TypedProgF root) FitsExit (frameProtocolsF root) w ty x
  PendingOk w _ ps := ∀ p ∈ ps, ∃ id, (w.Θ id p.token).isSome = true
  exit w e ex := ∀ ty, expectOf w e = some ty → FitsExit w ty ex
  ResumeOk w _ target token code := Contracts.ResumeOk (TypedProgF root) w target token code
  ServiceOk w _ ctx := ServicesFitE w ctx.services
  RaceOk w _ races := ∀ r ∈ races, (w.Θ r.host r.token).isSome = true
  PromiseTable w s := ∀ o ∈ s.deferreds.due, ∀ ty, w.Θ o.waiter o.token = some ty →
    CompletionStrongF w ty o.code
  HeapCell w key v := ∀ ty, w.Ρ key = some ty → StrongValueF w ty v
  PromiseCell w key cell := ∀ a e, w.«Π» key = some (a, e) →
    ∀ c, cell.completion = some c → CompletionStrongF w ⟨a, e, Env.Requirement.empty⟩ c
  CaptureOk w _ c := CaptureTypedF root w c

/-- The typed state: world validity, the generated whole-state predicate over `predsF`, and the
active-delivery correlation: a parked fiber's saved stack expects its token's declared type. -/
def TypedStateF (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (predsF root) w m ∧
  ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token →
    ∃ tin final, w.Θ f.id token = some tin ∧ w.Γ f.id = some final ∧
      StackAccepts (TypedProgF root) FitsExit (frameProtocolsF root) w tin final f.frame.stack ∧
      InterruptProvenance f.frame

/-! ## New: the allocation programs' loaded code under the proposed judgment -/

def refProg : NativeEff := .perform .refMake (.lit (.nat 5))
def getProg : NativeEff := .bind (.perform .refMake (.lit (.nat 5))) (.perform .refGet (.var 0))

/-- The seat's `refProg_typedF`, re-proved here: allocate and return, at every world. -/
theorem refProg_typedF (w : W) :
    TypedProgF (refProg : ProgramSource) w (EffTy.pure (.handle NativeOp.refTarget))
      (denoteR refProg refProg (rootPoint 20)) := by
  refine TypedProgF.store (cert := Ty.nat) ⟨rfl, trivial⟩ ?_
  intro w' _ ans hpost
  obtain ⟨key, rfl, hs⟩ := hpost
  exact TypedProgF.pure ⟨rfl, .nat, hs, Ty.sub_refl _, Ty.sub_refl _⟩

/-- The continuation after the guard, for a cell: the read. -/
theorem getProg_after (index : Nat) (completed : List (FiberId × ExitV)) :
    denoteRWith getProg 19 (Eff.perform NativeOp.refGet (Term.var 0))
      ({ (rootPoint 20) with completed }.childWith 1 (Val.cell ⟨index⟩)) =
      .vis (.inl (.refGet ⟨index⟩)) fun v => .pure (.success v) := rfl

/-- `Ref.make(5).flatMap(r => Ref.get(r))` at every world. The guard's body allocates and
unguards the cell at `Ref.Ref<number>`; the declaration the post names is the fit. The run arm
reads the cell's declaration from the value's fit (the only link across the guard), carries it
to the later worlds, and reads the answer through `fits_sub` from the declaration's `Equiv` to
`nat`. The skip arm is a clean failure. -/
theorem getProg_typedF (w : W) :
    TypedProgF (getProg : ProgramSource) w (EffTy.pure .nat)
      (denoteR getProg getProg (rootPoint 20)) := by
  refine TypedProgF.guard (EffTy.pure (.handle NativeOp.refTarget)) ?_ ?_ ?_
  · refine TypedProgF.store (cert := Ty.nat) ⟨rfl, trivial⟩ ?_
    intro w' _ ans hpost
    obtain ⟨key, rfl, hs⟩ := hpost
    exact TypedProgF.unguard ⟨rfl, .nat, hs, Ty.sub_refl _, Ty.sub_refl _⟩
  · intro w' _ ex hpost
    cases ex with
    | failure c => exact Bool.noConfusion hpost.1
    | success v =>
      have hv : Fits w' v (.handle NativeOp.refTarget) := hpost.2
      simp only [Fits, FitsInv] at hv
      split at hv
      · rename_i kind index
        simp only [HandleFits] at hv
        split at hv
        · rename_i hk
          obtain ⟨_, t', hΡ, hsub, _⟩ := hv
          have hkind := HandleKind.ofByte?_exact hk
          subst hkind
          refine TypedProgF.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
            (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () trivial ?_
          intro w'' hle' completed _
          rw [show Val.handle HandleKind.cell.byte index = Val.cell ⟨index⟩ from rfl, getProg_after]
          refine TypedProgF.store (cert := ()) ⟨t', hle'.1.2.2.2.1 _ _ hΡ⟩ ?_
          intro w''' hle'' ans hpost'
          obtain ⟨ty, hty, hfit⟩ := hpost'
          have hsame : w'''.Ρ ⟨index⟩ = some t' := hle''.1.2.2.2.1 _ _ (hle'.1.2.2.2.1 _ _ hΡ)
          change w'''.Ρ ⟨index⟩ = some ty at hty
          rw [hsame] at hty
          cases hty
          exact TypedProgF.pure (fits_sub w''' hsub ans hfit)
        · exact absurd hv.1 (by decide)
        · exact absurd hv (by decide)
        · exact absurd hv.1 (by decide)
        · exact hv.elim
      · exact absurd hv.1 (by decide)
  · intro w' _ ex hex miss
    cases ex with
    | success v => exact Bool.noConfusion miss
    | failure c => exact fitsExit_of_clean w' _ c (cleanExit_of_never_fits w' _ c rfl hex)

/- The copied declarations' axioms, for completeness (the seat prints some of them in its own
files; the copy is checked again here). -/
#print axioms fitsExit_success_iff
#print axioms fitsExit_failure_iff
#print axioms causeFits_map
#print axioms flatFits_fitsInv
#print axioms live_of_keys_nil
#print axioms live_list
#print axioms live_ctor
#print axioms live_ctor_one
#print axioms keys_of_cause
#print axioms live_fiber
#print axioms live_cell
#print axioms live_promise
#print axioms live_handle
#print axioms fits_live
#print axioms fits_sub
#print axioms fitsExit_success
#print axioms fitsExit_of_clean
#print axioms cleanExit_of_never_fits
#print axioms TypedProgF.pure_inv
#print axioms TypedProgF.store_inv
#print axioms TypedProgF.guard_inv
#print axioms unguard_payload_invF
#print axioms finishFinalizer_payload_invF

#print axioms refProg_typedF
#print axioms getProg_after
#print axioms getProg_typedF

/-! ## New: the M5 instance itself holds under the proposed judgment

For a program whose loaded code is typed at every world, the restated typed state holds at the
initial world: the one fiber's saved state is typed, and every other generated clause is over an
empty list or the empty context. So `typedState_load`, restated over `Fits`, is true at
`Ref.make(5)` and at the bind program, the two instances `verify-load.lean` refutes for
`StrongValue`. (No claim is made for every program.) -/

theorem typedStateF_load (p : NativeEff) (ty : EffTy) (closed : ClosedEff ty)
    (code : ∀ w, TypedProgF (p : ProgramSource) w ty (denoteR p p (rootPoint 20))) :
    ∃ w, TypedStateF (p : ProgramSource) ty w (loadR p 20 20) := by
  refine ⟨initialWorld ty, initial_world_valid _ p 20 20 closed, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty' hty
      have h0 : tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root ty Api.root =
          some ty := insert_here _ _ _
      change tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root ty Api.root =
        some ty' at hty
      rw [h0] at hty
      cases hty
      exact ⟨ty, code _, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro q hq
      cases hq
    · intro v0 h
      cases h
    · intro v0 h
      cases h
    · intro v0 hv
      cases hv
    · intro key sv sty hget
      change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
      rw [Env.Context.getV_empty] at hget
      cases hget
  · intro r hr
    cases hr
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v0 hv => nomatch hv)⟩, (fun v0 hv => nomatch hv), trivial⟩
  · intro f hf token hq
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hq

theorem typedStateF_load_ref :
    ∃ w, TypedStateF (refProg : ProgramSource) (EffTy.pure (.handle NativeOp.refTarget)) w
      (loadR refProg 20 20) :=
  typedStateF_load refProg _ ⟨rfl, rfl⟩ refProg_typedF

theorem typedStateF_load_get :
    ∃ w, TypedStateF (getProg : ProgramSource) (EffTy.pure .nat) w (loadR getProg 20 20) :=
  typedStateF_load getProg _ ⟨rfl, rfl⟩ getProg_typedF

#print axioms typedStateF_load
#print axioms typedStateF_load_ref
#print axioms typedStateF_load_get

/-! ## The fold connector's axioms (the seat's `fits.log` shows `fold_of`'s output but no axiom
line for the generated `FitsInv.eq_cata`) -/

fold_of Research.Pass.Membership.VerifyFits.FitsInv

#print axioms FitsInv.eq_cata

end Research.Pass.Membership.VerifyFits
