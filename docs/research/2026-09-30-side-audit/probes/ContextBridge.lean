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


/-- Audit witness: an ordinary context with a string at the static nat key. -/
def auditKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def auditCtx : Ctx := Ctx.withServices ((Env.Context.empty : Env.Ctx).add auditKey (.str "wrong"))
def auditValue : Val := Val.context auditCtx

#guard Val.hasTy auditValue Ty.context = true
#guard auditValue.handles = []

/-- Item A's proposed success preparation, copied from the synthesis appendix. -/
def externalValueA (ty : Ty) (allocated : List String) (value : Val) :
    Option (List String × Val) :=
  match ty, value with
  | .handle target, .nat index =>
    if externalHandleTarget target && index == allocated.length then
      some (allocated ++ [target], Value.external index)
    else none
  | _, _ =>
    if Val.hasTy value ty allocated && (Store.Val.handles value).isEmpty then
      some (allocated, value)
    else none

#guard (externalValueA Ty.context [] auditValue).isSome
#guard internalHandleTargets.contains Ty.contextTarget

theorem audit_context_not_fits (w : W) : ¬ Fits w auditValue Ty.context := by
  intro h
  change Ty.contextTarget = Ty.contextTarget ∧ ∃ ctx,
    Val.context? (Val.context auditCtx) = some ctx ∧ ServicesFit w Equiv ctx.services ∧ Live w auditValue at h
  obtain ⟨_, ctx, hc, hs, _⟩ := h
  rw [Val.context?_context] at hc
  cases hc
  have hb := hs auditKey (.str "wrong") .nat (by rfl) (by decide)
  exact hb

theorem audit_no_generic_handlefree_bridge :
    ¬ (∀ (w : W) (v : Val) (ty : Ty), Val.hasTy v ty w.state.externals.allocated = true →
      v.handles = [] → Fits w v ty) := by
  intro h
  exact audit_context_not_fits (initialWorld (EffTy.pure .unit))
    (h _ auditValue Ty.context (by decide) (by decide))

#print axioms audit_context_not_fits
#print axioms audit_no_generic_handlefree_bridge
end Research.Pass.Membership
