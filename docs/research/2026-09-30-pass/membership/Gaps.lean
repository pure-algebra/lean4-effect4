import Effect4.Laws.Program.Typed.Assembly

/-!
# Research probe: what the old judgment admits and the membership judgment refuses

Seat MEMBERSHIP, 2026-09-30 pass. Base `be15b062`. Every refutation is a kernel theorem over a
concrete world; the program-level facts at the end are finite `#guard`s, reported as such.

The definitions block below is a verbatim copy of `Fits.lean`'s (research files cannot import
each other); `prelude_check.py` in this folder checks the copies are byte-identical.
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

/-! ## Worlds for the controls -/

/-- Fiber 1 declared at `string`, nothing else declared, empty stores. -/
def wString : W :=
  { ids := [], state := Stores.empty,
    Γ := tableInsert (fun _ => none) ⟨1⟩ (EffTy.pure .string),
    «Π» := fun _ => none, Ρ := fun _ => none, Θ := fun _ _ => none }

/-- Fiber 1 declared at `nat`. -/
def wNat : W :=
  { ids := [], state := Stores.empty,
    Γ := tableInsert (fun _ => none) ⟨1⟩ (EffTy.pure .nat),
    «Π» := fun _ => none, Ρ := fun _ => none, Θ := fun _ _ => none }

/-- Cell 0 declared at `bool`, holding `true`. -/
def wBoolCell : W :=
  { ids := [], state := { Stores.empty with refs := [.bool true] },
    Γ := fun _ => none, «Π» := fun _ => none,
    Ρ := tableInsert (fun _ => none) ⟨0⟩ .bool, Θ := fun _ _ => none }

/-- Cell 0 declared at `nat`, holding `7`. -/
def wNatCell : W :=
  { ids := [], state := { Stores.empty with refs := [.nat 7] },
    Γ := fun _ => none, «Π» := fun _ => none,
    Ρ := tableInsert (fun _ => none) ⟨0⟩ .nat, Θ := fun _ _ => none }

theorem wString_one : wString.Γ ⟨1⟩ = some (EffTy.pure .string) := by
  simp only [wString]
  exact insert_here _ _ _
theorem wNat_one : wNat.Γ ⟨1⟩ = some (EffTy.pure .nat) := by
  simp only [wNat]
  exact insert_here _ _ _
theorem wBoolCell_zero : wBoolCell.Ρ ⟨0⟩ = some .bool := by
  simp only [wBoolCell]
  exact insert_here _ _ _
theorem wNatCell_zero : wNatCell.Ρ ⟨0⟩ = some .nat := by
  simp only [wNatCell]
  exact insert_here _ _ _

theorem string_not_sub_nat : Ty.sub .string .nat = false :=
  Ty.sub_eq_false_of_not_sameHead .string .nat rfl rfl rfl rfl rfl

theorem bool_not_sub_nat : Ty.sub .bool .nat = false :=
  Ty.sub_eq_false_of_not_sameHead .bool .nat rfl rfl rfl rfl rfl

/-- The declaration check refuses fiber 1 at `nat` where it is declared `string`. -/
theorem fiber1_refused : ¬ FiberDeclared wString ⟨1⟩ .nat .never := by
  rintro ⟨fty, hs, ha, _⟩
  rw [wString_one] at hs
  cases hs
  change Ty.sub .string .nat = true at ha
  rw [string_not_sub_nat] at ha
  exact Bool.noConfusion ha

theorem fiber1_accepted : FiberDeclared wNat ⟨1⟩ .nat .never :=
  ⟨EffTy.pure .nat, wNat_one, Ty.sub_refl _, Ty.sub_refl _⟩

/-- Fiber 1 is live (a fiber's `HandlesLive` clause is the table). -/
theorem handlesLive_one {v : Val} (hk : v.keys = [Handle.fiber ⟨1⟩]) : HandlesLive wString v := by
  intro k hmem
  rw [hk, List.mem_singleton] at hmem
  subst hmem
  show (wString.Γ ⟨1⟩).isSome = true
  rw [wString_one]
  rfl

/-! ## The converse of `fits_hasTy` is false -/

theorem shape_without_fit :
    Val.hasTy (Value.fiber 1) (.fiberOf .nat .never) wString.state.externals.allocated = true ∧
      ¬ Fits wString (Value.fiber 1) (.fiberOf .nat .never) :=
  ⟨rfl, fun h => fiber1_refused h⟩

theorem converse_false :
    ¬ ∀ (w : W) (v : Val) (ty : Ty),
      Val.hasTy v ty w.state.externals.allocated = true → Fits w v ty :=
  fun h => shape_without_fit.2 (h _ _ _ shape_without_fit.1)

/-! ## The gaps: `StrongValue` admits, `Fits` refuses, and admits the honest value

G1–G4 are `PredicateProbe.lean`'s four (product, Result, successful exit, union); G5 is the
contract's snapshot bullet (§4); G6 is the native cell spelling, which `HandlesFit` never checks
(its `.handle` arm types contexts only, `Typed/Admission.lean:57`). -/

-- G1: a product is a two-cell list; `HandlesFit` looks for `.pair`.
theorem g1_old : StrongValue wString (.prod (.fiberOf .nat .never) .unit) (.list [Value.fiber 1, .unit]) :=
  ⟨rfl, trivial, handlesLive_one rfl⟩
theorem g1_refused : ¬ Fits wString (.list [Value.fiber 1, .unit]) (.prod (.fiberOf .nat .never) .unit) :=
  fun h => fiber1_refused h.1
theorem g1_control : Fits wNat (.list [Value.fiber 1, .unit]) (.prod (.fiberOf .nat .never) .unit) :=
  ⟨fiber1_accepted, trivial⟩

-- G2: a Result's success arm.
theorem g2_old : StrongValue wString (.except .never (.fiberOf .nat .never)) (.ctor 1 [Value.fiber 1]) :=
  ⟨rfl, trivial, handlesLive_one rfl⟩
theorem g2_refused : ¬ Fits wString (.ctor 1 [Value.fiber 1]) (.except .never (.fiberOf .nat .never)) :=
  fun h => fiber1_refused h
theorem g2_control : Fits wNat (.ctor 1 [Value.fiber 1]) (.except .never (.fiberOf .nat .never)) :=
  fiber1_accepted

-- G3: a successful reified exit.
theorem g3_old :
    StrongValue wString (.exitOf (.fiberOf .nat .never) .never) (Value.exitOk (Value.fiber 1)) :=
  ⟨rfl, trivial, handlesLive_one rfl⟩
theorem g3_refused :
    ¬ Fits wString (Value.exitOk (Value.fiber 1)) (.exitOf (.fiberOf .nat .never) .never) :=
  fun h => fiber1_refused h
theorem g3_control : Fits wNat (Value.exitOk (Value.fiber 1)) (.exitOf (.fiberOf .nat .never) .never) :=
  fiber1_accepted

-- G4: a union whose shape evidence and handle evidence come from different branches.
theorem g4_old : StrongValue wString (.union (.fiberOf .nat .never) .unit) (Value.fiber 1) :=
  ⟨rfl, Or.inr trivial, handlesLive_one rfl⟩
theorem g4_refused : ¬ Fits wString (Value.fiber 1) (.union (.fiberOf .nat .never) .unit) :=
  fun h => h.elim (fun hf => fiber1_refused hf) (fun hu => hu)
theorem g4_control : Fits wNat (Value.fiber 1) (.union (.fiberOf .nat .never) .unit) :=
  Or.inl fiber1_accepted

-- G5: a fiber snapshot, which the shape check decodes and `HandlesFit` skips.
theorem g5_old : StrongValue wString (.list (.fiberOf .nat .never)) (Val.fibers [⟨1⟩]) :=
  ⟨rfl, trivial, handlesLive_one (by rw [Val.keys_fibers]; rfl)⟩
theorem g5_refused : ¬ Fits wString (Val.fibers [⟨1⟩]) (.list (.fiberOf .nat .never)) := by
  intro h
  simp only [Fits, FitsInv, Val.snapshot?_fibers] at h
  exact fiber1_refused (h ⟨1⟩ (List.mem_singleton_self _))
theorem g5_control : Fits wNat (Val.fibers [⟨1⟩]) (.list (.fiberOf .nat .never)) := by
  simp only [Fits, FitsInv, Val.snapshot?_fibers]
  intro id hid
  rw [List.mem_singleton] at hid
  subst hid
  exact fiber1_accepted

-- G6: the native cell spelling `Ref.Ref<number>` at a cell declared `bool`.
theorem g6_old : StrongValue wBoolCell (.handle NativeOp.refTarget) (Value.cell 0) := by
  refine ⟨beq_iff_eq.mpr rfl, fun _ ctx hctx => ?_, fun k hk => ?_⟩
  · exact nomatch hctx
  · have hk' : k ∈ (Val.cell ⟨0⟩).keys := hk
    rw [Val.keys_cell, List.mem_singleton] at hk'
    subst hk'
    exact Nat.zero_lt_one
theorem g6_refused : ¬ Fits wBoolCell (Value.cell 0) (.handle NativeOp.refTarget) := by
  rintro ⟨_, t', hs, hsub, _⟩
  rw [wBoolCell_zero] at hs
  cases hs
  rw [bool_not_sub_nat] at hsub
  exact Bool.noConfusion hsub
theorem g6_control : Fits wNatCell (Value.cell 0) (.handle NativeOp.refTarget) :=
  ⟨rfl, .nat, wNatCell_zero, Ty.sub_refl _, Ty.sub_refl _⟩

/-! ## G7: invariance spelled as equality is not closed under the checker's subtyping

`refOf nat` and `refOf (union nat nat)` are subtypes of each other under `Ty.sub`. `HandlesFit`
(and `FitsEq`) demand the declared spelling exactly, so they break subsumption at an invariant
handle; `Fits` (subtyping both ways) keeps it (`fits_sub`, `Fits.lean`). -/

theorem sub_nat_union : Ty.sub .nat (.union .nat .nat) = true := by
  rw [Ty.sub_union_right .nat .nat .nat rfl, Ty.sub_refl]
  rfl

theorem sub_union_nat : Ty.sub (.union .nat .nat) .nat = true := by
  rw [Ty.sub_union_left .nat .nat .nat (fun h => Ty.noConfusion h), Ty.sub_refl]
  rfl

theorem sub_ref_equiv : Ty.sub (.refOf .nat) (.refOf (.union .nat .nat)) = true := by
  rw [Ty.sub_args_refOf]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, sub_nat_union, sub_union_nat]

theorem cell0_keys : Val.keys (Value.cell 0) = [Handle.cell ⟨0⟩] := Val.keys_cell ⟨0⟩

theorem natCell_old : StrongValue wNatCell (.refOf .nat) (Value.cell 0) := by
  refine ⟨rfl, fun key hkey => ?_, fun k hk => ?_⟩
  · rw [cell0_keys, List.mem_singleton] at hkey
    cases hkey
    exact wNatCell_zero
  · rw [cell0_keys, List.mem_singleton] at hk
    subst hk
    exact Nat.zero_lt_one

theorem natCell_old_refused : ¬ StrongValue wNatCell (.refOf (.union .nat .nat)) (Value.cell 0) := by
  intro h
  have hs := h.2.1 ⟨0⟩ (by rw [cell0_keys]; exact List.mem_singleton_self _)
  rw [wNatCell_zero] at hs
  cases hs

theorem strongValue_not_closed_under_sub :
    ¬ ∀ (w : W) (a b : Ty) (v : Val), Ty.sub a b = true → StrongValue w a v → StrongValue w b v :=
  fun h => natCell_old_refused (h _ _ _ _ sub_ref_equiv natCell_old)

theorem fitsEq_not_closed_under_sub :
    ¬ ∀ (w : W) (a b : Ty) (v : Val), Ty.sub a b = true → FitsEq w v a → FitsEq w v b := by
  intro h
  have hb := h wNatCell _ _ (Value.cell 0) sub_ref_equiv ⟨.nat, wNatCell_zero, rfl⟩
  obtain ⟨t', hs, heq⟩ := hb
  rw [wNatCell_zero] at hs
  cases hs
  cases heq

/-- The `Ty.sub` reading admits the equivalent spelling, where the old judgment refuses it. -/
theorem natCell_equiv_spelling :
    Fits wNatCell (Value.cell 0) (.refOf (.union .nat .nat)) ∧
      ¬ StrongValue wNatCell (.refOf (.union .nat .nat)) (Value.cell 0) :=
  ⟨⟨.nat, wNatCell_zero, sub_nat_union, sub_union_nat⟩, natCell_old_refused⟩

/-! ## G8: a program that returns a fresh `Ref` has no `TypedProg` derivation under `StrongValue`

`TypedProg` types a continuation at every later world the post admits (`Typed/Residual.lean:189-192`).
`storePost (.refMake _)` names the new key's declaration and not the heap length
(`:58`), while `HandlesLive` asks for the heap length (`Typed/Admission.lean:23`). The later world
below declares cell 0 without growing the heap: it is `leHost`-after the initial world, satisfies
the post, and refutes the returned cell's `StrongValue`. `Fits` reads liveness from the tables, so
the same continuation obligation holds at every later world (`refReturn_fits`). -/

/-- `Ref.make(true)`, then return the cell: the store protocol's own program shape (as
`refAllocGetProg`, `Typed/Residual.lean:316`). -/
def refReturnProg : RProgram := .vis (.inl (.refMake (Val.bool true))) fun ans => .pure (.success ans)

def w0 : W := initialWorld (EffTy.pure (.refOf .bool))

theorem w0_order (cert : Ty) : w0.leHost (w0.addRef w0.state ⟨0⟩ cert) := by
  refine ⟨⟨⟨fun _ h => h, Stores.le_refl _⟩, table_refl _, table_refl _,
    insert_extends _ _ _ rfl, ⟨fun key ty h => ?_, fun key types h => ?_⟩, fun _ => table_refl _⟩,
    fun _ _ h => h⟩
  · exact nomatch h.1
  · exact nomatch h.1

theorem refReturn_untypable (root : ProgramSource) :
    ¬ TypedProg root w0 (EffTy.pure (.refOf .bool)) refReturnProg := by
  intro h
  obtain ⟨cert, _, next⟩ := TypedProg.store_inv h
  have post : (Ψ_S root).post (w0.addRef w0.state ⟨0⟩ cert) (.refMake (Val.bool true)) cert
      (Val.cell ⟨0⟩) := ⟨⟨0⟩, rfl, insert_here w0.Ρ ⟨0⟩ cert⟩
  have hex := TypedProg.pure_inv (next _ (w0_order cert) _ post)
  have hv := hex.2.1 (Val.cell ⟨0⟩) rfl
  have hlive := hv.2.2 (Handle.cell ⟨0⟩) (by rw [Val.keys_cell]; exact List.mem_singleton_self _)
  exact Nat.lt_irrefl 0 hlive

/-- Under `Fits` the continuation's obligation holds at every world the post admits. -/
theorem refReturn_fits (w' : W) (ans : Val)
    (post : storePost w' (.refMake (Val.bool true)) Ty.bool ans) :
    FitsExit w' (EffTy.pure (.refOf .bool)) (.success ans) := by
  obtain ⟨key, rfl, hs⟩ := post
  exact ⟨.bool, hs, Ty.sub_refl _, Ty.sub_refl _⟩

/-! ## G9: the pair program (`host-answers-evidence/PathProbes.lean` §D)

A closed program with no host: fork a child answering 7, store its handle in a pair, take it
back with `fst`, await it. Finite checks: it types at `nat` and runs to 7; the pair's static
type is `prod (fiberOf nat never) unit`. Kernel facts: the pair atom builds the two-cell list;
the old judgment holds of that pair where fiber 1 is declared `string`, yet not of its first
component, so no `fst` step can carry the fiber's declaration under `StrongValue`.
`Fits.lean`'s `fits_fst` and `await_fits` are the steps M6 needs, proved for `Fits`. -/

def opts : Supervision.ForkOptions := ⟨true, true, .interruptible⟩

def pairProgram : Api.Program :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 7))) opts))
    (.bind (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit .unit) .nil))))
      (.awaitFiber (.app "fst" (.cons (.var 1) .nil)) .joinEffect))

def pairOnly : Api.Program :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 7))) opts))
    (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit .unit) .nil))))

#guard Api.typeOf pairProgram [] = some (EffTy.pure .nat)
#guard (Api.run pairProgram 1000).exit = some (.success (.nat 7))
#guard Api.typeOf pairOnly [] = some (EffTy.pure (.prod (.fiberOf .nat .never) .unit))

theorem pair_builds :
    NativeAtom.eval .pair [Value.fiber 1, .unit] = some (.list [Value.fiber 1, .unit]) := rfl

theorem fst_projects : NativeAtom.eval .fst [.list [Value.fiber 1, .unit]] = some (Value.fiber 1) :=
  rfl

theorem strongValue_no_fst :
    StrongValue wString (.prod (.fiberOf .nat .never) .unit) (.list [Value.fiber 1, .unit]) ∧
      NativeAtom.eval .fst [.list [Value.fiber 1, .unit]] = some (Value.fiber 1) ∧
      ¬ StrongValue wString (.fiberOf .nat .never) (Value.fiber 1) := by
  refine ⟨g1_old, rfl, fun h => ?_⟩
  have hk : Handle.fiber ⟨1⟩ ∈ Val.keys (Value.fiber 1) := List.mem_singleton_self _
  exact fiber1_refused (h.2.1 ⟨1⟩ hk)

/-- The pair the honest program builds fits where fiber 1 is declared `nat`; the same pair is
refused where it is declared `string` (`g1_refused`). -/
theorem pair_honest : Fits wNat (.list [Value.fiber 1, .unit]) (.prod (.fiberOf .nat .never) .unit) :=
  g1_control

/-! ## G10: the declared M5 obligation `typedState_load` is false for `Ref.make(5)`

`M3bAssembly.typedState_load` (`Typed/Assembly.lean:148-150`, `#proof_wanted`) promises a typed
initial state for every checked source with closed columns. The one-line program below checks at
`Ref.Ref<number>` (kernel, `decide +kernel`); its loaded code is the store protocol's
`refMake` step followed by returning the answer (`loaded_root`, by `rfl`). Every typed state of the
loaded machine types that code at the root's type, and `refProg_untypable` refutes that at every
world with an empty heap and an undeclared cell 0, which `WorldValid` forces for the loaded
machine. The obstruction is G8's: `HandlesLive` reads the heap length, the post names only the
table. -/

def refProg : NativeEff := .perform .refMake (.lit (.nat 5))
abbrev refTy : EffTy := EffTy.pure (.handle NativeOp.refTarget)

theorem refProg_checks : Api.typeOf refProg [] = some refTy := by decide +kernel

theorem refTy_closed : ClosedEff refTy := ⟨rfl, rfl⟩

theorem loaded_root : ∃ f, (loadR refProg 20 20).fiber? Api.root = some f ∧
    f.frame.stack = [] ∧ f.frame.current = denoteR refProg refProg (rootPoint 20) :=
  ⟨_, rfl, rfl, rfl⟩

/-- No typed derivation of the loaded code at any world with an empty heap and cell 0 undeclared. -/
theorem refProg_untypable (w : W) (hRho : w.Ρ ⟨0⟩ = none) (hrefs : w.state.refs = []) :
    ¬ TypedProg refProg w refTy (denoteR refProg refProg (rootPoint 20)) := by
  intro h
  obtain ⟨cert, _, next⟩ := TypedProg.store_inv h
  have hle : w.leHost (w.addRef w.state ⟨0⟩ cert) := by
    refine ⟨⟨⟨fun _ h => h, Stores.le_refl _⟩, table_refl _, table_refl _,
      insert_extends _ _ _ hRho, ⟨fun key ty h => ?_, fun key types h => ?_⟩, fun _ => table_refl _⟩,
      fun _ _ h => h⟩
    · exact ⟨insert_extends _ _ _ hRho key ty h.1, fun value hv => h.2 value hv⟩
    · exact ⟨h.1, fun cell hc comp hcomp =>
        completionOk_extends w (w.addRef w.state ⟨0⟩ cert) types (insert_extends _ _ _ hRho) rfl comp
          (h.2 cell hc comp hcomp)⟩
  have post : (Ψ_S (refProg : ProgramSource)).post (w.addRef w.state ⟨0⟩ cert) (.refMake (.nat 5))
      cert (Val.cell ⟨0⟩) := ⟨⟨0⟩, rfl, insert_here w.Ρ ⟨0⟩ cert⟩
  have hex := TypedProg.pure_inv (next _ hle _ post)
  have hv := hex.2.1 (Val.cell ⟨0⟩) rfl
  have hlive := hv.2.2 (Handle.cell ⟨0⟩) (by rw [Val.keys_cell]; exact List.mem_singleton_self _)
  change 0 < w.state.refs.length at hlive
  rw [hrefs] at hlive
  exact Nat.lt_irrefl 0 hlive

/-- **The obligation's instance at `Ref.make(5)` is false**: its premises hold and no typed state
of the loaded machine exists. -/
theorem typedState_load_false :
    ¬ (Api.typeOf refProg [] = some refTy → ClosedEff refTy →
      ∃ w, TypedState (refProg : ProgramSource) refTy w (loadR refProg 20 20)) := by
  intro obligation
  obtain ⟨w, valid, ok, _⟩ := obligation refProg_checks refTy_closed
  obtain ⟨f, hf, hstack, hcur⟩ := loaded_root
  have hmem : f ∈ (loadR refProg 20 20).fibers := List.mem_of_find?_eq_some hf
  have hid : f.id = Api.root := by
    have := List.find?_some hf
    simpa using this
  have hroot : expectOf w (.fiber f.id) = some refTy := by
    rw [hid]
    exact valid.root
  obtain ⟨tin, hprog, hst, _⟩ := (ok.c0 f hmem).c0.c0 _ hroot
  rw [hstack] at hst
  cases hst
  rw [hcur] at hprog
  have hRho : w.Ρ ⟨0⟩ = none := by
    cases hs : w.Ρ ⟨0⟩ with
    | none => rfl
    | some t =>
      have live : (w.Ρ ⟨0⟩).isSome = true := by rw [hs]; rfl
      exact absurd ((valid.heap ⟨0⟩).mp live) (Nat.lt_irrefl 0)
  have hrefs : w.state.refs = [] := by
    rw [valid.state]
    rfl
  exact refProg_untypable w hRho hrefs hprog

#print axioms converse_false
#print axioms g1_old
#print axioms g1_refused
#print axioms g1_control
#print axioms g2_old
#print axioms g2_refused
#print axioms g2_control
#print axioms g3_old
#print axioms g3_refused
#print axioms g3_control
#print axioms g4_old
#print axioms g4_refused
#print axioms g4_control
#print axioms g5_old
#print axioms g5_refused
#print axioms g5_control
#print axioms g6_old
#print axioms g6_refused
#print axioms g6_control
#print axioms sub_ref_equiv
#print axioms strongValue_not_closed_under_sub
#print axioms fitsEq_not_closed_under_sub
#print axioms natCell_equiv_spelling
#print axioms refReturn_untypable
#print axioms refReturn_fits
#print axioms pair_builds
#print axioms fst_projects
#print axioms strongValue_no_fst
#print axioms pair_honest
#print axioms refProg_checks
#print axioms refProg_untypable
#print axioms typedState_load_false

end Research.Pass.Membership
