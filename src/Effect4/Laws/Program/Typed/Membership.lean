import Effect4.Laws.Program.Typed.Validity
import Effect4.Laws.Program.Typed.RecordValues
import Effect4.Laws.Program.Typed.MapValues
import Effect4.Program.FoldOf
import Effect4.Laws.Program.Signature
import Effect4.Program.TyClasses

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

/-- The column a handle frame of kind `kind` at `index` is read in: a cell, deferred or fiber the
world declares, a scope or memo map the world's store holds, an external it has allocated. An
unregistered byte is no capability. -/
def KindLive (w : World) (index : Nat) : Option HandleKind → Prop
  | some .cell => (w.Ρ ⟨index⟩).isSome = true
  | some .promise => (w.«Π» ⟨index⟩).isSome = true
  | some .fiber => (w.Γ ⟨index⟩).isSome = true
  | some .scope => ScopeLive w index
  | some .memoMap => MemoLive w ⟨index⟩
  | some .external => index < w.state.externals.allocated.length
  | none => False

/-- **Capability membership** (finding F-WF, owner's ruling 2026-10-02: membership at `unknown` is
validity): every raw handle frame of the value (`Store.Val.handles`, unregistered bytes included)
is live in its kind's column (`KindLive`). Cells, deferreds and fibers are read in the declaration
tables, as allocation posts supply them; with the store's forward bounds (`CellsTyped.heap`,
`.promises`) this is the store's validity (`live_validIn`), which `Stores.WF` asks of every stored
value and closing exit. Before the ruling only the registered cell, deferred and fiber frames
were read (`Val.keys`), so `.handle 255 7` fit `unknown` (`E4-TYPED-CE-040`). -/
def Live (w : World) (v : Val) : Prop :=
  ∀ h ∈ Store.Val.handles v, KindLive w h.2 (HandleKind.ofByte? h.1)

/-- The reserved and external handle spellings (`Val.hasTy`'s `.handle` arm). A cell or a
promise fits no spelling: it fits `refOf _` or `deferredOf _ _` at its declaration (the state
plan's T3a; decisions row 96 D2 retired). A scope handle names a scope the world's store holds
(`ScopeLive`, decisions rows 139 and 156), as the external arm reads its table. -/
def HandleFits (w : World) (kind : UInt8) (index : Nat) (target : String) : Prop :=
  match HandleKind.ofByte? kind with
  | some .scope => target = Ty.scopeTarget ∧ ScopeLive w index
  -- a memo map is read through a guard, so its handle has its own type; it names a memo map the
  -- world's store holds (decisions row 187, amended 2026-10-02 by finding F-WF: capability
  -- membership reads presence for every kind; memo maps are never removed, `Stores.le`)
  | some .memoMap => target = Ty.memoMapTarget ∧ MemoLive w ⟨index⟩
  | some .external => externalHandleTarget target = true ∧
      w.state.externals.allocated[index]? = some target
  | _ => False

/-- Membership at a service's static type (decision row 90): the service table's types are
scalars, non-context handles and a cell (`nativeServiceTypes`, `nativeReservedServiceTypes`), so
this needs no recursion: a cell reads its declaration at its argument and never recurses into it.
`flatFits_fits` connects it to `Fits`. -/
def FlatFits (w : World) (v : Val) : Ty → Prop
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .string => match v with | .str _ => True | _ => False
  | .handle target =>
    match v with | .handle kind index => HandleFits w kind index target | _ => False
  | .refOf t => match v with | Value.cell index => RefDeclared w ⟨index⟩ t | _ => False
  | _ => False

/-- A context's services fit their keys' static types, read off the world's static service
table (shape A, decisions row 112), and every service value the context holds, declared key or
not, is live (finding F-CTX: so the context itself is live, `Val.handles_context`, and
`getContext`'s answer fits the context handle). -/
def ServicesFit (w : World) (services : Env.Ctx) : Prop :=
  (∀ key sv sty, services.getV key = some sv → w.serviceTy key = some sty →
    FlatFits w sv sty) ∧ ∀ e ∈ services.entries, Live w e.valueVal

/-- The liveness half of `ServicesFit` from the entries' raw handles. -/
theorem entriesLive_of_flatMap {w : World} {es : List (Env.Service Env.ValU)}
    (h : ∀ x ∈ es.flatMap (fun e => Store.Val.handles e.valueVal),
      KindLive w x.2 (HandleKind.ofByte? x.1)) :
    ∀ e ∈ es, Live w e.valueVal :=
  fun e he x hx => h x (List.mem_flatMap.mpr ⟨e, he, hx⟩)

/-- …and back. -/
theorem flatMap_live {w : World} {es : List (Env.Service Env.ValU)}
    (h : ∀ e ∈ es, Live w e.valueVal) :
    ∀ x ∈ es.flatMap (fun e => Store.Val.handles e.valueVal),
      KindLive w x.2 (HandleKind.ofByte? x.1) := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := List.mem_flatMap.mp hx
  exact h e he x hxe

/-- The empty map's services fit vacuously (`Context.empty()`, `Layer.ts:1515`). -/
theorem servicesFit_empty (w : World) : ServicesFit w Env.Context.empty := by
  refine ⟨fun key sv sty hget _ => ?_, fun e he => by cases he⟩
  rw [Env.Context.getV_empty] at hget
  cases hget

/-- Adding a live service keeps every service value live (`Context.add`, `Map.set`). -/
theorem entriesLive_addV {w : World} {s : Env.Ctx} {key : ServiceKey} {v : Val} (hv : Live w v)
    (hs : ∀ e ∈ s.entries, Live w e.valueVal) :
    ∀ e ∈ (s.addV key v).entries, Live w e.valueVal := by
  apply entriesLive_of_flatMap
  intro x hx
  rcases List.mem_append.mp (Env.Context.flatMap_setEntries_subset
      (fun e => Store.Val.handles e.valueVal) key v s.entries hx) with new | old
  · exact hv x new
  · exact flatMap_live hs x old

/-- Every typed failure of a cause has an image satisfying `member`; defects and interruptions
are outside the error column (`reasonAdmits`, `Program/ErrorImage.lean:31`). -/
def CauseFits (member : Val → Prop) (c : CauseV) : Prop :=
  ∀ r ∈ c.reasons, match r with
  | .fail e _ => ∃ v, valOfErr e = some v ∧ member v
  | .die _ _ | .interrupt _ _ => True

/-- No reason of a cause dies with a shape defect: `badName` or `notImplemented`, the defects a
checked program never produces (decisions row 107, H2 part one; `NoShapeDefect`'s failure arm,
`Typed/Admission.lean`, is this predicate, `noShapeDefect_failure_iff`). Membership at an exit
type reads it (decisions row 152), so an exit carried as a value keeps the exclusion its typed
position had. -/
def ShapeFree (c : CauseV) : Prop :=
  ∀ r ∈ c.reasons, match r with
  | .die defect _ => defect ≠ .badName ∧ defect ≠ .notImplemented
  | _ => True

/-- A tuple's items, one for one (decisions row 159). -/
def ItemsFit : List (Val → Prop) → List Val → Prop
  | [], [] => True
  | P :: ps, x :: xs => P x ∧ ItemsFit ps xs
  | _, _ => False

/-- The entries of a map value: sorted pairs whose keys and values fit (decisions row 125). -/
def EntriesFit (PK PV : Val → Prop) (es : List Val) : Prop :=
  sortedEntries es = true ∧ ∀ e ∈ es, match e with
    | .pair a x => PK a ∧ PV x
    | _ => False

mutual
/-- **The membership judgment.** The arms and value shapes are `Val.hasTy`'s, one for one; the
handle leaves read the world's declaration tables; `unknown` requires declared liveness. At an
exit type the encoded cause is also shape-free (`ShapeFree`, decisions row 152): a reified exit
fits `Exit<A, E>` exactly when the exit has `ExitOk`'s base membership and part one's exclusion,
so the close walk, which passes each finalizer's exit on as a value, keeps the exclusion
(`Test/Program/ProtocolPosts.lean`, `CloseIter`). A record value is read by name in canonical
order (`NamedFit`), a map by its sorted entries, a tuple item by item, a nominal reference as the
handle at its name; `int` and `number` are the nesting images (decisions row 121). -/
def Fits (w : World) (v : Val) : Ty → Prop
  | .never => False
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .int => intImage v = true
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
      | some c => CauseFits (fun x => Fits w x e) c ∧ ShapeFree c
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
    match recordParts? v with
    | some (ns, xs) => NamedFit (Ty.canon (fitters w fs)) ns xs
    | none => False
  | .map k t =>
    match v with
    | .list es => EntriesFit (fun a => Fits w a k) (fun x => Fits w x t) es
    | _ => False
  | .tuple ts =>
    match v with
    | .list xs => ItemsFit (itemFitters w ts) xs
    | _ => False
  | .app name _ =>
    match v with
    | .handle kind index => HandleFits w kind index name
    | _ => name = Ty.contextTarget ∧
        ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w ctx.services ∧ Live w v
  | .null => match v with | .none => True | _ => False
  | .undefined => match v with | .unit => True | _ => False
  | .number => numberImage v = true
  | .bytes => match v with | .bytes _ => True | _ => False
/-- The field-list companion of `Fits`: one membership predicate per written field. -/
def fitters (w : World) : List (String × Bool × Ty) → List (String × Bool × (Val → Prop))
  | [] => []
  | (n, o, t) :: rest => (n, o, fun x => Fits w x t) :: fitters w rest
/-- The item-list companion of `Fits`. -/
def itemFitters (w : World) : List Ty → List (Val → Prop)
  | [] => []
  | t :: rest => (fun x => Fits w x t) :: itemFitters w rest
end

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

/-- A failed exit fits exactly when its cause fits the error column and is shape-free (decisions
row 152; before it, the cause half alone). -/
theorem fitsExit_failure_iff (w : World) (ty : EffTy) (c : CauseV) :
    FitsExit w ty (.failure c) ↔ FitsCause w ty.error c ∧ ShapeFree c := by
  unfold FitsExit
  simp only [reifyExitVal, Fits, Store.Image.ofVal_toVal]

/-- A failed exit's membership gives its cause's at the error column. -/
theorem fitsExit_failure_cause {w : World} {ty : EffTy} {c : CauseV}
    (h : FitsExit w ty (.failure c)) : FitsCause w ty.error c :=
  ((fitsExit_failure_iff w ty c).mp h).1

/-- A failed exit's membership gives part one's exclusion on its cause (decisions row 152). -/
theorem fitsExit_failure_shape {w : World} {ty : EffTy} {c : CauseV}
    (h : FitsExit w ty (.failure c)) : ShapeFree c :=
  ((fitsExit_failure_iff w ty c).mp h).2

/-- An exit whose failure carries no `Fail` reason: interruptions and defects only. Every
success is clean. The sanitized exit at a preempted skip is clean (`Cause.sanitize_clean`). -/
def cleanExit : ExitV → Bool
  | .success _ => true
  | .failure c => c.reasons.all fun r => r.tag != .fail

/-- Membership at the answer column gives membership of a successful exit. -/
theorem fitsExit_success (w : World) (ty : EffTy) (v : Val) (h : Fits w v ty.answer) :
    FitsExit w ty (.success v) := h

/-- A clean cause fits every error column: only `Fail` reasons use it. -/
theorem fitsCause_of_clean (w : World) (errTy : Ty) (c : CauseV)
    (h : cleanExit (.failure c) = true) : FitsCause w errTy c := by
  intro r hr
  have hne : r.tag ≠ .fail := bne_iff_ne.mp (List.all_eq_true.mp h r hr)
  cases r with
  | fail e ann => exact absurd rfl hne
  | die _ _ => trivial
  | interrupt _ _ => trivial

/-- A clean, shape-free failure fits every effect type: only `Fail` reasons use the error column.
Cleanliness alone admits `badName` and `notImplemented` (decisions row 152: the premise `shape`
is new; before it a clean `die badName` fit every exit type). -/
theorem fitsExit_of_clean (w : World) (ty : EffTy) (c : CauseV)
    (h : cleanExit (.failure c) = true) (shape : ShapeFree c) : FitsExit w ty (.failure c) :=
  (fitsExit_failure_iff w ty c).mpr ⟨fitsCause_of_clean w ty.error c h, shape⟩

/-- At a `never` error column a failed exit is clean: no value fits `never`. -/
theorem cleanExit_of_never_fits (w : World) (ty : EffTy) (c : CauseV) (never : ty.error = .never)
    (h : FitsExit w ty (.failure c)) : cleanExit (.failure c) = true := by
  have hc := fitsExit_failure_cause h
  rw [never] at hc
  unfold cleanExit
  rw [List.all_eq_true]
  intro r hr
  have hr' := hc r hr
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
  case refOf t =>
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

/-- The handle arm: membership implies the shape check. A nominal reference reads the same arm
at its name (`fits_app_iff`, `hasTy_app_eq`). -/
theorem handle_fits_hasTy (w : World) {v : Val} {target : String} (h : Fits w v (.handle target)) :
    Val.hasTy v (.handle target) w.state.externals.allocated = true := by
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
      exact Bool.and_eq_true_iff.mpr ⟨h.1, beq_iff_eq.mpr h.2⟩
    · exact h.elim
  · obtain ⟨ht, ctx, hctx, _, _⟩ := h
    simp only [Val.hasTy]
    rw [hctx]
    exact Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr ht, rfl⟩

/-- A nominal reference's membership is the handle's at its name (decisions row 158). -/
theorem fits_app_iff (w : World) (v : Val) (name : String) (args : List Ty) :
    Fits w v (.app name args) ↔ Fits w v (.handle name) := Iff.rfl

/-- A nominal reference's shape check is the handle's at its name. -/
theorem hasTy_app_eq (v : Val) (name : String) (args : List Ty) (al : List String) :
    Val.hasTy v (.app name args) al = Val.hasTy v (.handle name) al := rfl

/-- A field's membership predicate. -/
def fitterOf (w : World) (c : Bool × Ty) : Bool × (Val → Prop) := (c.1, fun x => Fits w x c.2)

/-- The field companion of `Fits` is a payload map. -/
theorem fitters_eq_map (w : World) (fs : List (String × Bool × Ty)) :
    fitters w fs = fs.map (fun q => (q.1, fitterOf w q.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [fitters, ih]
    rfl

theorem itemFitters_eq_map (w : World) (ts : List Ty) :
    itemFitters w ts = ts.map (fun t x => Fits w x t) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [itemFitters, ih]
    rfl

/-- **The record arm (decisions rows 157, 165), named**: a record value is its names and values,
read in canonical order. -/
theorem fits_record (w : World) {v : Val} {ns xs : List Val} (hv : recordParts? v = some (ns, xs))
    (fs : List (String × Bool × Ty)) :
    Fits w v (.record fs) ↔
      NamedFit ((Ty.canon fs).map (fun q => (q.1, fitterOf w q.2))) ns xs := by
  rw [Fits, hv, fitters_eq_map, Ty.canon, Field.canonBy_map]

/-- Nothing else is a record value. -/
theorem fits_record_inv (w : World) (v : Val) (fs : List (String × Bool × Ty))
    (h : Fits w v (.record fs)) : ∃ ns xs, recordParts? v = some (ns, xs) ∧
      NamedFit ((Ty.canon fs).map (fun q => (q.1, fitterOf w q.2))) ns xs := by
  cases hv : recordParts? v with
  | none =>
    rw [Fits, hv] at h
    exact h.elim
  | some parts =>
    obtain ⟨ns, xs⟩ := parts
    exact ⟨ns, xs, rfl, (fits_record w hv fs).mp h⟩

/-- A value without record parts is no record's member. -/
theorem fits_record_none (w : World) {v : Val} (hv : recordParts? v = none)
    (fs : List (String × Bool × Ty)) : ¬ Fits w v (.record fs) := by
  rw [Fits, hv]
  exact id

/-- The tuple arm. -/
theorem fits_tuple (w : World) (xs : List Val) (ts : List Ty) :
    Fits w (.list xs) (.tuple ts) ↔ ItemsFit (ts.map (fun t x => Fits w x t)) xs := by
  rw [Fits, itemFitters_eq_map]

/-- The tuple read: the proposition implies the check. -/
theorem itemsFit_hasTy :
    ∀ (ps : List (Val → Prop)) (cs : List (Val → Bool)) (xs : List Val), ps.length = cs.length →
      (∀ pc ∈ ps.zip cs, ∀ x, pc.1 x → pc.2 x = true) → ItemsFit ps xs → itemsHasTy cs xs = true
  | [], [], [], _, _, _ => rfl
  | P :: ps, c :: cs, x :: xs, hlen, hpt, h => by
    simp only [itemsHasTy, Bool.and_eq_true]
    exact ⟨hpt (P, c) List.mem_cons_self x h.1,
      itemsFit_hasTy ps cs xs (Nat.succ.inj hlen) (fun q hq => hpt q (List.mem_cons_of_mem _ hq)) h.2⟩
  | [], [], _ :: _, _, _, h => h.elim
  | [], _ :: _, _, hlen, _, _ => nomatch hlen
  | _ :: _, [], _, hlen, _, _ => nomatch hlen
  | _ :: _, _ :: _, [], _, _, h => h.elim

/-- The tuple read from the check. -/
theorem itemsFit_of_itemsHasTy {β : Type} (P : β → Val → Prop) (c : β → Val → Bool) :
    ∀ (l : List β) (xs : List Val), (∀ t ∈ l, ∀ x, c t x = true → P t x) →
      itemsHasTy (l.map fun t => c t) xs = true → ItemsFit (l.map fun t => P t) xs
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => Bool.noConfusion h
  | _ :: _, [], _, h => Bool.noConfusion h
  | t :: l, x :: xs, hpt, h => by
    simp only [List.map_cons, itemsHasTy, Bool.and_eq_true] at h
    exact ⟨hpt t List.mem_cons_self x h.1,
      itemsFit_of_itemsHasTy P c l xs (fun u hu => hpt u (List.mem_cons_of_mem _ hu)) h.2⟩

/-- A record value fitting the named read: every field is optional or has a member. -/
theorem namedFit_witness :
    ∀ (l : List (String × Bool × (Val → Prop))) (ns xs : List Val), NamedFit l ns xs →
      ∀ q ∈ l, q.2.1 = true ∨ ∃ x, q.2.2 x
  | [], _, _, _ => fun _ hq => absurd hq List.not_mem_nil
  | (n, o, P) :: l, ns, xs, h => by
    intro q hq
    match ns, xs, h with
    | [], [], h =>
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inl h.1
      · exact namedFit_witness l [] [] h.2 q hq
    | [], _ :: _, h => exact h.elim
    | v0 :: _, [], h => cases v0 <;> exact h.elim
    | v0 :: ns, x :: xs, h =>
      cases v0 with
      | str k =>
        simp only [NamedFit] at h
        by_cases hk : k = n
        · rw [if_pos hk] at h
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inr ⟨x, h.1⟩
          · exact namedFit_witness l ns xs h.2 q hq
        · rw [if_neg hk] at h
          rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl h.1
          · exact namedFit_witness l (.str k :: ns) (x :: xs) h.2 q hq
      | _ => exact h.elim

/-- A tuple value: every item predicate has a member. -/
theorem itemsFit_witness :
    ∀ (ps : List (Val → Prop)) (xs : List Val), ItemsFit ps xs → ∀ P ∈ ps, ∃ x, P x
  | [], _, _ => fun _ hP => absurd hP List.not_mem_nil
  | P :: ps, x :: xs, h => by
    intro Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact ⟨x, h.1⟩
    · exact itemsFit_witness ps xs h.2 Q hQ
  | _ :: _, [], h => h.elim

/-- An optional field left out of both lists, when no later name is its own. -/
theorem namedFit_skip (n : String) (o : Bool) (P : Val → Prop)
    (ps : List (String × Bool × (Val → Prop))) (ns xs : List Val) (h : NamedFit ps ns xs)
    (ho : o = true) (hfresh : ∀ k, .str k ∈ ns → k ≠ n) : NamedFit ((n, o, P) :: ps) ns xs := by
  match ns, xs with
  | [], [] => exact ⟨ho, h⟩
  | [], _ :: _ => cases ps <;> exact h.elim
  | v0 :: _, [] => cases v0 <;> cases ps <;> exact h.elim
  | v0 :: ns, x :: xs =>
    cases v0 with
    | str k =>
      simp only [NamedFit]
      rw [if_neg (hfresh k List.mem_cons_self)]
      exact ⟨ho, h⟩
    | _ => cases ps <;> exact h.elim

/-- A field given at its own name. -/
theorem namedFit_cons_eq (n : String) (o : Bool) (P : Val → Prop)
    (ps : List (String × Bool × (Val → Prop))) (ns xs : List Val) (y : Val) :
    NamedFit ((n, o, P) :: ps) (.str n :: ns) (y :: xs) ↔ P y ∧ NamedFit ps ns xs := by
  simp only [NamedFit]
  rw [if_pos trivial]

/-- The named read along a payload map: each field's predicate implies its image's. -/
theorem namedFit_map {β : Type} (P Q : β → Val → Prop) :
    ∀ (l : List (String × Bool × β)) (ns xs : List Val),
      (∀ q ∈ l, ∀ x, P q.2.2 x → Q q.2.2 x) →
      NamedFit (l.map fun q => (q.1, q.2.1, P q.2.2)) ns xs →
      NamedFit (l.map fun q => (q.1, q.2.1, Q q.2.2)) ns xs
  | [], ns, xs, _, h => by
    match ns, xs, h with
    | [], [], _ => trivial
    | [], _ :: _, h => exact h.elim
    | _ :: _, _, h => exact h.elim
  | (n, o, t) :: l, ns, xs, hpt, h => by
    have hl : ∀ q ∈ l, ∀ x, P q.2.2 x → Q q.2.2 x := fun q hq => hpt q (List.mem_cons_of_mem _ hq)
    have ht : ∀ x, P t x → Q t x := hpt (n, o, t) List.mem_cons_self
    match ns, xs, h with
    | [], [], h => exact ⟨h.1, namedFit_map P Q l [] [] hl h.2⟩
    | [], _ :: _, h => exact h.elim
    | v0 :: _, [], h => cases v0 <;> exact h.elim
    | v0 :: ns, x :: xs, h =>
      cases v0 with
      | str k =>
        simp only [List.map_cons, NamedFit] at h ⊢
        by_cases hk : k = n
        · rw [if_pos hk] at h ⊢
          exact ⟨ht x h.1, namedFit_map P Q l ns xs hl h.2⟩
        · rw [if_neg hk] at h ⊢
          exact ⟨h.1, namedFit_map P Q l (.str k :: ns) (x :: xs) hl h.2⟩
      | _ => exact h.elim

/-- The tuple read along an item map. -/
theorem itemsFit_map {β : Type} (P Q : β → Val → Prop) :
    ∀ (l : List β) (xs : List Val), (∀ t ∈ l, ∀ x, P t x → Q t x) →
      ItemsFit (l.map fun t => P t) xs → ItemsFit (l.map fun t => Q t) xs
  | [], [], _, _ => trivial
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | t :: l, x :: xs, hpt, h =>
    ⟨hpt t List.mem_cons_self x h.1,
      itemsFit_map P Q l xs (fun u hu => hpt u (List.mem_cons_of_mem _ hu)) h.2⟩

/-- A list zipped with itself pairs each element with itself. -/
theorem mem_zip_self {α : Type} : ∀ {l : List α} {a b : α}, (a, b) ∈ l.zip l → a = b
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: xs, a, b, h => by
    rw [List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · simp only [Prod.mk.injEq] at h
      rw [h.1, h.2]
    · exact mem_zip_self h

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
  | handle target => intro v h; exact handle_fits_hasTy w h
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
        exact causeFits_admits (fun x hx => ihe x hx) c h.1
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
  | record fs ih =>
    intro v h
    obtain ⟨ns, xs, hv, hfit⟩ := fits_record_inv w v fs h
    rw [Val.hasTy_record hv]
    refine namedFit_hasTy _ _ ns xs ?_ ?_ hfit
    · simp only [List.map_map]
      rfl
    · intro pc hpc x hx
      rw [List.zip_map, List.mem_map] at hpc
      obtain ⟨⟨q1, q2⟩, hq, rfl⟩ := hpc
      have heq : q1 = q2 := mem_zip_self hq
      subst heq
      exact ih q1 (Ty.mem_canon (List.of_mem_zip hq).1) x hx
  | map k t ihk iht =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i es
      simp only [Val.hasTy]
      unfold EntriesFit at h
      unfold entriesHasTy
      rw [Bool.and_eq_true, List.all_eq_true]
      refine ⟨h.1, fun e he => ?_⟩
      have := h.2 e he
      cases e
      case pair a x => exact Bool.and_eq_true_iff.mpr ⟨ihk a this.1, iht x this.2⟩
      all_goals exact this.elim
    · exact h.elim
  | tuple ts ih =>
    intro v h
    cases v
    case list xs =>
      rw [fits_tuple] at h
      rw [Val.hasTy_tuple]
      refine itemsFit_hasTy _ _ xs (by rw [List.length_map, List.length_map]) ?_ h
      intro pc hpc x hx
      rw [List.zip_map, List.mem_map] at hpc
      obtain ⟨⟨t1, t2⟩, ht, rfl⟩ := hpc
      have heq : t1 = t2 := mem_zip_self ht
      subst heq
      exact ih t1 (List.of_mem_zip ht).1 x hx
    all_goals exact h.elim
  | app name args _ =>
    intro v h
    rw [hasTy_app_eq]
    exact handle_fits_hasTy w ((fits_app_iff w v name args).mp h)
  | int | number => intro v h; exact h
  | null | undefined | bytes =>
    intro v h
    simp only [Fits] at h
    split at h
    · rfl
    · exact h.elim

/-! ## Declared liveness follows from membership -/

theorem live_of_handles_nil {w : World} {v : Val} (h : Store.Val.handles v = []) : Live w v := by
  intro k hk
  rw [h] at hk
  cases hk

theorem live_list {w : World} {values : List Val} (h : ∀ x ∈ values, Live w x) :
    Live w (.list values) := by
  intro k hk
  have hk' : k ∈ Store.Val.handlesList values := hk
  rw [Store.Val.handlesList_eq_flatMap, List.mem_flatMap] at hk'
  obtain ⟨x, hx, hkx⟩ := hk'
  exact h x hx k hkx

theorem live_ctor {w : World} {i : Nat} {args : List Val} (h : ∀ x ∈ args, Live w x) :
    Live w (.ctor i args) := by
  intro k hk
  have hk' : k ∈ Store.Val.handlesList args := hk
  rw [Store.Val.handlesList_eq_flatMap, List.mem_flatMap] at hk'
  obtain ⟨x, hx, hkx⟩ := hk'
  exact h x hx k hkx

theorem live_ctor_one {w : World} {i : Nat} {x : Val} (h : Live w x) : Live w (.ctor i [x]) :=
  live_ctor fun y hy => by
    rw [List.mem_singleton] at hy
    subst hy
    exact h

/-- A reified failed exit names no handle: the cause image writes none (`causeImage_handleFree`). -/
theorem handles_exitErr (c : CauseV) : Store.Val.handles (Val.exitErr c) = [] := by
  show Store.Val.handles (.ctor 1 [causeImage.toVal c]) = []
  rw [Store.Val.handles, Store.Val.handlesList_cons, causeImage_handleFree c,
    Store.Val.handlesList_nil]
  rfl

/-- A reified cause names no handle. -/
theorem handles_of_cause {v : Val} {c : CauseV} (h : Val.cause? v = some c) :
    Store.Val.handles v = [] := by
  unfold Val.cause? at h
  split at h
  · rename_i written
    rw [Store.Image.ofVal_exact causeImage h]
    exact handles_exitErr c
  · exact nomatch h

/-- One handle frame of a registered kind is live when its column holds it. -/
theorem live_kind {w : World} {k : HandleKind} {index : Nat} (h : KindLive w index (some k)) :
    Live w (.handle k.byte index) := by
  intro x hx
  have hx' : x ∈ [(k.byte, index)] := hx
  rw [List.mem_singleton] at hx'
  subst hx'
  show KindLive w index (HandleKind.ofByte? k.byte)
  rw [HandleKind.ofByte?_byte]
  exact h

theorem live_fiber {w : World} {index : Nat} {a e : Ty} (h : FiberDeclared w ⟨index⟩ a e) :
    Live w (Value.fiber index) := by
  obtain ⟨fty, hΓ, _⟩ := h
  refine live_kind (k := .fiber) ?_
  show (w.Γ ⟨index⟩).isSome = true
  rw [hΓ]
  rfl

theorem live_cell {w : World} {index : Nat} {t : Ty} (h : RefDeclared w ⟨index⟩ t) :
    Live w (Value.cell index) := by
  obtain ⟨t', hΡ, _⟩ := h
  refine live_kind (k := .cell) ?_
  show (w.Ρ ⟨index⟩).isSome = true
  rw [hΡ]
  rfl

theorem live_promise {w : World} {index : Nat} {a e : Ty}
    (h : PromiseDeclared w ⟨index⟩ a e) : Live w (Value.promise index) := by
  obtain ⟨a', e', hPi, _⟩ := h
  refine live_kind (k := .promise) ?_
  show (w.«Π» ⟨index⟩).isSome = true
  rw [hPi]
  rfl

theorem live_handle {w : World} {kind : UInt8} {index : Nat} {target : String}
    (h : HandleFits w kind index target) : Live w (.handle kind index) := by
  simp only [HandleFits] at h
  split at h
  · rename_i hk
    rw [HandleKind.ofByte?_exact hk]
    exact live_kind (k := .scope) h.2
  · rename_i hk
    rw [HandleKind.ofByte?_exact hk]
    exact live_kind (k := .memoMap) h.2
  · rename_i hk
    rw [HandleKind.ofByte?_exact hk]
    exact live_kind (k := .external) (List.getElem?_eq_some_iff.mp h.2).1
  · exact h.elim

theorem live_some {w : World} {x : Val} (h : Live w x) : Live w (.some x) := h

theorem live_pair {w : World} {a x : Val} (ha : Live w a) (hx : Live w x) : Live w (.pair a x) := by
  intro k hk
  have hk' : k ∈ Store.Val.handles a ++ Store.Val.handles x := hk
  rcases List.mem_append.mp hk' with h | h
  · exact ha k h
  · exact hx k h

/-- **Capability membership is the store's validity**, given the store's forward bounds (the
heap and the Deferred cells hold every declared index; `CellsTyped.heap`, `.promises`). Codex's
`rawLive_validIn` (`m6-adoption-next/RawLiveBridge.lean`), on the restated `Live`. -/
theorem live_validIn {w : World} {v : Val}
    (heap : ∀ k, (w.Ρ k).isSome = true → k.index < w.state.refs.length)
    (promises : ∀ k, (w.«Π» k).isSome = true → k.index < w.state.deferreds.cells.length)
    (live : Live w v) : v.validIn w.state = true := by
  rw [Val.validIn_eq_handles, List.all_eq_true]
  intro h hh
  have hl := live h hh
  unfold Stores.handleValid
  cases hk : HandleKind.ofByte? h.1 with
  | none =>
    rw [hk] at hl
    exact hl.elim
  | some k =>
    rw [hk] at hl
    cases k with
    | cell => exact decide_eq_true (heap ⟨h.2⟩ hl)
    | promise => exact decide_eq_true (promises ⟨h.2⟩ hl)
    | fiber => rfl
    | scope => exact hl
    | memoMap => exact hl
    | external => exact decide_eq_true hl

/-- The handle arm keeps declared liveness (shared by a nominal reference, `fits_app_iff`). -/
theorem handle_fits_live {w : World} {v : Val} {target : String} (h : Fits w v (.handle target)) :
    Live w v := by
  simp only [Fits] at h
  split at h
  · exact live_handle h
  · obtain ⟨_, _, _, _, hl⟩ := h
    exact hl

theorem intImage_handles {v : Val} (h : intImage v = true) : Store.Val.handles v = [] := by
  unfold intImage at h
  split at h
  · rfl
  · rfl
  · exact Bool.noConfusion h

theorem numberImage_handles {v : Val} (h : numberImage v = true) : Store.Val.handles v = [] := by
  unfold numberImage at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact intImage_handles h
  · split at h
    · rfl
    · exact Bool.noConfusion h

/-- A record value's names and values are live when every canonical field's members are. -/
theorem namedFit_live {w : World} :
    ∀ (ps : List (String × Bool × (Val → Prop))) (ns xs : List Val),
      (∀ p ∈ ps, ∀ y, p.2.2 y → Live w y) → NamedFit ps ns xs →
      (∀ x ∈ ns, Live w x) ∧ (∀ x ∈ xs, Live w x)
  | [], [], [], _, _ => ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  | [], [], _ :: _, _, h => h.elim
  | [], _ :: _, _, _, h => h.elim
  | (n, o, P) :: ps, ns, xs, hp, h => by
    have hP := hp (n, o, P) List.mem_cons_self
    have hp' : ∀ q ∈ ps, ∀ y, q.2.2 y → Live w y := fun q hq => hp q (List.mem_cons_of_mem _ hq)
    match ns, xs, h with
    | [], [], h => exact namedFit_live ps [] [] hp' h.2
    | [], _ :: _, h => exact h.elim
    | v0 :: _, [], h => cases v0 <;> exact h.elim
    | v0 :: ns, x :: xs, h =>
      cases v0 with
      | str k =>
        simp only [NamedFit] at h
        by_cases hk : k = n
        · rw [if_pos hk] at h
          obtain ⟨hns, hxs⟩ := namedFit_live ps ns xs hp' h.2
          refine ⟨fun y hy => ?_, fun y hy => ?_⟩
          · rcases List.mem_cons.mp hy with rfl | hy
            · exact live_of_handles_nil rfl
            · exact hns y hy
          · rcases List.mem_cons.mp hy with rfl | hy
            · exact hP y h.1
            · exact hxs y hy
        · rw [if_neg hk] at h
          exact namedFit_live ps (.str k :: ns) (x :: xs) hp' h.2
      | _ => exact h.elim

/-- A tuple's items are live when every position's members are. -/
theorem itemsFit_live {w : World} :
    ∀ (ps : List (Val → Prop)) (xs : List Val), (∀ P ∈ ps, ∀ y, P y → Live w y) → ItemsFit ps xs →
      ∀ x ∈ xs, Live w x
  | _, [], _, _ => fun _ hx => absurd hx List.not_mem_nil
  | P :: ps, x :: xs, hp, h => by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hp P List.mem_cons_self z h.1
    · exact itemsFit_live ps xs (fun Q hQ => hp Q (List.mem_cons_of_mem _ hQ)) h.2 z hz
  | [], _ :: _, _, h => h.elim

/-- **Membership implies capability membership**, at every type. -/
theorem fits_live (w : World) : ∀ (ty : Ty) (v : Val), Fits w v ty → Live w v := by
  intro ty
  induction ty with
  | never => intro v h; exact h.elim
  | unit =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_of_handles_nil rfl
    · exact h.elim
  | nat =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_of_handles_nil rfl
    · exact h.elim
  | string =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_of_handles_nil rfl
    · exact h.elim
  | bool =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_of_handles_nil rfl
    · exact h.elim
  | handle target => intro v h; exact handle_fits_live h
  | option a ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_of_handles_nil rfl
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
        refine live_ctor_one (live_list fun x hx => ?_)
        obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hx
        exact ih _ (h id hid)
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
        refine live_ctor_one (live_of_handles_nil ?_)
        rw [Store.Image.ofVal_exact causeImage hc]
        exact causeImage_handleFree c
      · exact h.elim
    · exact h.elim
  | causeOf e _ =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i c hc
      exact live_of_handles_nil (handles_of_cause hc)
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
    · exact live_of_handles_nil rfl
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
    obtain ⟨ns, xs, hv, hfit⟩ := fits_record_inv w v fs h
    have hp : ∀ p ∈ (Ty.canon fs).map (fun q => (q.1, fitterOf w q.2)), ∀ y, p.2.2 y → Live w y := by
      intro p hp y hy
      rw [List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      exact ih q (Ty.mem_canon hq) y hy
    obtain ⟨hns, hxs⟩ := namedFit_live _ ns xs hp hfit
    rw [recordParts?_eq_some hv]
    refine live_ctor fun y hy => ?_
    rw [List.mem_cons, List.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact live_list hns
    · exact live_list hxs
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
  | tuple ts ih =>
    intro v h
    cases v
    case list xs =>
      rw [fits_tuple] at h
      refine live_list (itemsFit_live _ xs ?_ h)
      intro P hP y hy
      rw [List.mem_map] at hP
      obtain ⟨t, ht, rfl⟩ := hP
      exact ih t ht y hy
    all_goals exact h.elim
  | app name args _ => intro v h; exact handle_fits_live ((fits_app_iff w v name args).mp h)
  | int => intro v h; exact live_of_handles_nil (intImage_handles h)
  | number => intro v h; exact live_of_handles_nil (numberImage_handles h)
  | null | undefined | bytes =>
    intro v h
    simp only [Fits] at h
    split at h
    · exact live_of_handles_nil rfl
    · exact h.elim

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
  (hstore : w1.state.le w2.state)
include hΓ hPi hRho

include halloc hstore in
/-- A handle frame's column moves along the tables and the store: scopes and memo maps are never
removed (`Stores.le`), externals only grow. -/
theorem kindLive_map {index : Nat} {k : Option HandleKind} (h : KindLive w1 index k) :
    KindLive w2 index k := by
  cases k with
  | none => exact h
  | some k =>
    cases k with
    | cell => exact isSome_extends hRho h
    | promise => exact isSome_extends hPi h
    | fiber => exact isSome_extends hΓ h
    | scope => exact hstore.2.2.1 index h
    | memoMap => exact hstore.2.2.2.2.1 ⟨index⟩ h
    | external =>
      obtain ⟨t, ht⟩ : ∃ t, w1.state.externals.allocated[index]? = some t :=
        ⟨_, List.getElem?_eq_getElem h⟩
      exact (List.getElem?_eq_some_iff.mp (halloc index t ht)).1

include halloc hstore in
theorem live_map {v : Val} (h : Live w1 v) : Live w2 v :=
  fun k hk => kindLive_map hΓ hPi hRho halloc hstore (h k hk)

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

include halloc hstore in
omit hΓ hPi hRho in
/-- A handle's membership moves along the store and the allocation table (row 156: a scope handle
needs its scope present in the later world too; row 187 amended: a memo map handle its map). No
handle spelling reads a declaration table since the state plan's T3a. -/
theorem handleFits_map {kind : UInt8} {index : Nat} {target : String}
    (h : HandleFits w1 kind index target) : HandleFits w2 kind index target := by
  simp only [HandleFits] at h ⊢
  split at h
  · exact ⟨h.1, hstore.2.2.1 index h.2⟩
  · exact ⟨h.1, hstore.2.2.2.2.1 ⟨index⟩ h.2⟩
  · exact ⟨h.1, halloc index target h.2⟩
  · exact h.elim

include halloc hstore in
omit hΓ hPi in
theorem flatFits_map {v : Val} {t : Ty} (h : FlatFits w1 v t) : FlatFits w2 v t := by
  cases t
  case unit => exact h
  case nat => exact h
  case bool => exact h
  case string => exact h
  case handle target =>
    simp only [FlatFits] at h ⊢
    split at h
    · exact handleFits_map halloc hstore h
    · exact h.elim
  case refOf t =>
    simp only [FlatFits] at h ⊢
    split at h
    · exact refDeclared_map hRho h
    · exact h.elim
  all_goals exact h.elim

include halloc hstore in
/-- A context's services fit in a later world when every carrier the later world reads was the
earlier world's (the lookup agreement of decisions row 112; the world order gives it as an
equality of the two tables) and every scope it names is still present (row 156); its values stay
live (`live_map`). -/
theorem servicesFit_map {services : Env.Ctx}
    (hsvc : ∀ key sty, w2.serviceTy key = some sty → w1.serviceTy key = some sty)
    (h : ServicesFit w1 services) : ServicesFit w2 services :=
  ⟨fun key sv sty hget hty =>
    flatFits_map hRho halloc hstore (h.1 key sv sty hget (hsvc key sty hty)),
   fun e he => live_map hΓ hPi hRho halloc hstore (h.2 e he)⟩

end Map

/-- Pointwise stronger field predicates with the same names, and flags that only grow, admit more
(the named read). -/
theorem namedFit_mono :
    ∀ (ps qs : List (String × Bool × (Val → Prop))) (ns xs : List Val),
      ps.map Prod.fst = qs.map Prod.fst →
      (∀ pq ∈ ps.zip qs, (pq.1.2.1 = true → pq.2.2.1 = true) ∧ ∀ x, pq.1.2.2 x → pq.2.2.2 x) →
      NamedFit ps ns xs → NamedFit qs ns xs
  | [], [], _, _, _, _, h => h
  | [], _ :: _, _, _, hh, _, _ => nomatch hh
  | _ :: _, [], _, _, hh, _, _ => nomatch hh
  | (n, o, P) :: ps, (m, p, Q) :: qs, ns, xs, hh, hpt, h => by
    simp only [List.map_cons, List.cons.injEq] at hh
    obtain ⟨rfl, hrest⟩ := hh
    obtain ⟨hop, hPQ⟩ := hpt ((n, o, P), (n, p, Q)) List.mem_cons_self
    have hpt' : ∀ pq ∈ ps.zip qs,
        (pq.1.2.1 = true → pq.2.2.1 = true) ∧ ∀ x, pq.1.2.2 x → pq.2.2.2 x :=
      fun pq hpq => hpt pq (List.mem_cons_of_mem _ hpq)
    match ns, xs, h with
    | [], [], h => exact ⟨hop h.1, namedFit_mono ps qs [] [] hrest hpt' h.2⟩
    | [], _ :: _, h => exact h.elim
    | v0 :: _, [], h => cases v0 <;> exact h.elim
    | v0 :: ns, x :: xs, h =>
      cases v0 with
      | str k =>
        simp only [NamedFit] at h ⊢
        by_cases hk : k = n
        · rw [if_pos hk] at h ⊢
          exact ⟨hPQ x h.1, namedFit_mono ps qs ns xs hrest hpt' h.2⟩
        · rw [if_neg hk] at h ⊢
          exact ⟨hop h.1, namedFit_mono ps qs (.str k :: ns) (x :: xs) hrest hpt' h.2⟩
      | _ => exact h.elim

/-- Pointwise stronger predicates of one arity admit more (the tuple read). -/
theorem itemsFit_mono :
    ∀ (ps qs : List (Val → Prop)) (xs : List Val), ps.length = qs.length →
      (∀ pq ∈ ps.zip qs, ∀ x, pq.1 x → pq.2 x) → ItemsFit ps xs → ItemsFit qs xs
  | [], [], _, _, _, h => h
  | P :: ps, Q :: qs, x :: xs, hlen, hpt, h =>
    ⟨hpt (P, Q) List.mem_cons_self x h.1,
      itemsFit_mono ps qs xs (Nat.succ.inj hlen) (fun q hq => hpt q (List.mem_cons_of_mem _ hq)) h.2⟩
  | _ :: _, _ :: _, [], _, _, h => h.elim
  | [], _ :: _, _, hlen, _, _ => nomatch hlen
  | _ :: _, [], _, hlen, _, _ => nomatch hlen

/-- The handle arm moves to a later world (shared by a nominal reference, `fits_app_iff`). -/
theorem handle_fits_map {w1 w2 : World}
    (hΓ : TableExtends w1.Γ w2.Γ) (hPi : TableExtends w1.«Π» w2.«Π») (hRho : TableExtends w1.Ρ w2.Ρ)
    (halloc : Extends w1.state.externals.allocated w2.state.externals.allocated)
    (hstore : w1.state.le w2.state)
    (hsvc : ∀ key sty, w2.serviceTy key = some sty → w1.serviceTy key = some sty)
    {v : Val} {target : String} (h : Fits w1 v (.handle target)) : Fits w2 v (.handle target) := by
  simp only [Fits] at h
  split at h
  · exact handleFits_map halloc hstore h
  · obtain ⟨ht, ctx, hctx, hs, hl⟩ := h
    simp only [Fits]
    exact ⟨ht, ctx, hctx, servicesFit_map hΓ hPi hRho halloc hstore hsvc hs, live_map hΓ hPi hRho halloc hstore hl⟩

/-- Membership moves to a world whose declaration tables and allocation spellings extend
the old ones, whose store grows (`Stores.le`: every present scope and memo map stays, rows 156 and
187), and whose service table agrees on every key it types. -/
theorem fits_map {w1 w2 : World}
    (hΓ : TableExtends w1.Γ w2.Γ) (hPi : TableExtends w1.«Π» w2.«Π») (hRho : TableExtends w1.Ρ w2.Ρ)
    (halloc : Extends w1.state.externals.allocated w2.state.externals.allocated)
    (hstore : w1.state.le w2.state)
    (hsvc : ∀ key sty, w2.serviceTy key = some sty → w1.serviceTy key = some sty) :
    ∀ (ty : Ty) (v : Val), Fits w1 v ty → Fits w2 v ty := by
  intro ty
  induction ty with
  | never => intro v h; exact h.elim
  | unit => intro v h; exact h
  | nat => intro v h; exact h
  | string => intro v h; exact h
  | bool => intro v h; exact h
  | handle target => intro v h; exact handle_fits_map hΓ hPi hRho halloc hstore hsvc h
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
        exact ⟨causeFits_map (fun x hx => ihe x hx) h.1, h.2⟩
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
  | unknown => intro v h; exact live_map hΓ hPi hRho halloc hstore h
  | record fs ih =>
    intro v h
    obtain ⟨ns, xs, hv, hfit⟩ := fits_record_inv w1 v fs h
    rw [fits_record w2 hv]
    refine namedFit_mono _ _ ns xs ?_ ?_ hfit
    · simp only [List.map_map]
      rfl
    · intro pq hpq
      rw [List.zip_map, List.mem_map] at hpq
      obtain ⟨⟨q1, q2⟩, hq, rfl⟩ := hpq
      have heq : q1 = q2 := mem_zip_self hq
      subst heq
      exact ⟨id, fun x hx => ih q1 (Ty.mem_canon (List.of_mem_zip hq).1) x hx⟩
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
  | tuple ts ih =>
    intro v h
    cases v
    case list xs =>
      rw [fits_tuple] at h ⊢
      refine itemsFit_mono _ _ xs (by rw [List.length_map, List.length_map]) ?_ h
      intro pq hpq x hx
      rw [List.zip_map, List.mem_map] at hpq
      obtain ⟨⟨t1, t2⟩, ht, rfl⟩ := hpq
      have heq : t1 = t2 := mem_zip_self ht
      subst heq
      exact ih t1 (List.of_mem_zip ht).1 x hx
    all_goals exact h.elim
  | app name args _ =>
    intro v h
    exact (fits_app_iff w2 v name args).mpr
      (handle_fits_map hΓ hPi hRho halloc hstore hsvc ((fits_app_iff w1 v name args).mp h))
  | int | null | undefined | number | bytes => intro v h; exact h

/-- The world order fixes the service table, so a later world's lookups are the earlier one's. -/
theorem serviceTy_of_le {w w' : World} (ordered : w.le w') :
    ∀ key sty, w'.serviceTy key = some sty → w.serviceTy key = some sty :=
  fun _ _ h => le_serviceTy ordered ▸ h

/-- Membership is monotone under the host world order. -/
theorem fits_mono {w w' : World} (ordered : w.leHost w') {ty : Ty} {v : Val} (h : Fits w v ty) :
    Fits w' v ty :=
  fits_map ordered.1.2.1 ordered.1.2.2.1 ordered.1.2.2.2.1 ordered.2 ordered.1.1.2
    (serviceTy_of_le ordered.1) ty v h

/-! ## Scope handles: membership owns presence (decisions row 156) -/

/-- **A member of `Ty.scope` is a present scope's handle** (row 156): the handle former's scope arm
reads the scope store, and no other arm accepts the scope target. The posts that answer a scope
handle state `Fits w' ans Ty.scope`; their consumers read the scope back here. -/
theorem fits_scope_inv {w : World} {v : Val} (h : Fits w v Ty.scope) :
    ∃ sc, v = Val.scopeHandle sc ∧ ScopeLive w sc := by
  change Fits w v (.handle Ty.scopeTarget) at h
  simp only [Fits] at h
  split at h
  · rename_i kind index
    simp only [HandleFits] at h
    split at h
    · rename_i hk
      have hkind : kind = HandleKind.scope.byte := HandleKind.ofByte?_exact hk
      subst hkind
      exact ⟨index, rfl, h.2⟩
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)
    · exact h.elim
  · exact absurd h.1 (by decide)

/-- A present scope's handle is a member of `Ty.scope`. -/
theorem fits_scopeHandle (w : World) (sc : Nat) (h : ScopeLive w sc) :
    Fits w (Val.scopeHandle sc) Ty.scope :=
  ⟨rfl, h⟩

/-! ## Subsumption: membership respects the checker's subtyping -/

/-! ## The leaf table's obligation in `Fits`: one line per edge (decisions rows 121, 160, 177)

A leaf head's members are its representative's (`leafRep`: a literal's is `string`, the union of
every literal's members). A type's members are among its head's representative's (`fits_leafRep`),
and at a payload-free head the two are one (`fits_of_leafRep`). An edge's obligation is the
inclusion of its source's representative's members in its target's (`fits_leafEdge`: one line per
edge, where the nesting images of row 121 are what make `nat ⊑ int ⊑ number` inclusions); the
closure needs nothing more, because a path carries the inclusion along (`fits_leafPath`) and no
edge enters `lit`. -/

/-- A leaf head's representative type: the type whose members are every type's of that head. -/
def leafRep : Ty.LeafHead → Ty
  | .lit => .string
  | .string => .string
  | .nat => .nat
  | .int => .int
  | .number => .number
  | .undefined => .undefined
  | .unit => .unit

theorem fits_leafRep {t : Ty} {x : Ty.LeafHead} (h : Ty.leafHead t = some x) (w : World) (v : Val)
    (hv : Fits w v t) : Fits w v (leafRep x) := by
  cases t
  case lit s =>
    cases h
    cases v
    case str => trivial
    all_goals exact hv.elim
  case string | nat | int | number | undefined | unit => cases h; exact hv
  all_goals cases h

theorem fits_of_leafRep {t : Ty} {x : Ty.LeafHead} (h : Ty.leafHead t = some x) (hx : x ≠ .lit)
    (w : World) (v : Val) (hv : Fits w v (leafRep x)) : Fits w v t := by
  cases t
  case lit => cases h; exact absurd rfl hx
  case string | nat | int | number | undefined | unit => cases h; exact hv
  all_goals cases h

/-- **The membership obligation of the leaf table: one line per edge.** -/
theorem fits_leafEdge {x y : Ty.LeafHead} (he : (x, y) ∈ Ty.leafEdges) (w : World) (v : Val)
    (hv : Fits w v (leafRep x)) : Fits w v (leafRep y) := by
  simp only [Ty.leafEdges, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hv                                      -- lit → string
  · cases v                                        -- nat → int: a natural is its own image
    case nat => rfl
    all_goals exact hv.elim
  · show (intImage v || _) = true                  -- int → number
    rw [show intImage v = true from hv, Bool.true_or]
  · cases v <;> exact hv                           -- undefined → unit: one image

/-- No declared edge enters a literal. -/
theorem leafEdges_target_ne_lit (e : Ty.LeafHead × Ty.LeafHead) (he : e ∈ Ty.leafEdges) :
    e.2 ≠ .lit := by
  have hall : ∀ e ∈ Ty.leafEdges, e.2 ≠ .lit := by decide
  exact hall e he

theorem fits_leafPath {x y : Ty.LeafHead} (h : Ty.LeafPath Ty.leafEdges x y) (w : World) (v : Val)
    (hv : Fits w v (leafRep x)) : Fits w v (leafRep y) := by
  induction h with
  | refl => exact hv
  | step he _ ih => exact ih (fits_leafEdge he w v hv)

/-- A path's target is its source or an edge's target. -/
theorem leafPath_target {x y : Ty.LeafHead} (h : Ty.LeafPath Ty.leafEdges x y) :
    y = x ∨ ∃ e ∈ Ty.leafEdges, e.2 = y := by
  induction h with
  | refl => exact Or.inl rfl
  | step he _ ih =>
    rcases ih with rfl | ⟨e, he', hy⟩
    · exact Or.inr ⟨_, he, rfl⟩
    · exact Or.inr ⟨e, he', hy⟩

/-- **The table's rule keeps membership**: no edge is named. -/
theorem fits_leafRule {a b : Ty} (h : Ty.leafRule a b = true) (w : World) (v : Val)
    (hv : Fits w v a) : Fits w v b := by
  obtain ⟨x, y, hx, hy, hxy, hle⟩ := Ty.leafRule_eq_true h
  have hpath := Ty.leafLe_iff_path.mp hle
  have hy_ne : y ≠ .lit := by
    rcases leafPath_target hpath with hyx | ⟨e, he, rfl⟩
    · exact absurd hyx.symm hxy
    · exact leafEdges_target_ne_lit e he
  exact fits_of_leafRep hy hy_ne w v (fits_leafPath hpath w v (fits_leafRep hx w v hv))

/-- Equal canonical heads pair every field with a field of the same flag. -/
theorem heads_zip_flag {cf cg : List (String × Bool × Ty)}
    (hh : cf.map (fun p => (p.1, p.2.1)) = cg.map (fun p => (p.1, p.2.1)))
    {q1 q2 : String × Bool × Ty} (hq : (q1, q2) ∈ cf.zip cg) : q1.2.1 = q2.2.1 := by
  induction cf generalizing cg with
  | nil => exact absurd hq (by rw [List.zip_nil_left]; exact List.not_mem_nil)
  | cons a cf ih =>
    cases cg with
    | nil => exact absurd hq (by rw [List.zip_nil_right]; exact List.not_mem_nil)
    | cons b cg =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hh
      rw [List.zip_cons_cons, List.mem_cons] at hq
      rcases hq with hq | hq
      · simp only [Prod.mk.injEq] at hq
        rw [hq.1, hq.2]
        exact hh.1.2
      · exact ih hh.2 hq

/-- **Fits is closed under `Ty.sub`.** By `fun_induction Ty.sub`, so the cases are `sub`'s own arms
(as `cata_admits_sub`, `Laws/Program/Admits.lean`): `case2` is the leaf table's line
(`fits_leafRule`, naming no edge); the record case reads the named read's monotonicity; the handle
arms move the raw step into the checker's order (`Ty.sub_le_subN`) and compose there
(`Ty.subN_trans`); a nominal reference is the handle at its name, its arguments unread. -/
theorem fits_sub (w : World) {a b : Ty} (hsub : Ty.sub a b = true) : ∀ v, Fits w v a → Fits w v b := by
  fun_induction Ty.sub a b
  case case1 => intro v h; exact h
  case case2 a b _ hl => intro v h; exact fits_leafRule hl w v h
  case case3 => intro v h; exact h.elim
  case case4 a1 a2 b _ _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    exact h.elim (iha h1 v) (ihb h2 v)
  case case5 a b1 b2 _ _ _ _ iha ihb =>
    intro v h
    exact (Bool.or_eq_true_iff.mp hsub).elim (fun hx => Or.inl (iha hx v h))
      (fun hx => Or.inr (ihb hx v h))
  case case6 => intro v h; exact fits_live w _ v h
  case case7 x y _ _ ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · trivial
    · rename_i z
      exact ih hsub z h
    · exact h.elim
  case case8 x y _ _ ih =>
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
  case case9 a1 a2 b1 b2 _ _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits] at h
    split at h
    · exact ⟨iha h1 _ h.1, ihb h2 _ h.2⟩
    · exact h.elim
  case case10 e1 a1 e2 a2 _ _ ihe iha =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits] at h
    split at h
    · exact ihe h1 _ h
    · exact iha h2 _ h
    · exact h.elim
  case case11 a1 e1 a2 e2 _ _ iha ihe =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits] at h
    split at h
    · exact iha h1 _ h
    · rename_i written
      split at h
      · rename_i c hc
        simp only [Fits, hc]
        exact ⟨causeFits_map (fun x hx => ihe h2 x hx) h.1, h.2⟩
      · exact h.elim
    · exact h.elim
  case case12 e1 e2 _ _ ih =>
    intro v h
    simp only [Fits] at h
    split at h
    · rename_i c hc
      simp only [Fits, hc]
      exact causeFits_map (fun x hx => ih hsub x hx) h
    · exact h.elim
  case case13 a1 e1 a2 e2 _ _ _ _ =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits] at h
    split at h
    · obtain ⟨fty, hs, ha, he⟩ := h
      exact ⟨fty, hs, Ty.subN_trans ha (Ty.sub_le_subN h1), Ty.subN_trans he (Ty.sub_le_subN h2)⟩
    · exact h.elim
  case case14 a1 a2 _ _ _ _ =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v h
    simp only [Fits] at h
    split at h
    · obtain ⟨t', hs, hl, hr⟩ := h
      exact ⟨t', hs, Ty.subN_trans hl (Ty.sub_le_subN h1), Ty.subN_trans (Ty.sub_le_subN h2) hr⟩
    · exact h.elim
  case case15 a1 e1 a2 e2 _ _ _ _ _ _ =>
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
  case case16 fs gs _ _ ih =>
    obtain ⟨hh, hall⟩ := Bool.and_eq_true_iff.mp hsub
    have hh' := of_decide_eq_true hh
    have hall' : ((Ty.canon fs).zip (Ty.canon gs)).all (fun pq => Ty.sub pq.1.2.2 pq.2.2.2) = true := by
      rw [← Ty.all_attach_eq]
      exact hall
    rw [List.all_eq_true] at hall'
    intro v h
    obtain ⟨ns, xs, hv, hfit⟩ := fits_record_inv w v fs h
    rw [fits_record w hv]
    refine namedFit_mono _ _ ns xs ?_ ?_ hfit
    · have hn := congrArg (List.map Prod.fst) hh'
      simp only [List.map_map, Function.comp_def] at hn ⊢
      exact hn
    · intro pq hpq
      rw [List.zip_map, List.mem_map] at hpq
      obtain ⟨⟨q1, q2⟩, hq, rfl⟩ := hpq
      refine ⟨fun hf => ?_, fun x hx => ih (q1, q2) hq (hall' (q1, q2) hq) x hx⟩
      have he : q1.2.1 = q2.2.1 := heads_zip_flag hh' hq
      show q2.2.1 = true
      rw [← he]
      exact hf
  case case17 k1 v1 k2 v2 _ _ ihk _ ihv =>
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
  case case18 ts us _ _ ih =>
    obtain ⟨hlen, hall⟩ := Bool.and_eq_true_iff.mp hsub
    have hlen' : ts.length = us.length := of_decide_eq_true hlen
    have hall' : (ts.zip us).all (fun pq => Ty.sub pq.1 pq.2) = true := by
      rw [← Ty.all_attach_eq]
      exact hall
    rw [List.all_eq_true] at hall'
    intro v h
    cases v
    case list xs =>
      rw [fits_tuple] at h ⊢
      refine itemsFit_mono _ _ xs (by rw [List.length_map, List.length_map, hlen']) ?_ h
      intro p hp x hx
      rw [List.zip_map, List.mem_map] at hp
      obtain ⟨⟨t, u⟩, htu, rfl⟩ := hp
      exact ih (t, u) htu (hall' (t, u) htu) x hx
    all_goals exact h.elim
  case case19 n1 xs n2 ys _ _ _ _ =>
    obtain ⟨hnm, _⟩ := Bool.and_eq_true_iff.mp hsub
    obtain ⟨hn, _⟩ := Bool.and_eq_true_iff.mp hnm
    have hn' : n1 = n2 := of_decide_eq_true hn
    subst hn'
    intro v h
    exact h
  case case20 => exact Bool.noConfusion hsub

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
  | record _ _ => exact exists_mem_singleton_iff _ _
  | map _ _ _ _ => exact exists_mem_singleton_iff _ _
  | tuple _ _ => exact exists_mem_singleton_iff _ _
  | app _ _ _ => exact exists_mem_singleton_iff _ _
  | null => exact exists_mem_singleton_iff _ _
  | undefined => exact exists_mem_singleton_iff _ _
  | number => exact exists_mem_singleton_iff _ _
  | bytes => exact exists_mem_singleton_iff _ _

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

/-- The record case of `fits_normalize`, named: normalizing a record maps its canonical list
(names and flags kept), and a normalized field type has its field type's members. -/
theorem fits_normalize_record (w : World) (fs : List (String × Bool × Ty)) (v : Val)
    (ih : ∀ p ∈ fs, ∀ v, Fits w v (Ty.normalize p.2.2) ↔ Fits w v p.2.2) :
    Fits w v (Ty.normalize (.record fs)) ↔ Fits w v (.record fs) := by
  rw [Ty.normalize_record]
  cases hv : recordParts? v with
  | none => exact iff_of_false (fits_record_none w hv _) (fits_record_none w hv _)
  | some parts =>
    obtain ⟨ns, xs⟩ := parts
    rw [fits_record w hv, fits_record w hv, Ty.canon,
      Field.canonBy_of_ascending _ (Field.ascending_map Ty.normPayload (Field.canonBy_ascending fs)),
      List.map_map]
    have hmap : (Field.canonBy Field.bytesKey fs).map
          ((fun q => (q.1, fitterOf w q.2)) ∘ (fun q => (q.1, Ty.normPayload q.2))) =
        (Field.canonBy Field.bytesKey fs).map (fun q => (q.1, fitterOf w q.2)) := by
      apply List.map_congr_left
      intro q hq
      have hfun : (fun x => Fits w x (Ty.normalize q.2.2)) = fun x => Fits w x q.2.2 :=
        funext fun x => propext (ih q (Field.mem_canonBy hq) x)
      simp only [Function.comp_apply, fitterOf, Ty.normPayload]
      rw [hfun]
    rw [hmap]

/-- A pair tuple and a product have the same members. -/
theorem fits_tuple_pair (w : World) (v : Val) (a b : Ty) :
    Fits w v (.tuple [a, b]) ↔ Fits w v (.prod a b) := by
  cases v
  case list xs =>
    rw [fits_tuple]
    match xs with
    | [] => exact Iff.rfl
    | [_] => exact ⟨fun h => h.2.elim, fun h => h.elim⟩
    | [_, _] => exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, trivial⟩⟩
    | _ :: _ :: _ :: _ => exact ⟨fun h => h.2.2.elim, fun h => h.elim⟩
  all_goals exact Iff.rfl

/-- The product case of `fits_normalize`, extracted so the pair tuple reads it. -/
theorem fits_normalize_prod (w : World) (a b : Ty) (v : Val)
    (iha : ∀ v, Fits w v a.normalize ↔ Fits w v a) (ihb : ∀ v, Fits w v b.normalize ↔ Fits w v b) :
    Fits w v (Ty.normalize (.prod a b)) ↔ Fits w v (.prod a b) := by
  show Fits w v (Ty.ofMembers (Ty.normalizeRow (Ty.productMembers a.normalize b.normalize)).elems) ↔
    Fits w v (.prod a b)
  rw [fits_ofMembers, fits_normalizeRow, fits_productMembers, fits_prod_iff, fits_prod_iff]
  constructor
  · rintro ⟨p, q, hv, hp, hq⟩
    exact ⟨p, q, hv, (iha p).mp hp, (ihb q).mp hq⟩
  · rintro ⟨p, q, hv, hp, hq⟩
    exact ⟨p, q, hv, (iha p).mpr hp, (ihb q).mpr hq⟩

/-- The tuple case: a pair is a product, any other arity in place. -/
theorem fits_normalize_tuple (w : World) (ts : List Ty) (v : Val)
    (ih : ∀ t ∈ ts, ∀ v, Fits w v (Ty.normalize t) ↔ Fits w v t) :
    Fits w v (Ty.normalize (.tuple ts)) ↔ Fits w v (.tuple ts) := by
  by_cases h2 : ts.length = 2
  · match ts, h2, ih with
    | [a, b], _, ih =>
      show Fits w v (Ty.normalize (.prod a b)) ↔ Fits w v (.tuple [a, b])
      rw [fits_tuple_pair]
      exact fits_normalize_prod w a b v (ih a List.mem_cons_self)
        (ih b (List.mem_cons_of_mem _ List.mem_cons_self))
  · rw [Ty.normalize_tuple_of_ne ts h2, Ty.normalizeItems_eq_map]
    cases v
    case list xs =>
      rw [fits_tuple, fits_tuple, List.map_map]
      have hmap : ts.map ((fun t x => Fits w x t) ∘ Ty.normalize) = ts.map (fun t x => Fits w x t) := by
        apply List.map_congr_left
        intro t ht
        funext x
        exact propext (ih t ht x)
      rw [hmap]
    all_goals exact Iff.rfl

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
  | prod a b iha ihb => exact fun v => fits_normalize_prod w a b v iha ihb
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
      · exact and_congr_left' (causeFits_iff (fun x => ihe x) _)
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
  | null | undefined | number | bytes => intro v; exact Iff.rfl
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
  | tuple ts ih => exact fun v => fits_normalize_tuple w ts v (fun t ht v => ih t ht v)
  | app n ts _ =>
    intro v
    cases ts with
    | nil => exact Iff.rfl
    | cons t ts =>
      rw [Ty.normalize_app_of_ne n _ (List.cons_ne_nil _ _)]
      exact Iff.rfl

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
    exact ⟨causeFits_map (fun x hx => fits_sub w he x hx) h.1, h.2⟩

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
    exact ⟨causeFits_map (fun x hx => fits_subN w he x hx) h.1, h.2⟩

/-- Every fitting exit fits `Exit<unknown, unknown>`, the exit a scope closes with (`closeScope`'s
pre, finding F-CLOSE). -/
theorem fitsExit_unknown {w : World} {ty : EffTy} {ex : ExitV} (h : FitsExit w ty ex) :
    FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex := by
  refine fitsExit_subN ?_ ?_ h
  · exact Ty.sub_unknown _
  · exact Ty.sub_unknown _

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
    exact causeFits_admits (fun x hx => fits_hasTy w e x hx) c (fitsExit_failure_cause h)

/-! ## Term soundness (TY-07)

`evalTerm_hasTy` (`Laws/Program/Typed.lean`) is the coarse check's term law. This section is the
same law for membership: a term that types and evaluates over values fitting their types
evaluates to a value that fits the term's type (`evalTerm_fitsAll`; the `EnvTyped` form the
ledger names is `Typed/Admission.lean`'s `evalTerm_fits`). The atom table is discharged once per
scheme, as there (`atomFits`). Two things differ. The polymorphic schemes widen their bindings in
the order itself (`Ty.WidensSub`, `fits_instantiate_widens`), because membership reads
declarations at handles where the coarse check reads kinds. And `fst`/`snd` over a union of
products answer at `Ty.join`, which the checker's join closure covers (`projectProduct_fits`). -/

/-! ### Inversions at the scalar and value formers

`fits_unit_inv` and `fits_nat_inv` are also the store rows' value facts (seat B's
`Typed/Adequacy.lean` stated them as `fits_unit_val` and `fits_nat_val`; row 132 keeps person-written
`Ty` cases here, so they have one home). -/

theorem fits_unit_inv {w : World} {v : Val} (h : Fits w v .unit) : v = Val.unit := by
  simp only [Fits] at h
  split at h
  · rfl
  · exact h.elim

/-- A member of `refOf A` is a cell declared at a type equivalent to `A` in the checker's order
(`RefDeclared`: both `subN` directions, not syntactic equality). A step of `denote-typed`; its
consumers are `syncRow_typed`'s `Ref` arms and the identity atom's cases (`atomFits`,
`atom_progress`). Moved here from `Typed/Denotation.lean`, name and statement kept. -/
theorem fits_refOf_inv {w : World} {v : Val} {A : Ty} (h : Fits w v (.refOf A)) :
    ∃ k, v = Val.cell k ∧ RefDeclared w k A := by
  simp only [Fits] at h
  split at h
  · rename_i index
    exact ⟨⟨index⟩, rfl, h⟩
  · exact h.elim

/-- A member of `deferredOf A E` is a deferred declared at columns equivalent to `(A, E)` in the
checker's order. A step of `denote-typed`; its consumers are `syncRow_typed`'s `Deferred` arms,
`deferredAwait_arm`, `inlineYield_typed` and the identity atom's cases. Moved here from
`Typed/Denotation.lean`, name and statement kept. -/
theorem fits_deferredOf_inv {w : World} {v : Val} {A E : Ty} (h : Fits w v (.deferredOf A E)) :
    ∃ k, v = Val.promise k ∧ PromiseDeclared w k A E := by
  simp only [Fits] at h
  split at h
  · rename_i index
    exact ⟨⟨index⟩, rfl, h⟩
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

/-- A member of the context handle type is a context whose services fit: no handle kind takes
the context target (the context read's answer, `getContext_answers`, read back; decisions row 151
(a″): a foreign finalizer restores the context it read). -/
theorem fits_context_inv {w : World} {v : Val} (h : Fits w v (.handle Ty.contextTarget)) :
    ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w ctx.services := by
  simp only [Fits] at h
  split at h
  · simp only [HandleFits] at h
    split at h
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)
    · exact absurd h.1 (by decide)
    · exact h.elim
  · obtain ⟨_, ctx, hctx, services, _⟩ := h
    exact ⟨ctx, hctx, services⟩

/-- Membership of a number does not read the number: the `nat` arm is the only one a number
reaches, a union passes it to a branch, and `unknown` reads no keys (one induction over the
judgment; the store rows that overwrite a `nat` cell read it). -/
theorem fits_nat_irrel (w : World) (n m : Nat) : ∀ t, Fits w (Val.nat n) t → Fits w (Val.nat m) t := by
  intro t
  induction t with
  | nat => intro _; trivial
  | union l r ihl ihr =>
    intro h
    rcases h with h | h
    · exact Or.inl (ihl h)
    · exact Or.inr (ihr h)
  | unknown => intro _; exact live_of_handles_nil rfl
  | handle target =>
    intro h
    obtain ⟨_, ctx, hctx, _⟩ := h
    exact (nomatch hctx)
  | int | number => intro _; rfl
  | app target _ _ =>
    intro h
    obtain ⟨_, ctx, hctx, _⟩ := h
    exact (nomatch hctx)
  | never | unit | string | bool | option | list | prod | except | exitOf | causeOf
  | fiberOf | lit | refOf | deferredOf | var | record | map | tuple | null | undefined
  | bytes => intro h; exact h.elim

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

/-- Appending the two binders of a list fold keeps the fit: the accumulator at the fold's level
and the element one above it (decisions row 228). Step of `fold-typed-atomic-update` (R4); its
consumers are the fold cases of `evalTerm_fitsAll` and `evalTerm_progress`. -/
theorem append_pair {vs : List Val} {tys : List Ty} (h : FitsAll w vs tys) {v x : Val}
    {t u : Ty} (hv : Fits w v t) (hx : Fits w x u) :
    FitsAll w (vs ++ [v, x]) (tys ++ [t, u]) := by
  induction h with
  | nil => exact .cons hv (.cons hx .nil)
  | cons hy _ ih => exact .cons hy ih

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

/-- **The list fold's semantic typing rule** (decisions row 228), in a fixed world. The list
evaluates to a member of `list A` and the initial value to a member of `B`. The body maps a
member of `B` and a member of `A`, at the environment extended by both, to a member of `B`.
Then the fold answers a member of `B`. The list is read through its decoded element view
(`fits_list_iff`), so an admitted snapshot of handles is a list here too. The empty list answers
the initial value, and no step runs.

It assumes no rule of the checker: `evalTerm_progress` (`Typed/Denotation.lean`) discharges its
premises from the term typer's rule. A step of `fold-typed-atomic-update` (R4). It says nothing
of a body that refuses on a member, and nothing of a target. -/
theorem fold_fits {w : World} {vals : List Val} {accTy : Option Ty} {list init body : Term}
    {A B : Ty} {value start : Val}
    (hlist : evalTerm vals list = some value) (hvalue : Fits w value (.list A))
    (hinit : evalTerm vals init = some start) (hstart : Fits w start B)
    (hbody : ∀ acc x, Fits w acc B → Fits w x A →
      ∃ next, evalTerm (vals ++ [acc, x]) body = some next ∧ Fits w next B) :
    ∃ v, evalTerm vals (.fold accTy list init body) = some v ∧ Fits w v B := by
  obtain ⟨items, hitems, hall⟩ := (fits_list_iff w value A).mp hvalue
  obtain ⟨v, hv, hfitv⟩ := foldlM_answers (P := fun acc => Fits w acc B)
    (Q := fun x => Fits w x A) hbody items start hall hstart
  refine ⟨v, ?_, hfitv⟩
  rw [evalTerm_fold, hlist, Option.bind_some, hitems, Option.bind_some, hinit, Option.bind_some]
  exact hv

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

/-- `Ty.valueVarsAlg` at a record: each half reads every field's. -/
theorem valueVarsAlg_record (fs : List (String × Bool × Ty)) :
    cata_ty Ty.valueVarsAlg (.record fs) =
      (fs.all fun p => (cata_ty Ty.valueVarsAlg p.2.2).1,
        fs.all fun p => (cata_ty Ty.valueVarsAlg p.2.2).2) := by
  rw [cata_ty_record]
  exact Prod.ext List.all_map List.all_map

/-- `Ty.valueVarsAlg` at a tuple. -/
theorem valueVarsAlg_tuple (ts : List Ty) :
    cata_ty Ty.valueVarsAlg (.tuple ts) =
      (ts.all fun t => (cata_ty Ty.valueVarsAlg t).1, ts.all fun t => (cata_ty Ty.valueVarsAlg t).2) := by
  rw [cata_ty_tuple]
  exact Prod.ext List.all_map List.all_map

/-- `Ty.valueVarsAlg` at a reference: its arguments are unread by membership. -/
theorem valueVarsAlg_app (n : String) (ts : List Ty) :
    cata_ty Ty.valueVarsAlg (.app n ts) = (ts.all fun t => (cata_ty Ty.valueVarsAlg t).1, true) := by
  rw [cata_ty_app]
  exact Prod.ext List.all_map rfl

/-- `Ty.valueVars` at a record reads every field. -/
theorem valueVars_record_fields {fs : List (String × Bool × Ty)} (h : Ty.valueVars (.record fs) = true) :
    ∀ p ∈ fs, Ty.valueVars p.2.2 = true := by
  unfold Ty.valueVars at h
  rw [valueVarsAlg_record] at h
  exact fun p hp => List.all_eq_true.mp h p hp

/-- `Ty.valueVars` at a tuple reads every item. -/
theorem valueVars_tuple_items {ts : List Ty} (h : Ty.valueVars (.tuple ts) = true) :
    ∀ t ∈ ts, Ty.valueVars t = true := by
  unfold Ty.valueVars at h
  rw [valueVarsAlg_tuple] at h
  exact fun t ht => List.all_eq_true.mp h t ht

/-- Canonical order sees names only, so it commutes with instantiation. -/
theorem canon_instantiate (σ : Ty.Subst) (fs : List (String × Bool × Ty)) :
    Ty.canon (fs.map fun q => (q.1, q.2.1, Ty.instantiate σ q.2.2)) =
      (Ty.canon fs).map fun q => (q.1, q.2.1, Ty.instantiate σ q.2.2) :=
  Field.canonBy_map (fun c : Bool × Ty => (c.1, Ty.instantiate σ c.2)) fs

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
        exact ⟨causeFits_map (fun x hx => ihe he x hx) h.1, h.2⟩
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
  | null => intro _ v h; exact h
  | undefined => intro _ v h; exact h
  | number => intro _ v h; exact h
  | bytes => intro _ v h; exact h
  | app _ _ _ => intro _ v h; exact h
  | map a b iha ihb =>
    intro hv v h
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hv
    change Fits w v (.map (Ty.instantiate σ a) (Ty.instantiate σ b)) at h
    show Fits w v (.map (Ty.instantiate σ' a) (Ty.instantiate σ' b))
    simp only [Fits] at h ⊢
    split at h
    · refine ⟨h.1, fun e he => ?_⟩
      have hx := h.2 e he
      cases e
      case pair x y => exact ⟨iha ha x hx.1, ihb hb y hx.2⟩
      all_goals exact hx.elim
    · exact h.elim
  | record fs ih =>
    intro hv v h
    have hvs := valueVars_record_fields hv
    change Fits w v (.record (Ty.instantiateFields σ fs)) at h
    show Fits w v (.record (Ty.instantiateFields σ' fs))
    rw [Ty.instantiateFields_eq_map] at h ⊢
    obtain ⟨ns, xs, hp, hfit⟩ := fits_record_inv w v _ h
    rw [fits_record w hp, canon_instantiate, List.map_map]
    rw [canon_instantiate, List.map_map] at hfit
    exact namedFit_map (fun t x => Fits w x (Ty.instantiate σ t)) (fun t x => Fits w x (Ty.instantiate σ' t))
      (Ty.canon fs) ns xs (fun q hq x hx => ih q (Ty.mem_canon hq) (hvs q (Ty.mem_canon hq)) x hx) hfit
  | tuple ts ih =>
    intro hv v h
    have hvs := valueVars_tuple_items hv
    change Fits w v (.tuple (Ty.instantiateItems σ ts)) at h
    show Fits w v (.tuple (Ty.instantiateItems σ' ts))
    rw [Ty.instantiateItems_eq_map] at h ⊢
    cases v
    case list xs =>
      rw [fits_tuple, List.map_map] at h
      rw [fits_tuple, List.map_map]
      exact itemsFit_map (fun t x => Fits w x (Ty.instantiate σ t)) (fun t x => Fits w x (Ty.instantiate σ' t))
        ts xs (fun t ht x hx => ih t ht (hvs t ht) x hx) h
    all_goals exact h.elim

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
        (hps p List.mem_cons_self) _
        ((fits_normalize w _ _).mp (fits_sub w (Ty.matchTemplate_sound σ₀ p r σ₁ h₁) _
          ((fits_normalize w r _).mpr hv))))
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

/-- Fitted arguments form an exact tuple; consumed by the tuple atom membership law. -/
theorem FitsAll.tuple {w : World} {values : List Val} {types : List Ty}
    (h : FitsAll w values types) : Fits w (.list values) (.tuple types) := by
  rw [fits_tuple]
  induction h with
  | nil => trivial
  | cons hx _ ih => exact ⟨hx, ih⟩

/-- An admitted position in `ItemsFit` supplies its exact member.
This helper feeds tuple projection and world-indexed term progress. -/
theorem tupleItem_fits (w : World) :
    ∀ (types : List Ty) (values : List Val) (index : Nat) (answer : Ty),
      types[index]? = some answer →
      ItemsFit (types.map (fun t x => Fits w x t)) values →
      ∃ value, values[index]? = some value ∧ Fits w value answer
  | [], _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, _, h => h.elim
  | t :: ts, value :: values, 0, answer, h, hv => by
    cases h
    exact ⟨value, rfl, hv.1⟩
  | t :: ts, value :: values, index + 1, answer, h, hv =>
    tupleItem_fits w ts values index answer h hv.2

/-- Plain tuple projection supplies a member in the same world. -/
theorem tupleAt_fits {w : World} {types : List Ty} {value : Val}
    {index : Nat} {answer : Ty} (hi : types[index]? = some answer)
    (hv : Fits w value (.tuple types)) :
    ∃ out, Val.tupleAt? value index = some out ∧ Fits w out answer := by
  simp only [Fits] at hv
  split at hv
  · next values =>
    rw [itemFitters_eq_map] at hv
    exact tupleItem_fits w types values index answer hi hv
  · exact hv.elim

/-- Every admitted tuple alternative supplies the selected member.
This serves `denote-typed` through `evalTerm_progress`; no host or scheduler premise changes. -/
theorem tuple_project_fits (w : World) (index : Nat) (input output : Ty) (value : Val)
    (hp : Tuple.project index input = some output) (hv : Fits w value input) :
    ∃ out, Val.tupleAt? value index = some out ∧ Fits w out output := by
  induction input generalizing output with
  | never => exact hv.elim
  | tuple items _ => exact tupleAt_fits hp hv
  | prod a b _ _ =>
    apply tupleAt_fits hp
    exact (fits_tuple_pair w value a b).mpr hv
  | union a b iha ihb =>
    obtain ⟨left, hl, rest⟩ := Option.bind_eq_some_iff.mp hp
    obtain ⟨right, hr, heq⟩ := Option.bind_eq_some_iff.mp rest
    cases heq
    rcases hv with ha | hb
    · obtain ⟨out, he, hm⟩ := iha left hl ha
      exact ⟨out, he, fits_join_left w left right out hm⟩
    · obtain ⟨out, he, hm⟩ := ihb right hr hb
      exact ⟨out, he, fits_join_right w left right out hm⟩
  | _ => simp only [Tuple.project, reduceCtorEq] at hp

/-- Normalization retains the world-indexed tuple projection premise. -/
theorem tuple_typeAt_fits {w : World} {index : Nat} {input output : Ty} {value : Val}
    (hp : Tuple.typeAt input index = some output) (hv : Fits w value input) :
    ∃ out, Val.tupleAt? value index = some out ∧ Fits w out output :=
  tuple_project_fits w index input.normalize output value hp
    ((fits_normalize w input value).mpr hv)

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
        refine ⟨cause.reasons, ?_, hfit.1⟩
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

/-! String-map operations at world-indexed membership.
These `denote-typed` helpers supply both membership and existence to the native atom consumers. -/
namespace MapFits
open MapValues

/-- A fitting string map exposes its exact carrier and each payload's world membership. -/
theorem map_inv {w : World} {value : Val} {t : Ty} (h : Fits w value (.map .string t)) :
    ∃ entries, value = Machine.Map.write entries ∧ ∀ e ∈ entries, Fits w e.2 t := by
  simp only [Fits] at h
  split at h
  · next values =>
    have hw : ∀ value ∈ values, ∃ e : String × Val,
        value = .pair (.str e.1) e.2 ∧ Fits w e.2 t := by
      intro v hv
      have hp := h.2 v hv
      cases v with
      | pair key payload =>
        obtain ⟨name, rfl⟩ := fits_string_inv (w := w) hp.1
        exact ⟨(name, payload), rfl, hp.2⟩
      | _ => exact hp.elim
    obtain ⟨entries, rfl, hentries⟩ := encoded_of_all _ _ values hw
    exact ⟨entries, rfl, hentries⟩
  · exact h.elim

/-- Canonical map construction retains every payload's world membership. -/
theorem write_canon {w : World} {entries : List (String × Val)} {t : Ty}
    (h : ∀ e ∈ entries, Fits w e.2 t) :
    Fits w (Machine.Map.write (Field.canonBy Field.bytesKey entries)) (.map .string t) := by
  refine ⟨sorted_pairs (Field.canonBy_ascending entries), ?_⟩
  intro value hv
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
  exact ⟨True.intro, canon_all (P := fun value => Fits w value t) h e he⟩

/-- Lookup returns an option whose present payload fits in the same world. -/
theorem get {w : World} {value : Val} {t : Ty} (h : Fits w value (.map .string t)) (key : String) :
    ∃ out, Machine.Map.get value key = some out ∧ Fits w out (.option t) := by
  obtain ⟨entries, rfl, hall⟩ := map_inv h
  cases hf : Field.firstOf key entries with
  | none => exact ⟨.none, by simp only [Machine.Map.get, Machine.Map.read_write, hf, Option.map_some, Option.elim_none], True.intro⟩
  | some found =>
    exact ⟨.some found, by simp only [Machine.Map.get, Machine.Map.read_write, hf, Option.map_some, Option.elim_some],
      hall (key, found) (Field.firstOf_mem hf)⟩

/-- Update keeps the old and replacement memberships as separate union alternatives. -/
theorem set {w : World} {value replacement : Val} {a b : Ty}
    (h : Fits w value (.map .string a)) (key : String) (hr : Fits w replacement b) :
    ∃ out, Machine.Map.set value key replacement = some out ∧
      Fits w out (.map .string (.union a b)) := by
  obtain ⟨entries, rfl, hall⟩ := map_inv h
  refine ⟨Machine.Map.write (Field.canonBy Field.bytesKey ((key, replacement) :: entries)),
    by simp only [Machine.Map.set, Machine.Map.read_write, Option.map_some], write_canon ?_⟩
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact Or.inr hr
  · exact Or.inl (hall e he)

/-- Extracted keys fit the string list type at every world. -/
theorem keys {w : World} {value : Val} {t : Ty} (h : Fits w value (.map .string t)) :
    ∃ out, Machine.Map.keys value = some out ∧ Fits w out (.list .string) := by
  obtain ⟨entries, rfl, _⟩ := map_inv h
  refine ⟨.list ((Field.canonBy Field.bytesKey entries).map fun e => .str e.1),
    by simp only [Machine.Map.keys, Machine.Map.read_write, Option.map_some], ?_⟩
  intro v hv
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hv
  trivial

/-- Extracted ordinary pairs retain every payload's membership in the supplied world. -/
theorem entries {w : World} {value : Val} {t : Ty} (h : Fits w value (.map .string t)) :
    ∃ out, Machine.Map.entries value = some out ∧ Fits w out (.list (.prod .string t)) := by
  obtain ⟨entries, rfl, hall⟩ := map_inv h
  refine ⟨.list ((Field.canonBy Field.bytesKey entries).map fun e => .list [.str e.1, e.2]),
    by simp only [Machine.Map.entries, Machine.Map.read_write, Option.map_some], ?_⟩
  intro v hv
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
  exact ⟨True.intro, canon_all (P := fun value => Fits w value t) hall e he⟩

/-- Every fitting entry-list view constructs a fitting map, without a new shape premise. -/
theorem fromEntries {w : World} {value : Val} {t : Ty}
    (h : Fits w value (.list (.prod .string t))) :
    ∃ out, Machine.Map.fromEntries value = some out ∧ Fits w out (.map .string t) := by
  obtain ⟨values, hv, hall⟩ := (fits_list_iff w value _).mp h
  have hw : ∀ value ∈ values, ∃ e : String × Val,
      value = .list [.str e.1, e.2] ∧ Fits w e.2 t := by
    intro value hvalue
    obtain ⟨key, payload, rfl, hk, hp⟩ := (fits_prod_iff w value _ _).mp (hall value hvalue)
    obtain ⟨name, rfl⟩ := fits_string_inv hk
    exact ⟨(name, payload), rfl, hp⟩
  obtain ⟨entries, rfl, hentries⟩ := encoded_of_all _ _ values hw
  refine ⟨Machine.Map.write (Field.canonBy Field.bytesKey entries.reverse),
    by simp only [Machine.Map.fromEntries, hv, Option.bind_eq_bind, Option.bind_some,
      Machine.Map.readTuples_map, Option.pure_def], write_canon ?_⟩
  exact fun e he => hentries e (List.mem_reverse.mp he)

end MapFits

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

  | mapEmpty =>
    refine atomFits_of_mono rfl fun w vs v hfit hv => ?_
    cases hfit.nil_inv
    cases hv
    exact ⟨rfl, fun _ hmem => nomatch hmem⟩
  | mapGet =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨value, key, rfl, hf, hk⟩ := hfit.pair_inv
    obtain ⟨name, rfl⟩ := fits_string_inv hk
    obtain ⟨out, he, ho⟩ := MapFits.get hf name
    change Machine.Map.get value name = some v at hv
    rw [he] at hv
    cases hv
    exact ho
  | mapSet =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨value, key, replacement, rfl, hf, hk, hr⟩ := hfit.triple_inv
    obtain ⟨name, rfl⟩ := fits_string_inv hk
    obtain ⟨out, he, ho⟩ := MapFits.set hf name hr
    change Machine.Map.set value name replacement = some v at hv
    rw [he] at hv
    cases hv
    exact ho
  | mapKeys =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨value, rfl, hf⟩ := hfit.singleton_inv
    obtain ⟨out, he, ho⟩ := MapFits.keys hf
    change Machine.Map.keys value = some v at hv
    rw [he] at hv
    cases hv
    exact ho
  | mapEntries =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨value, rfl, hf⟩ := hfit.singleton_inv
    obtain ⟨out, he, ho⟩ := MapFits.entries hf
    change Machine.Map.entries value = some v at hv
    rw [he] at hv
    cases hv
    exact ho
  | mapFromEntries =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨value, rfl, hf⟩ := hfit.singleton_inv
    obtain ⟨out, he, ho⟩ := MapFits.fromEntries hf
    change Machine.Map.fromEntries value = some v at hv
    rw [he] at hv
    cases hv
    exact ho
  | tuple =>
    refine atomFits_of_custom rfl fun w types answer values out ht hv he => ?_
    cases ht
    cases he
    exact (fits_normalize w (.tuple types) (.list values)).mpr hv.tuple
  -- a prefix and its rest hold members of the list (decisions row 228)
  | listTake =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨xs, i, rfl, hxs, hi⟩ := hfit.pair_inv
    obtain ⟨n, rfl⟩ := fits_nat_inv hi
    obtain ⟨elems, hl, helems⟩ := (fits_list_iff w xs _).mp hxs
    simp only [NativeAtom.eval, hl, Option.map_some, Option.some.injEq] at hv
    subst hv
    exact (fits_list_iff w _ _).mpr ⟨elems.take n, rfl,
      fun y hy => helems y (List.mem_of_mem_take hy)⟩
  | listDrop =>
    refine atomFits_of_poly rfl (by decide) fun w σ vs v hfit hv => ?_
    obtain ⟨xs, i, rfl, hxs, hi⟩ := hfit.pair_inv
    obtain ⟨n, rfl⟩ := fits_nat_inv hi
    obtain ⟨elems, hl, helems⟩ := (fits_list_iff w xs _).mp hxs
    simp only [NativeAtom.eval, hl, Option.map_some, Option.some.injEq] at hv
    subst hv
    exact (fits_list_iff w _ _).mpr ⟨elems.drop n, rfl,
      fun y hy => helems y (List.mem_of_mem_drop hy)⟩
  -- the identity test answers a Boolean at both admitted kinds (decisions row 229)
  | sameHandle =>
    refine atomFits_of_custom rfl ?_
    intro w tys ty vs v hty hfit hv
    simp only [NativeAtom.CustomScheme.apply, NativeAtom.sameHandleRule] at hty
    split at hty
    · cases hty
      obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
      obtain ⟨k, rfl, _⟩ := fits_refOf_inv hx
      obtain ⟨k', rfl, _⟩ := fits_refOf_inv hy
      have hv' : (if (2 : UInt8) = 2 then some (Val.bool (decide (k.index = k'.index)))
          else none) = some v := hv
      rw [if_pos rfl] at hv'
      cases hv'
      trivial
    · cases hty
      obtain ⟨x, y, rfl, hx, hy⟩ := hfit.pair_inv
      obtain ⟨k, rfl, _⟩ := fits_deferredOf_inv hx
      obtain ⟨k', rfl, _⟩ := fits_deferredOf_inv hy
      have hv' : (if (3 : UInt8) = 3 then some (Val.bool (decide (k.index = k'.index)))
          else none) = some v := hv
      rw [if_pos rfl] at hv'
      cases hv'
      trivial
    · exact nomatch hty


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


/-! ## Inhabitance agrees with membership (decisions row 127; DI-67)

`inhabited` (`Program/Columns.lean`) is a `TyAlgebra` fold; the column check `admitColumn`
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

/-- An all-heads classifier at a record whose row answers `true`: every field's answer. -/
theorem allHeads_record (col : ClassRow → Bool) (hrow : col (tyClasses.get .record) = true)
    (fs : List (String × Bool × Ty)) :
    cata_ty (TyTable.allHeads tyClasses col) (.record fs) =
      fs.all fun p => cata_ty (TyTable.allHeads tyClasses col) p.2.2 := by
  unfold TyTable.allHeads TyAlgebra.headAlg
  rw [cata_ofLayer_view]
  show (col (tyClasses.get .record) && comb_pos_list_prod_string_prod_bool_ty true (· && ·)
    (fs.map (prodMapSnd (prodMapSnd (cata_ty (TyTable.allHeads tyClasses col)))))) =
      fs.all fun p => cata_ty (TyTable.allHeads tyClasses col) p.2.2
  rw [hrow, Bool.true_and]
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    rw [List.map_cons, comb_pos_list_prod_string_prod_bool_ty, ih, List.all_cons]
    rfl

/-- An all-heads classifier at a tuple whose row answers `true`: every item's answer. -/
theorem allHeads_tuple (col : ClassRow → Bool) (hrow : col (tyClasses.get .tuple) = true)
    (ts : List Ty) :
    cata_ty (TyTable.allHeads tyClasses col) (.tuple ts) =
      ts.all fun t => cata_ty (TyTable.allHeads tyClasses col) t := by
  unfold TyTable.allHeads TyAlgebra.headAlg
  rw [cata_ofLayer_view]
  show (col (tyClasses.get .tuple) && comb_pos_list_ty true (· && ·)
    (ts.map (cata_ty (TyTable.allHeads tyClasses col)))) =
      ts.all fun t => cata_ty (TyTable.allHeads tyClasses col) t
  rw [hrow, Bool.true_and]
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [List.map_cons, comb_pos_list_ty, ih, List.all_cons]

/-- The record arm of `inhabited`, read through the canonical fields. -/
theorem inhabited_record (fs : List (String × Bool × Ty)) :
    inhabited (.record fs) = (Ty.canon fs).all fun q => q.2.1 || inhabited q.2.2 := by
  unfold inhabited
  rw [cata_ty_record]
  have hpm : prodMapSnd (prodMapSnd (cata_ty inhabitedAlg)) =
      fun q : String × Bool × Ty => (q.1, prodMapSnd (cata_ty inhabitedAlg) q.2) := rfl
  rw [hpm]
  show (Ty.canon (fs.map fun q => (q.1, prodMapSnd (cata_ty inhabitedAlg) q.2))).all
    (fun p => p.2.1 || p.2.2) = _
  rw [Ty.canon, Ty.canon, Field.canonBy_map]
  exact List.all_map

/-- The tuple arm of `inhabited`. -/
theorem inhabited_tuple (ts : List Ty) : inhabited (.tuple ts) = ts.all inhabited := by
  unfold inhabited
  rw [cata_ty_tuple]
  exact List.all_map

/-- **Sound against the coarse judgment (proved)**, DI-67's frozen statement: a type with a
value under some allocation table is `inhabited`. -/
theorem inhabited_of_hasTy :
    ∀ (t : Ty) (v : Val) (alloc : List String), Val.hasTy v t alloc = true → inhabited t = true := by
  intro t
  induction t with
  | never => intro v alloc h; exact Bool.noConfusion h
  | var _ => intro v alloc h; exact Bool.noConfusion h
  | unit | nat | int | string | bool | option | list | exitOf | causeOf | fiberOf | lit
  | refOf | deferredOf | unknown | map | null | undefined | number | bytes => intro _ _ _; rfl
  | handle target =>
    intro v alloc h
    cases hr : retiredHandleTargets.contains target
    · show (!retiredHandleTargets.contains target) = true
      rw [hr]
      rfl
    · rw [Val.hasTy_handle_retired hr] at h
      exact Bool.noConfusion h
  | app name args _ =>
    intro v alloc h
    cases hr : retiredHandleTargets.contains name
    · show (!retiredHandleTargets.contains name) = true
      rw [hr]
      rfl
    · rw [hasTy_app_eq, Val.hasTy_handle_retired hr] at h
      exact Bool.noConfusion h
  | record fs ih =>
    intro v alloc h
    rw [inhabited_record, List.all_eq_true]
    intro q hq
    cases hp : recordParts? v with
    | none =>
      rw [Val.hasTy_record_none hp] at h
      exact Bool.noConfusion h
    | some parts =>
      obtain ⟨ns, xs⟩ := parts
      rw [Val.hasTy_record hp] at h
      have hfit := namedFit_of_namedHasTy (fun t x => Val.hasTy x t alloc = true)
        (fun t x => Val.hasTy x t alloc) (Ty.canon fs) ns xs (fun _ _ _ hx => hx) h
      rcases namedFit_witness _ ns xs hfit _ (List.mem_map_of_mem hq) with ho | ⟨x, hx⟩
      · exact Bool.or_eq_true_iff.mpr (Or.inl ho)
      · exact Bool.or_eq_true_iff.mpr (Or.inr (ih q (Ty.mem_canon hq) x alloc hx))
  | tuple ts ih =>
    intro v alloc h
    rw [inhabited_tuple, List.all_eq_true]
    intro t ht
    cases v
    case list xs =>
      rw [Val.hasTy_tuple] at h
      have hfit := itemsFit_of_itemsHasTy (fun t x => Val.hasTy x t alloc = true)
        (fun t x => Val.hasTy x t alloc) ts xs (fun _ _ _ hx => hx) h
      obtain ⟨x, hx⟩ := itemsFit_witness _ xs hfit _ (List.mem_map_of_mem ht)
      exact ih t ht x alloc hx
    all_goals exact Bool.noConfusion h
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

/-- **Sound against membership (proved).** A type with a member in some world is `inhabited`;
so refusing an `inhabited t = false` column never refuses a type with a member. -/
theorem inhabited_of_fits (w : World) (t : Ty) (v : Val) (h : Fits w v t) : inhabited t = true :=
  inhabited_of_hasTy t v _ (fits_hasTy w t v h)

/-! ### The data fragment: a witness that needs no world -/

/-- **The data fragment**: no handle, fiber, cell or deferred anywhere in the type, so its members
name no world entry. The classifier table's `handleFree` column read at every node
(`TyTable.allHeads`, `Program/TyClasses.lean`; decisions row 182 (a)): one answer per constructor,
the node's and all of its children's. -/
def handleFree (t : Ty) : Bool := cata_ty (TyTable.allHeads tyClasses ClassRow.handleFree) t

/-- **The shape-decided fragment**: at every node the shape check (`Val.hasTy`) decides membership
at every world. The classifier table's `shapeDecides` column read at every node (`TyTable.allHeads`,
`Program/TyClasses.lean`): no handle, fiber, cell, deferred or `unknown`, whose members read the
world, and no exit, whose membership also asks a shape-free cause (decisions row 152). -/
def shapeDecides (t : Ty) : Bool := cata_ty (TyTable.allHeads tyClasses ClassRow.shapeDecides) t

/-- **On the shape-decided fragment the shape check is membership**, at every world and every
allocation table: the converse of `fits_hasTy` there. The Schema decoder's filter is this check
(`Schema.decode`), so a decoded value at such a type fits it (`Typed/AnswerSchema.lean`). -/
theorem fits_of_hasTy_shapeDecides (w : World) :
    ∀ t : Ty, shapeDecides t = true → ∀ v allocated, Val.hasTy v t allocated = true → Fits w v t := by
  intro t
  induction t with
  | unit | nat | string | bool | null | undefined | bytes =>
    intro _ v allocated hv
    simp only [Val.hasTy] at hv
    split at hv
    · trivial
    · exact Bool.noConfusion hv
  | lit s =>
    intro _ v allocated hv
    simp only [Val.hasTy] at hv
    split at hv
    · exact beq_iff_eq.mp hv
    · exact Bool.noConfusion hv
  | option a iha =>
    intro hs v allocated hv
    have ha : shapeDecides a = true := hs
    simp only [Val.hasTy] at hv
    split at hv
    · trivial
    · exact iha ha _ _ hv
    · exact Bool.noConfusion hv
  | list a iha =>
    intro hs v allocated hv
    have ha : shapeDecides a = true := hs
    simp only [Val.hasTy] at hv
    split at hv
    · split at hv
      · rename_i ids hids
        simp only [Fits, hids]
        intro id hid
        exact iha ha _ _ (List.all_eq_true.mp hv id hid)
      · exact Bool.noConfusion hv
    · intro x hx
      exact iha ha _ _ (List.all_eq_true.mp hv x hx)
    · exact Bool.noConfusion hv
  | prod a b iha ihb =>
    intro hs v allocated hv
    have hs' : (shapeDecides a && shapeDecides b) = true := hs
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hs'
    simp only [Val.hasTy] at hv
    split at hv
    · obtain ⟨hx, hy⟩ := Bool.and_eq_true_iff.mp hv
      exact fits_pair (iha ha _ _ hx) (ihb hb _ _ hy)
    · exact Bool.noConfusion hv
  | except e a ihe iha =>
    intro hs v allocated hv
    have hs' : (shapeDecides e && shapeDecides a) = true := hs
    obtain ⟨he, ha⟩ := Bool.and_eq_true_iff.mp hs'
    simp only [Val.hasTy] at hv
    split at hv
    · exact ihe he _ _ hv
    · exact iha ha _ _ hv
    · exact Bool.noConfusion hv
  | union l r ihl ihr =>
    intro hs v allocated hv
    have hs' : (shapeDecides l && shapeDecides r) = true := hs
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hs'
    simp only [Val.hasTy] at hv
    rcases Bool.or_eq_true_iff.mp hv with h | h
    · exact Or.inl (ihl hl _ _ h)
    · exact Or.inr (ihr hr _ _ h)
  | causeOf e ihe =>
    intro hs v allocated hv
    have he : shapeDecides e = true := hs
    simp only [Val.hasTy] at hv
    split at hv
    · rename_i c hc
      simp only [Fits, hc]
      intro r hr
      have hr' := List.all_eq_true.mp hv r hr
      cases r with
      | fail err ann =>
        simp only [reasonAdmits] at hr'
        split at hr'
        · rename_i x hx
          exact ⟨x, hx, ihe he _ _ hr'⟩
        · exact Bool.noConfusion hr'
      | die _ _ => trivial
      | interrupt _ _ => trivial
    · exact Bool.noConfusion hv
  | never | var _ =>
    intro _ v allocated hv
    exact Bool.noConfusion hv
  | int | number => intro _ v allocated hv; exact hv
  | handle _ | fiberOf _ _ _ _ | refOf _ _ | deferredOf _ _ _ _ | exitOf _ _ _ _ | unknown
  | app _ _ _ =>
    intro hs
    exact Bool.noConfusion hs
  | map k t ihk iht =>
    intro hs v allocated hv
    have hs' : (shapeDecides k && shapeDecides t) = true := hs
    obtain ⟨hk, ht⟩ := Bool.and_eq_true_iff.mp hs'
    simp only [Val.hasTy] at hv
    split at hv
    · obtain ⟨hsort, hall⟩ := Bool.and_eq_true_iff.mp hv
      refine ⟨hsort, fun e he => ?_⟩
      have he' := List.all_eq_true.mp hall e he
      cases e
      case pair a x =>
        obtain ⟨ha, hx⟩ := Bool.and_eq_true_iff.mp he'
        exact ⟨ihk hk _ _ ha, iht ht _ _ hx⟩
      all_goals exact Bool.noConfusion he'
    · exact Bool.noConfusion hv
  | record fs ih =>
    intro hs v allocated hv
    have hs' : ∀ p ∈ fs, shapeDecides p.2.2 = true := by
      unfold shapeDecides at hs
      rw [allHeads_record ClassRow.shapeDecides rfl] at hs
      exact fun p hp => List.all_eq_true.mp hs p hp
    cases hp : recordParts? v with
    | none =>
      rw [Val.hasTy_record_none hp] at hv
      exact Bool.noConfusion hv
    | some parts =>
      obtain ⟨ns, xs⟩ := parts
      rw [Val.hasTy_record hp] at hv
      rw [fits_record w hp]
      exact namedFit_of_namedHasTy (fun t x => Fits w x t) (fun t x => Val.hasTy x t allocated)
        (Ty.canon fs) ns xs
        (fun q hq x hx => ih q (Ty.mem_canon hq) (hs' q (Ty.mem_canon hq)) x allocated hx) hv
  | tuple ts ih =>
    intro hs v allocated hv
    have hs' : ∀ t ∈ ts, shapeDecides t = true := by
      unfold shapeDecides at hs
      rw [allHeads_tuple ClassRow.shapeDecides rfl] at hs
      exact fun t ht => List.all_eq_true.mp hs t ht
    cases v
    case list xs =>
      rw [Val.hasTy_tuple] at hv
      rw [fits_tuple]
      exact itemsFit_of_itemsHasTy (fun t x => Fits w x t) (fun t x => Val.hasTy x t allocated) ts xs
        (fun t ht x hx => ih t ht (hs' t ht) x allocated hx) hv
    all_goals exact Bool.noConfusion hv

/-- The tuple case's witness on the data fragment: one value list for every world. -/
theorem itemsFit_world_free (ts : List Ty) :
    (∀ t ∈ ts, ∃ v : Val, ∀ w : World, Fits w v t) →
      ∃ xs : List Val, ∀ w : World, ItemsFit (ts.map (fun t x => Fits w x t)) xs := by
  induction ts with
  | nil => exact fun _ => ⟨[], fun _ => trivial⟩
  | cons t ts ih =>
    intro h
    obtain ⟨x, hx⟩ := h t List.mem_cons_self
    obtain ⟨xs, hxs⟩ := ih (fun u hu => h u (List.mem_cons_of_mem _ hu))
    exact ⟨x :: xs, fun w => ⟨hx w, hxs w⟩⟩

/-- The record case's witness on the data fragment: an optional field without a member is left
out of both lists, which the distinct names make a skip (`namedFit_skip`). -/
theorem namedFit_world_free :
    ∀ (l : List (String × Bool × Ty)), (l.map Prod.fst).Nodup →
      (∀ q ∈ l, q.2.1 = true ∨ ∃ v : Val, ∀ w : World, Fits w v q.2.2) →
      ∃ ns xs : List Val, (∀ k, Val.str k ∈ ns → k ∈ l.map Prod.fst) ∧
        ∀ w : World, NamedFit (l.map (fun q => (q.1, fitterOf w q.2))) ns xs
  | [], _, _ => ⟨[], [], fun _ h => absurd h List.not_mem_nil, fun _ => trivial⟩
  | (m, o, t) :: l, hnd, hall => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨ns, xs, hnames, hv⟩ :=
      namedFit_world_free l hnd.2 (fun q hq => hall q (List.mem_cons_of_mem _ hq))
    rcases hall (m, o, t) List.mem_cons_self with ho | ⟨x, hx⟩
    · refine ⟨ns, xs, fun k hk => List.mem_cons_of_mem _ (hnames k hk), fun w => ?_⟩
      refine namedFit_skip m o (fun x => Fits w x t) _ ns xs (hv w) ho ?_
      intro k hk hkm
      exact hnd.1 (hkm ▸ hnames k hk)
    · refine ⟨.str m :: ns, x :: xs, ?_,
        fun w => (namedFit_cons_eq m o (fun y => Fits w y t) _ ns xs x).mpr ⟨hx w, hv w⟩⟩
      intro k hk
      rcases List.mem_cons.mp hk with hk | hk
      · injection hk with hk
        rw [hk]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hnames k hk)

/-- **Complete on the data fragment (proved)**, with one witness for every world. -/
theorem fits_of_inhabited_handleFree :
    ∀ t : Ty, handleFree t = true → inhabited t = true → ∃ v : Val, ∀ w : World, Fits w v t := by
  intro t
  induction t with
  | never => intro _ hi; exact Bool.noConfusion hi
  | int => intro _ _; exact ⟨.nat 0, fun _ => rfl⟩
  | number => intro _ _; exact ⟨.nat 0, fun _ => rfl⟩
  | null => intro _ _; exact ⟨.none, fun _ => trivial⟩
  | undefined => intro _ _; exact ⟨.unit, fun _ => trivial⟩
  | bytes => intro _ _; exact ⟨.bytes [], fun _ => trivial⟩
  | app _ _ _ => intro hf _; exact Bool.noConfusion hf
  | map _ _ _ _ => intro _ _; exact ⟨.list [], fun _ => ⟨rfl, fun _ he => nomatch he⟩⟩
  | tuple ts ih =>
    intro hf hi
    have hf' : ∀ t ∈ ts, handleFree t = true := by
      unfold handleFree at hf
      rw [allHeads_tuple ClassRow.handleFree rfl] at hf
      exact fun t ht => List.all_eq_true.mp hf t ht
    rw [inhabited_tuple, List.all_eq_true] at hi
    obtain ⟨xs, hxs⟩ := itemsFit_world_free ts (fun t ht => ih t ht (hf' t ht) (hi t ht))
    exact ⟨.list xs, fun w => (fits_tuple w xs ts).mpr (hxs w)⟩
  | record fs ih =>
    intro hf hi
    have hf' : ∀ p ∈ fs, handleFree p.2.2 = true := by
      unfold handleFree at hf
      rw [allHeads_record ClassRow.handleFree rfl] at hf
      exact fun p hp => List.all_eq_true.mp hf p hp
    rw [inhabited_record, List.all_eq_true] at hi
    obtain ⟨ns, xs, _, hv⟩ := namedFit_world_free (Ty.canon fs) (Field.canonBy_names_nodup _)
      (fun q hq => (Bool.or_eq_true_iff.mp (hi q hq)).imp id
        (fun hq2 => ih q (Ty.mem_canon hq) (hf' q (Ty.mem_canon hq)) hq2))
    exact ⟨.ctor 0 [.list ns, .list xs], fun w => (fits_record w rfl fs).mpr (hv w)⟩
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
  | unknown => intro _ _; exact ⟨.unit, fun _ => live_of_handles_nil rfl⟩
  | list a _ =>
    intro _ _
    refine ⟨.list [], fun w => ?_⟩
    intro x hx
    nomatch hx
  | exitOf a e _ _ =>
    intro _ _
    exact ⟨Val.exitErr ⟨[]⟩, fun w =>
      (fitsExit_failure_iff w ⟨a, e, Env.Requirement.empty⟩ ⟨[]⟩).mpr
        ⟨(fun _ hr => nomatch hr), (fun _ hr => nomatch hr)⟩⟩
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
  store : w.state.le w'.state
  service : w'.serviceTy = w.serviceTy

theorem Grows.refl (w : World) : Grows w w :=
  ⟨table_refl _, table_refl _, table_refl _, fun _ _ h => h, Stores.le_refl _, rfl⟩

theorem Grows.trans {a b c : World} (hab : Grows a b) (hbc : Grows b c) : Grows a c :=
  ⟨table_trans _ _ _ hab.fiber hbc.fiber, table_trans _ _ _ hab.promise hbc.promise,
    table_trans _ _ _ hab.cell hbc.cell, fun i t h => hbc.alloc i t (hab.alloc i t h),
    Stores.le_trans hab.store hbc.store, hbc.service.trans hab.service⟩

theorem Grows.fits {w w' : World} (h : Grows w w') {t : Ty} {v : Val} (hv : Fits w v t) :
    Fits w' v t :=
  fits_map h.fiber h.promise h.cell h.alloc h.store
    (fun key sty hk => by rw [← h.service]; exact hk) t v hv

/-- Declaring fiber `n` keeps every earlier membership and frees the keys above it. -/
theorem FreshFrom.addFiber {w : World} {n : Nat} (h : FreshFrom w n) (ty : EffTy) :
    Grows w (w.addFiber ⟨n⟩ ty) ∧ FreshFrom (w.addFiber ⟨n⟩ ty) (n + 1) := by
  refine ⟨⟨insert_extends _ _ _ (h.fiber ⟨n⟩ (Nat.le_refl n)), table_refl _, table_refl _,
    fun _ _ hx => hx, Stores.le_refl _, rfl⟩, ⟨fun id hid => ?_, fun key hk => h.promise key (Nat.le_of_succ_le hk),
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
    fun _ _ hx => hx, Stores.le_refl _, rfl⟩, ⟨fun id hid => h.fiber id (Nat.le_of_succ_le hid),
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
    fun _ _ hx => hx, Stores.le_refl _, rfl⟩, ⟨fun id hid => h.fiber id (Nat.le_of_succ_le hid),
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
  ⟨⟨table_refl _, table_refl _, table_refl _, extends_append _ _,
      ⟨Nat.le_refl _, Nat.le_refl _, fun _ hs => hs, Nat.le_refl _, fun _ hm => hm,
        by show _ ≤ (_ ++ [target]).length; rw [List.length_append]; exact Nat.le_add_right _ _⟩, rfl⟩,
    ⟨h.fiber, h.promise, h.cell⟩⟩

/-- A scope allocated at the store's next name, as `scopeMake` allocates it
(`Machine/Stores.lean`'s `syncOpStep`). -/
def World.allocScope (w : World) : World :=
  { w with state := { w.state with
      scopes := w.state.scopes.make w.state.nextName .sequential
      nextName := w.state.nextName + 1 } }

/-- Allocating a scope keeps every earlier membership and every fresh key, and the new scope is
present (row 156: a scope handle needs a present scope). -/
theorem FreshFrom.allocScope {w : World} {n : Nat} (h : FreshFrom w n) :
    Grows w w.allocScope ∧ FreshFrom w.allocScope n ∧ ScopeLive w.allocScope w.state.nextName :=
  ⟨⟨table_refl _, table_refl _, table_refl _, fun _ _ hx => hx,
      ⟨Nat.le_refl _, Nat.le_refl _, fun sc hs => ScopeStore.entryAt_make_isSome _ _ _ sc hs,
        Nat.le_succ _, fun _ hm => hm, Nat.le_refl _⟩, rfl⟩,
    ⟨h.fiber, h.promise, h.cell⟩, ScopeStore.entryAt_make_self _ _ _⟩

/-- A memo map allocated at the store's next name, as `memoFork none` allocates it
(`Machine/Stores.lean`'s `syncOpStep`, `StoresLaws.syncOpStep_memoFork`). -/
def World.allocMemo (w : World) : World :=
  { w with state := { w.state with
      memo := w.state.memo ++ [⟨⟨w.state.nextName⟩, none, []⟩]
      nextName := w.state.nextName + 1 } }

/-- Allocating a memo map keeps every earlier membership and every fresh key, and the new map is
present (row 187 amended by F-WF: a memo map handle needs a present map). -/
theorem FreshFrom.allocMemo {w : World} {n : Nat} (h : FreshFrom w n) :
    Grows w w.allocMemo ∧ FreshFrom w.allocMemo n ∧
      MemoLive w.allocMemo ⟨w.state.nextName⟩ :=
  ⟨⟨table_refl _, table_refl _, table_refl _, fun _ _ hx => hx,
      ⟨Nat.le_refl _, Nat.le_refl _, fun _ hs => hs, Nat.le_succ _,
        fun _ hm => MemoWorld.mapAt_append_isSome hm, Nat.le_refl _⟩, rfl⟩,
    ⟨h.fiber, h.promise, h.cell⟩, MemoWorld.mapAt_append_self _ ⟨⟨w.state.nextName⟩, none, []⟩⟩

/-- An inhabited handle names a spelling some kind owns. -/
theorem not_retired_of_inhabited {target : String}
    (h : (!retiredHandleTargets.contains target) = true) :
    retiredHandleTargets.contains target = false := by
  cases hc : retiredHandleTargets.contains target
  · rfl
  · rw [hc] at h
    cases h

/-- The `handle` former at every target a kind owns, in a world grown from any world with fresh
keys: an external allocation, or the scope, context or memo map at its own spelling. -/
theorem fits_handle_fresh (target : String) (hr : retiredHandleTargets.contains target = false)
    (w : World) (n : Nat) (hn : FreshFrom w n) :
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
    rcases hm with rfl | rfl | rfl | rfl | rfl
    -- the retired spellings: no kind owns them
    · exact absurd hr (by decide)
    · exact absurd hr (by decide)
    · obtain ⟨hg, hf, hlive⟩ := hn.allocScope
      exact ⟨_, n, Val.handle HandleKind.scope.byte w.state.nextName, hg, hf,
        (rfl : Ty.scopeTarget = Ty.scopeTarget), hlive⟩
    · have hhandles : Store.Val.handles (Val.context emptyCtx) = [] := by decide
      refine ⟨w, n, Val.context emptyCtx, Grows.refl w, hn, rfl, emptyCtx,
        ctxImage.ofVal_toVal emptyCtx, ?_, live_of_handles_nil hhandles⟩
      refine ⟨fun key sv sty hget _ => ?_, fun e he => by cases he⟩
      have hnone : emptyCtx.services.getV key = none := rfl
      rw [hnone] at hget
      cases hget
    -- a memo map handle names a present map (decisions row 187, amended by F-WF): allocate one
    · obtain ⟨hg, hf, hpresent⟩ := hn.allocMemo
      exact ⟨_, n, Val.handle HandleKind.memoMap.byte w.state.nextName, hg, hf, rfl, hpresent⟩

/-- The record case's induction: one world threaded through the canonical fields; an optional
field is left out of both lists, a required one gets a witness built in the grown world. -/
theorem namedFit_fresh (fs : List (String × Bool × Ty))
    (ih : ∀ p ∈ fs, inhabited p.2.2 = true → ∀ (w : World) (n : Nat), FreshFrom w n →
      ∃ (w' : World) (n' : Nat) (v : Val), Grows w w' ∧ FreshFrom w' n' ∧ Fits w' v p.2.2) :
    ∀ (l : List (String × Bool × Ty)), (∀ q ∈ l, q ∈ fs) → (l.map Prod.fst).Nodup →
      (∀ q ∈ l, (q.2.1 || inhabited q.2.2) = true) →
      ∀ (w : World) (n : Nat), FreshFrom w n →
      ∃ (w' : World) (n' : Nat) (ns xs : List Val), Grows w w' ∧ FreshFrom w' n' ∧
        (∀ k, Val.str k ∈ ns → k ∈ l.map Prod.fst) ∧
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
      have hi : inhabited t = true := hall (m, false, t) List.mem_cons_self
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
  | int => intro _ w n hn; exact ⟨w, n, .nat 0, Grows.refl w, hn, rfl⟩
  | number => intro _ w n hn; exact ⟨w, n, .nat 0, Grows.refl w, hn, rfl⟩
  | null => intro _ w n hn; exact ⟨w, n, .none, Grows.refl w, hn, trivial⟩
  | undefined => intro _ w n hn; exact ⟨w, n, .unit, Grows.refl w, hn, trivial⟩
  | bytes => intro _ w n hn; exact ⟨w, n, .bytes [], Grows.refl w, hn, trivial⟩
  | app name _ _ => intro hi w n hn; exact fits_handle_fresh name (not_retired_of_inhabited hi) w n hn
  | map _ _ _ _ =>
    intro _ w n hn
    exact ⟨w, n, .list [], Grows.refl w, hn, rfl, fun _ he => nomatch he⟩
  | tuple ts ih =>
    intro hi w n hn
    rw [inhabited_tuple, List.all_eq_true] at hi
    obtain ⟨w', n', xs, hg, hf, hv⟩ := itemsFit_fresh ts (fun t ht => ih t ht) ts (fun _ h => h) hi w n hn
    exact ⟨w', n', .list xs, hg, hf, (fits_tuple w' xs ts).mpr hv⟩
  | record fs ih =>
    intro hi w n hn
    rw [inhabited_record, List.all_eq_true] at hi
    obtain ⟨w', n', ns, xs, hg, hf, _, hv⟩ := namedFit_fresh fs (fun p hp => ih p hp) (Ty.canon fs)
      (fun q hq => Ty.mem_canon hq) (Field.canonBy_names_nodup _) hi w n hn
    exact ⟨w', n', .ctor 0 [.list ns, .list xs], hg, hf, (fits_record w' rfl fs).mpr hv⟩
  | var _ => intro hi; exact Bool.noConfusion hi
  | unit => intro _ w n hn; exact ⟨w, n, .unit, Grows.refl w, hn, trivial⟩
  | nat => intro _ w n hn; exact ⟨w, n, .nat 0, Grows.refl w, hn, trivial⟩
  | string => intro _ w n hn; exact ⟨w, n, .str "", Grows.refl w, hn, trivial⟩
  | bool => intro _ w n hn; exact ⟨w, n, .bool true, Grows.refl w, hn, trivial⟩
  | lit s => intro _ w n hn; exact ⟨w, n, .str s, Grows.refl w, hn, rfl⟩
  | option _ _ => intro _ w n hn; exact ⟨w, n, .none, Grows.refl w, hn, trivial⟩
  | unknown => intro _ w n hn; exact ⟨w, n, .unit, Grows.refl w, hn, live_of_handles_nil rfl⟩
  | list _ _ =>
    intro _ w n hn
    exact ⟨w, n, .list [], Grows.refl w, hn, fun x hx => nomatch hx⟩
  | exitOf a e _ _ =>
    intro _ w n hn
    exact ⟨w, n, Val.exitErr ⟨[]⟩, Grows.refl w, hn,
      (fitsExit_failure_iff w ⟨a, e, Env.Requirement.empty⟩ ⟨[]⟩).mpr
        ⟨(fun _ hr => nomatch hr), (fun _ hr => nomatch hr)⟩⟩
  | causeOf e _ =>
    intro _ w n hn
    refine ⟨w, n, Val.exitErr ⟨[]⟩, Grows.refl w, hn, ?_⟩
    have hc : Val.cause? (Val.exitErr ⟨[]⟩) = some ⟨[]⟩ := causeImage.ofVal_toVal ⟨[]⟩
    simp only [Fits, hc]
    intro _ hr
    nomatch hr
  | handle target =>
    intro hi w n hn
    exact fits_handle_fresh target (not_retired_of_inhabited hi) w n hn
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

/-- Every `handle` target a kind owns has a member in some world: the three internal spellings
and an external allocation (the types verifier's `handle_inhabited`). The two retired spellings
have none (`Val.hasTy_handle_retired`, the state plan's T3a). -/
theorem handle_inhabited (target : String) (hr : retiredHandleTargets.contains target = false) :
    ∃ (w : World) (v : Val), Fits w v (.handle target) := by
  refine (inhabited_iff_fits (.handle target)).mp ?_
  show (!retiredHandleTargets.contains target) = true
  rw [hr]
  rfl

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

/-! ## Flat carriers, tag payloads, fiber handles (granted 2026-10-01, seat D2)

The case analyses on `Ty` that M5's denotation lemma (`Laws/Program/Typed/Denotation.lean`)
reads and that row 132 keeps in this module. -/

/-- **Membership at a flat carrier is `FlatFits`** (proved): the converse of `flatFits_fits` on
the carriers `flatCarrier` admits (`Program/SigApp.lean`: the scalars, every handle but the
context, and a cell at any type). `provideService`'s denotation sets a context binding the provided value under
its key, and the `setContext` row demands `ServicesFit` (`Typed/Residual.lean`'s `fiberPre`),
which reads the key's carrier through `FlatFits`; the checker gives the value's membership at
that carrier, and a lawful signature's carriers are flat (`LawfulSig.services`). -/
theorem fits_flatFits {w : World} {v : Val} {t : Ty} (hflat : flatCarrier t = true)
    (h : Fits w v t) : FlatFits w v t := by
  cases t with
  | unit => exact h
  | nat => exact h
  | string => exact h
  | bool => exact h
  | handle target =>
    have hne : target ≠ Ty.contextTarget := bne_iff_ne.mp hflat
    cases v with
    | handle kind index => exact h
    | _ => exact absurd h.1 hne
  | refOf t =>
    simp only [Fits] at h
    simp only [FlatFits]
    split at h
    · exact h
    · exact h.elim
  | _ => exact Bool.noConfusion hflat

/-- **A tag hit's payload fits the payload type** (proved): the membership form of
`Ty.payload_hasTy` (`Laws/Program/Decision.lean`). A `select` on a tag decision binds the hit's
payload at `payloadTy` (`Decision.arms`), so the chosen arm's point is typed only if the payload
fits there: the two-cell list fits only a member tagged with the hit's tag, whose payload type is
one of the payloads `payloadTy` joins. -/
theorem fits_tagPayload {w : World} {c : Ty} {v p : Val} {tag : String} {P : Ty}
    (hc : Ty.taggedColumn c = true) (hv : Fits w v c)
    (hp : Val.tagPayload? tag v = some p) (hP : Ty.payloadTy tag c = some P) : Fits w p P := by
  obtain rfl : v = Val.list [Val.str tag, p] := by
    unfold Val.tagPayload? at hp
    split at hp
    · rename_i t x
      split at hp
      · rename_i h
        simp only [Option.some.injEq] at hp
        subst hp
        simp only [beq_iff_eq] at h
        subst h
        rfl
      · exact nomatch hp
    · exact nomatch hp
  obtain ⟨m, hm, hvm⟩ := (fits_members w _ c).mpr hv
  have hcm := List.all_eq_true.mp hc m hm
  obtain ⟨q, hmq, hq⟩ : ∃ q, Ty.payloadOf tag m = some q ∧ Fits w p q := by
    cases m with
    | prod a b =>
      cases a with
      | lit t =>
        obtain ⟨x, y, hxy, hx, hy⟩ := (fits_prod_iff w _ _ b).mp hvm
        simp only [Store.Val.list.injEq, List.cons.injEq, and_true] at hxy
        obtain ⟨rfl, rfl⟩ := hxy
        have ht : tag = t := hx
        subst ht
        exact ⟨b, if_pos rfl, hy⟩
      | _ => exact Bool.noConfusion hcm
    | unit | nat | string | bool | lit _ => exact hvm.elim
    | int => exact Bool.noConfusion hvm
    | _ => exact Bool.noConfusion hcm
  have hmem : q ∈ c.members.filterMap (Ty.payloadOf tag) := List.mem_filterMap.mpr ⟨m, hm, hmq⟩
  unfold Ty.payloadTy at hP
  split at hP
  · rename_i hnil
    rw [hnil] at hmem
    exact absurd hmem List.not_mem_nil
  · simp only [Option.some.injEq] at hP
    subst hP
    rw [fits_normalize, fits_ofMembers]
    exact ⟨q, hmem, hq⟩

/-- The checker's fiber-handle reading (`fiberTy`, `Typing/Rules.lean:184`) answers only at a
fiber handle type: the one case analysis on `Ty` the fiber rows of M5's denotation lemma need
(awaitFiber, runIn, the interrupts, awaitAll, awaitAllFailFast; `Typed/Denotation.lean`).
`Typing/CheckInversion.lean:32-38` holds the same shape lemma for `listOf?` and `exitOf?`; a
later cleanup moves the three beside each other. -/
theorem fiberTy_eq_some {t : Ty} {pair : Ty × Ty} (h : fiberTy t = some pair) :
    t = .fiberOf pair.1 pair.2 := by
  cases t with
  | fiberOf a e =>
    cases h
    rfl
  | _ => nomatch h

end Effect4.Program.Typed
