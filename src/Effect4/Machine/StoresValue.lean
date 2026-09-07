import Effect4.Machine.Value
import Effect4.Machine.Handles

/-!
# Machine.StoresValue — the frame machine's value alphabet as a view of the shared carrier

Owner: the exact images, in `Effect4.Store.Val`, of the alphabets `Machine/Stores.lean`
instantiates the frame machine at — `Err`, `Defect`, `Ctx`, the handles, `CauseV`, `ExitV` and
`Machine.Val` itself — and the one theorem that joins the old key discipline to the new
carrier: the handles `Val.keys` counts are exactly the `handle` frames the image carries.

Nothing here changes the runtime. `Machine.Val` keeps its inductive; the images below are the
migration contract U1 performs (`docs/research/2026-09-07-u0-value-foundation.md`): after the
cutover `toStore` is the identity and every spelling of `Value` is a constructor pattern.

## The table

| `Machine.Val` | `Store.Val` |
| --- | --- |
| `unit`, `nat n`, `bool b` | `unit`, `nat n`, `bool b` |
| `fiber id` | `Value.fiber id.value` (`handle 1`) |
| `fibers ids` | `Value.fiberSnapshot (list [Value.fiber …])` (`ctor 3`) |
| `cell k`, `promise k`, `scopeHandle s` | `Value.cell`, `Value.promise`, `Value.scope` (`handle 2/3/4`) |
| `context ctx` | `Value.fiberContext (option (Value.scope s)) (nat budget) (bool preventYield)` (`ctor 2`) |
| `exitOk v` | `Value.exitOk v'` (`ctor 0`) |
| `exitErr c` | `Value.exitErr (cause c)` (`ctor 1`, the cause at the generated rule) |
| `exitNil`, `exitCons h t` with `t` a list cell | `list [h', …]` |
| `exitCons h t`, `t` not a list cell | `ctor 4 [h', t']` (`RuntimeCtor.improperCons`) |

The snapshot and a list of exits are distinct on purpose: rc.112's `fiber.children` is a
`Set` (`internal/effect.ts:534`, `:703-704`), an exit list is an array, and the truth wire
renders them differently (`harness/truth/Truth.lean`); review R5 refused the collapse. The
improper-cons row is the migration rule for tails the old arm could spell: no producer builds
one (`exitsVal`, `Val.tuple` and `syncOpOf` all build proper cells), the view is exact on them
anyway, and U1 deletes the row with the arm.
-/

set_option autoImplicit false

namespace Effect4.Machine

open Effect4.Store (Image)

/-! ## The alphabets -/

def ofErr : Store.Val → Option Err
  | .ctor 0 [] => some .boom
  | .ctor 1 [.nat c] => some (.tag c)
  | _ => none

/-- `Err` at the generated rule: `boom` is `ctor 0 []`, `tag c` is `ctor 1 [nat c]`. -/
def Err.image : Image Err where
  toVal
    | .boom => .ctor 0 []
    | .tag c => .ctor 1 [.nat c]
  ofVal := ofErr
  ofVal_toVal e := by cases e <;> rfl
  ofVal_exact := by
    intro v e h
    unfold ofErr at h
    split at h <;> first | (injection h with h; subst h; rfl) | exact nomatch h

theorem Err.image_handleFree : Image.HandleFree Err.image := by
  intro e
  cases e <;> rfl

def ofDefect : Store.Val → Option Defect
  | .ctor 0 [] => some .notImplemented
  | .ctor 1 [] => some .asyncFiber
  | .ctor 2 [] => some .badName
  | .ctor 3 [] => some .missingService
  | .ctor 4 [.nat n] => some (.user n)
  | _ => none

/-- `Defect` at the generated rule, in declaration order; `user n` is `ctor 4 [nat n]`. -/
def Defect.image : Image Defect where
  toVal
    | .notImplemented => .ctor 0 []
    | .asyncFiber => .ctor 1 []
    | .badName => .ctor 2 []
    | .missingService => .ctor 3 []
    | .user n => .ctor 4 [.nat n]
  ofVal := ofDefect
  ofVal_toVal d := by cases d <;> rfl
  ofVal_exact := by
    intro v d h
    unfold ofDefect at h
    split at h <;> first | (injection h with h; subst h; rfl) | exact nomatch h

theorem Defect.image_handleFree : Image.HandleFree Defect.image := by
  intro d
  cases d <;> rfl

/-- The cause carrier at this instantiation (`Ann = Unit`). -/
def causeImage : Image CauseV :=
  Value.cause Err.image Defect.image Value.fiberIdentity Image.unit

theorem causeImage_handleFree : Image.HandleFree causeImage :=
  Value.cause_handleFree _ _ _ _ Err.image_handleFree Defect.image_handleFree
    Value.fiberIdentity_handleFree Image.unit_handleFree

/-! ## Handles -/

/-- A `Ref` cell as a value. -/
def cellHandle : Image RefKey :=
  (HandleKind.handleOf .cell).equiv RefKey.mk RefKey.index (fun _ => rfl) (fun _ => rfl)

/-- A `Deferred` cell as a value. -/
def promiseHandle : Image DeferredKey :=
  (HandleKind.handleOf .promise).equiv DeferredKey.mk DeferredKey.index (fun _ => rfl)
    (fun _ => rfl)

/-- A scope-store key as a value. (Named apart from the old constructor `Val.scopeHandle`.) -/
def scopeKeyHandle : Image Nat := HandleKind.handleOf .scope

/-- The kind byte and index of a minted handle: what `Store.Val.handles` reports for it. -/
def Handle.code : Handle → UInt8 × Nat
  | .fiber id => (1, id.value)
  | .cell k => (2, k.index)
  | .promise k => (3, k.index)
  | .scope s => (4, s)

def Handle.toStore : Handle → Store.Val
  | .fiber id => Value.fiber id.value
  | .cell k => Value.cell k.index
  | .promise k => Value.promise k.index
  | .scope s => Value.scope s

def Handle.ofStore : Store.Val → Option Handle
  | .handle b n =>
    match HandleKind.ofByte? b with
    | some .fiber => some (.fiber ⟨n⟩)
    | some .cell => some (.cell ⟨n⟩)
    | some .promise => some (.promise ⟨n⟩)
    | some .scope => some (.scope n)
    | _ => none
  | _ => none

/-- `Machine/Handles.lean`'s `Handle` as a value: the four minted kinds; a `memoMap` byte is
not a frame-machine handle and is refused. -/
def Handle.image : Image Handle where
  toVal := Handle.toStore
  ofVal := Handle.ofStore
  ofVal_toVal h := by cases h <;> rfl
  ofVal_exact := by
    intro v h hv
    unfold Handle.ofStore at hv
    split at hv
    · next b n =>
      split at hv <;> first
        | (next hk =>
            injection hv with hv
            subst hv
            rw [HandleKind.ofByte?_exact hk] <;> rfl)
        | exact nomatch hv
    · exact nomatch hv

theorem Handle.handles_toStore (h : Handle) : (Handle.toStore h).handles = [h.code] := by
  cases h <;> rfl

/-! ## The cached context -/

/-- `Ctx` (`Machine/Stores.lean`): `ctor 2 [option (scope handle), nat, bool]`. The ambient
scope is a handle, as `Ctx.keys` says. -/
def ctxImage : Image Ctx :=
  (Image.ctor3 (Image.option scopeKeyHandle) Image.nat Image.bool 2).equiv
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (fun c => (c.ambientScope, c.maxOpsBeforeYield, c.preventYield))
    (fun _ => rfl) (fun _ => rfl)

theorem ctxImage_toVal (ctx : Ctx) :
    ctxImage.toVal ctx =
      Value.fiberContext ((Image.option scopeKeyHandle).toVal ctx.ambientScope)
        (.nat ctx.maxOpsBeforeYield) (.bool ctx.preventYield) := rfl

/-! ## `Machine.Val` -/

namespace Val

/-- The old carrier written on the shared one (the table in the module header). -/
def toStore : Val → Store.Val
  | .unit => .unit
  | .nat n => .nat n
  | .bool b => .bool b
  | .fiber id => Value.fiber id.value
  | .fibers ids => Value.fiberSnapshot ((Image.list Value.fiberHandle).toVal ids)
  | .cell k => Value.cell k.index
  | .promise k => Value.promise k.index
  | .scopeHandle s => Value.scope s
  | .context ctx =>
    Value.fiberContext ((Image.option scopeKeyHandle).toVal ctx.ambientScope)
      (.nat ctx.maxOpsBeforeYield) (.bool ctx.preventYield)
  | .exitOk v => Value.exitOk (toStore v)
  | .exitErr c => Value.exitErr (causeImage.toVal c)
  | .exitNil => .list []
  | .exitCons h t =>
    match toStore t with
    | .list xs => Store.Val.list (toStore h :: xs)
    | t' => Store.Val.ctor 4 [toStore h, t']

mutual
/-- The shared carrier read back as the old one; `none` outside the image. -/
def ofStore : Store.Val → Option Val
  | .unit => some .unit
  | .nat n => some (.nat n)
  | .bool b => some (.bool b)
  | .handle b n =>
    match HandleKind.ofByte? b with
    | some .fiber => some (.fiber ⟨n⟩)
    | some .cell => some (.cell ⟨n⟩)
    | some .promise => some (.promise ⟨n⟩)
    | some .scope => some (.scopeHandle n)
    | _ => none
  | .ctor i args => ofCtor i args
  | .list vs => ofChain vs
  | _ => none
/-- A `ctor` frame by its runtime index. -/
def ofCtor : Nat → List Store.Val → Option Val
  | 0, [v] => (ofStore v).map .exitOk
  | 1, [c] => (causeImage.ofVal c).map .exitErr
  | 2, args => (ctxImage.ofVal (.ctor 2 args)).map .context
  | 3, [hs] => ((Image.list Value.fiberHandle).ofVal hs).map .fibers
  | 4, [h, t] =>
    if t.isList then none
    else
      match ofStore h, ofStore t with
      | some h', some t' => some (.exitCons h' t')
      | _, _ => none
  | _, _ => none
/-- A `list` frame as the exit-list cells. -/
def ofChain : List Store.Val → Option Val
  | [] => some .exitNil
  | v :: vs =>
    match ofStore v, ofChain vs with
    | some h, some t => some (.exitCons h t)
    | _, _ => none
end

theorem ofStore_toStore : ∀ v : Val, ofStore (toStore v) = some v
  | .unit => rfl
  | .nat _ => rfl
  | .bool _ => rfl
  | .fiber _ => rfl
  | .fibers ids => by
    show ((Image.list Value.fiberHandle).ofVal ((Image.list Value.fiberHandle).toVal ids)).map
      Val.fibers = some (.fibers ids)
    rw [Image.ofVal_toVal, Option.map_some]
  | .cell _ => rfl
  | .promise _ => rfl
  | .scopeHandle _ => rfl
  | .context ctx => by
    show (ctxImage.ofVal (ctxImage.toVal ctx)).map Val.context = some (.context ctx)
    rw [Image.ofVal_toVal, Option.map_some]
  | .exitOk v => by
    show (ofStore (toStore v)).map Val.exitOk = some (.exitOk v)
    rw [ofStore_toStore v, Option.map_some]
  | .exitErr c => by
    show (causeImage.ofVal (causeImage.toVal c)).map Val.exitErr = some (.exitErr c)
    rw [Image.ofVal_toVal, Option.map_some]
  | .exitNil => rfl
  | .exitCons h t => by
    have ihh := ofStore_toStore h
    have iht := ofStore_toStore t
    show ofStore (match toStore t with
      | .list xs => Store.Val.list (toStore h :: xs)
      | t' => Store.Val.ctor 4 [toStore h, t']) = some (.exitCons h t)
    generalize hT : toStore t = t' at iht ⊢
    cases t'
    case list xs =>
      have iht' : ofChain xs = some t := iht
      show (match ofStore (toStore h), ofChain xs with
        | some h', some t'' => some (Val.exitCons h' t'')
        | _, _ => none) = some (.exitCons h t)
      rw [ihh, iht'] <;> rfl
    all_goals
      show (match ofStore (toStore h), ofStore _ with
        | some h', some t'' => some (Val.exitCons h' t'')
        | _, _ => none) = some (.exitCons h t)
      rw [ihh, iht] <;> rfl

theorem ofChain_exact : ∀ (vs : List Store.Val),
    (∀ x ∈ vs, ∀ v : Val, ofStore x = some v → x = toStore v) →
    ∀ v : Val, ofChain vs = some v → toStore v = Store.Val.list vs
  | [], _, v, h => by
    simp only [ofChain] at h
    cases h
    rfl
  | x :: xs, ih, v, h => by
    simp only [ofChain] at h
    split at h
    · next h' t' hx ht =>
      injection h with h
      subst h
      have hxs := ofChain_exact xs (fun y hy => ih y (by simp [hy])) t' ht
      have hx' := ih x (by simp) h' hx
      show (match toStore t' with
        | .list ys => Store.Val.list (toStore h' :: ys)
        | t'' => Store.Val.ctor 4 [toStore h', t'']) = Store.Val.list (x :: xs)
      rw [hxs, ← hx'] <;> rfl
    · exact nomatch h

theorem ofStore_exact : ∀ (w : Store.Val) (v : Val), ofStore w = some v → w = toStore v := by
  intro w
  induction w using Store.Val.ind with
  | unit =>
    intro v h
    simp only [ofStore] at h
    cases h
    rfl
  | bool b =>
    intro v h
    simp only [ofStore] at h
    cases h
    rfl
  | nat n =>
    intro v h
    simp only [ofStore] at h
    cases h
    rfl
  | str s => intro v h; exact nomatch h
  | bytes bs => intro v h; exact nomatch h
  | pair a b _ _ => intro v h; exact nomatch h
  | none => intro v h; exact nomatch h
  | some a _ => intro v h; exact nomatch h
  | ref k d => intro v h; exact nomatch h
  | list xs ih =>
    intro v h
    simp only [ofStore] at h
    exact (ofChain_exact xs ih v h).symm
  | handle b n =>
    intro v h
    simp only [ofStore] at h
    split at h <;> first
      | (next hk =>
          injection h with h
          subst h
          rw [HandleKind.ofByte?_exact hk] <;> rfl)
      | exact nomatch h
  | ctor i args ih =>
    intro v h
    simp only [ofStore] at h
    unfold ofCtor at h
    split at h
    · next x =>
      obtain ⟨y, hy, hj⟩ := Option.map_eq_some_iff.mp h
      subst hj
      show Store.Val.ctor 0 [x] = Value.exitOk (toStore y)
      rw [ih x (by simp) y hy]
      rfl
    · next c =>
      obtain ⟨cause, hc, hj⟩ := Option.map_eq_some_iff.mp h
      subst hj
      show Store.Val.ctor 1 [c] = Value.exitErr (causeImage.toVal cause)
      rw [causeImage.ofVal_exact hc]
      rfl
    · next args' =>
      obtain ⟨ctx, hc, hj⟩ := Option.map_eq_some_iff.mp h
      subst hj
      exact ctxImage.ofVal_exact hc
    · next hs =>
      obtain ⟨ids, hids, hj⟩ := Option.map_eq_some_iff.mp h
      subst hj
      show Store.Val.ctor 3 [hs] = Value.fiberSnapshot ((Image.list Value.fiberHandle).toVal ids)
      rw [(Image.list Value.fiberHandle).ofVal_exact hids]
      rfl
    · next x t =>
      split at h
      · exact nomatch h
      · next hnl =>
        split at h
        · next x' t' hx ht =>
          injection h with h
          subst h
          have hx' := ih x (by simp) x' hx
          have ht' := ih t (by simp) t' ht
          show Store.Val.ctor 4 [x, t] = (match toStore t' with
            | .list ys => Store.Val.list (toStore x' :: ys)
            | t'' => Store.Val.ctor 4 [toStore x', t''])
          rw [← ht', ← hx']
          cases t <;> first | rfl | exact absurd rfl hnl
        · exact nomatch h
    · exact nomatch h

/-- The frame machine's value alphabet as an exact image of the shared carrier. -/
def image : Image Val := ⟨toStore, ofStore, ofStore_toStore, fun h => ofStore_exact _ _ h⟩

/-! ### The key discipline carried over

`Val.keys` (`Machine/Handles.lean`) lists the handles a value names; on the shared carrier
they are the `handle` frames, and the two agree exactly. A cause contributes none on either
side. -/

theorem snapshot_handles (ids : List FiberId) :
    Store.Val.handlesList (ids.map Value.fiberHandle.toVal) = ids.map (fun id => (1, id.value)) := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
    show Store.Val.handlesList (Value.fiberHandle.toVal id :: ids.map Value.fiberHandle.toVal) = _
    rw [Store.Val.handlesList_cons, ih]
    rfl

theorem handles_toStore : ∀ v : Val, (toStore v).handles = v.keys.map Handle.code
  | .unit => rfl
  | .nat _ => rfl
  | .bool _ => rfl
  | .fiber _ => rfl
  | .fibers ids => by
    show Store.Val.handles (.ctor 3 [.list (ids.map Value.fiberHandle.toVal)]) =
      (ids.map Handle.fiber).map Handle.code
    rw [Store.Val.handles, Store.Val.handlesList_cons, Store.Val.handlesList_nil, List.append_nil,
      Store.Val.handles, snapshot_handles, List.map_map]
    rfl
  | .cell _ => rfl
  | .promise _ => rfl
  | .scopeHandle _ => rfl
  | .context ctx => by
    rcases ctx with ⟨s, m, p⟩
    cases s <;> rfl
  | .exitOk v => by
    show Store.Val.handles (.ctor 0 [toStore v]) = v.keys.map Handle.code
    rw [Store.Val.handles, Store.Val.handlesList_cons, Store.Val.handlesList_nil, List.append_nil,
      handles_toStore v]
  | .exitErr c => by
    show Store.Val.handles (.ctor 1 [causeImage.toVal c]) = []
    rw [Store.Val.handles, Store.Val.handlesList_cons, causeImage_handleFree c,
      Store.Val.handlesList_nil]
    rfl
  | .exitNil => rfl
  | .exitCons h t => by
    have ihh := handles_toStore h
    have iht := handles_toStore t
    show Store.Val.handles (match toStore t with
      | .list xs => Store.Val.list (toStore h :: xs)
      | t' => Store.Val.ctor 4 [toStore h, t']) = (h.keys ++ t.keys).map Handle.code
    rw [List.map_append, ← ihh, ← iht]
    generalize toStore t = t'
    cases t' <;> simp only [Store.Val.handles, Store.Val.handlesList, List.append_nil]

/-! ### The spellings agree with the old constructors -/

theorem toStore_cell (k : RefKey) : toStore (.cell k) = Value.cell k.index := rfl
theorem toStore_promise (k : DeferredKey) : toStore (.promise k) = Value.promise k.index := rfl
theorem toStore_fiber (id : FiberId) : toStore (.fiber id) = Value.fiber id.value := rfl
theorem toStore_scopeHandle (s : Nat) : toStore (.scopeHandle s) = Value.scope s := rfl
theorem toStore_exitOk (v : Val) : toStore (.exitOk v) = Value.exitOk (toStore v) := rfl
theorem toStore_exitErr (c : CauseV) :
    toStore (.exitErr c) = Value.exitErr (causeImage.toVal c) := rfl
theorem toStore_exitNil : toStore .exitNil = .list [] := rfl

/-- A chain of exit cells: `exitNil`, or `exitCons` onto a chain. -/
def isChain : Val → Bool
  | .exitNil => true
  | .exitCons _ t => isChain t
  | _ => false

/-- A chain is written as one `list` frame; the improper row is never reached. -/
theorem toStore_chain : ∀ {t : Val}, isChain t = true → ∃ xs, toStore t = Store.Val.list xs
  | .exitNil, _ => ⟨[], rfl⟩
  | .exitCons h t, hc => by
    obtain ⟨xs, hxs⟩ := toStore_chain (t := t) hc
    exact ⟨toStore h :: xs, by
      show (match toStore t with
        | .list ys => Store.Val.list (toStore h :: ys)
        | t' => Store.Val.ctor 4 [toStore h, t']) = Store.Val.list (toStore h :: xs)
      rw [hxs]⟩

end Val

/-- The exit carrier at this instantiation. -/
def exitImage : Image ExitV := Value.exit Val.image causeImage

/-! ## Receipts -/

#guard Val.toStore (.cell ⟨2⟩) = Value.cell 2
#guard Val.toStore (.fibers [⟨1⟩, ⟨4⟩]) = Value.fiberSnapshot (.list [Value.fiber 1, Value.fiber 4])
#guard Val.toStore (.exitCons (.cell ⟨0⟩) (.exitCons (.nat 5) .exitNil)) =
  .list [Value.cell 0, .nat 5]
#guard Val.toStore (.exitCons (.nat 1) (.nat 2)) = .ctor 4 [.nat 1, .nat 2]
#guard Val.ofStore (.ctor 4 [.nat 1, .nat 2]) = some (.exitCons (.nat 1) (.nat 2))
#guard Val.ofStore (.ctor 4 [.nat 1, .list []]) = none
#guard Val.ofStore (.list [Value.fiber 1, Value.fiber 4]) =
  some (.exitCons (.fiber ⟨1⟩) (.exitCons (.fiber ⟨4⟩) .exitNil))
#guard Val.ofStore (Value.fiberSnapshot (.list [Value.fiber 1, Value.fiber 4])) =
  some (.fibers [⟨1⟩, ⟨4⟩])
#guard Val.ofStore (Value.memoMap 3) = none
#guard Val.ofStore (.handle 9 3) = none
#guard Val.ofStore (.str "x") = none
#guard (Val.toStore (.context ⟨some 3, 2048, false⟩)).handles = [(4, 3)]
#guard (Val.toStore (.exitErr (Cause.interrupt (some ⟨9⟩)))).handles = []
#guard Val.isChain (.exitCons (.nat 1) (.nat 2)) = false

#print axioms Err.image
#print axioms Defect.image
#print axioms causeImage
#print axioms Handle.image
#print axioms ctxImage
#print axioms Val.image
#print axioms Val.handles_toStore
#print axioms Val.toStore_chain
#print axioms exitImage

end Effect4.Machine
