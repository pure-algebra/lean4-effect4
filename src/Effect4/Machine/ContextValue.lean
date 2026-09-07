import Effect4.Machine.Value
import Effect4.Machine.Context

/-!
# Machine.ContextValue — the Layer machine's value alphabet as a view of the shared carrier

Owner: the exact images, in `Effect4.Store.Val`, of the alphabets `Machine/Context.lean`
instantiates the frame machine at for `Machine/Layer.lean` — `Env.Err`, `Env.Defect`,
`ServiceKey`, `Env.CauseV` and `Env.Val` itself. The runtime is unchanged; this is the
migration contract U1 performs for the Layer side
(`docs/research/2026-09-07-u0-value-foundation.md`).

## The table

| `Env.Val` | `Store.Val` |
| --- | --- |
| `unit`, `nat n`, `bool b` | `unit`, `nat n`, `bool b` |
| `fiber id` / `fibers ids` | `Value.fiber` / `Value.fiberSnapshot` as for `Machine.Val` |
| `scopeHandle s`, `memoMap id`, `promise cell` | `Value.scope`, `Value.memoMap`, `Value.promise` (`handle 4/5/3`) |
| `pair a b` | `pair a' b'` |
| `exitOk v`, `exitErr c`, `exitNil`, `exitCons h t` | as for `Machine.Val` (`ctor 0`, `ctor 1`, `list`, `ctor 4`) |
| `ctxNil`, `ctxCons key value rest` with `rest` a spine | `Value.serviceContext [pair key' value', …]` (`ctor 5`) |
| `ctxCons key value rest`, `rest` not a spine | `ctor 6 [key', value', rest']` (`RuntimeCtor.improperServiceCons`) |

A service context is rc.112's `Context` map (`Context.ts`), keyed by `ServiceKey` at the
generated rule (`Machine/Key.lean`; the generator's own instance for the same declaration
writes `ctor 0 [ctor 0 [nat], ctor 0 [nat]]`, `ocaml/eff/eff_wire.ml` `emit_service_key`). It
is distinct from the frame machine's cached `Ctx` (`Value.fiberContext`, `ctor 2`): the two
are joined by V1, not by this view. The two `improper*` rows are the migration rule for tails
the old arms could spell; `Context.lean`'s own `spine` already refuses them, no producer builds
one, and U1 deletes the rows with the arms.
-/

set_option autoImplicit false

namespace Effect4.Machine.Env

open Effect4.Store (Image)

/-! ## The alphabets -/

def ofErr : Store.Val → Option Err
  | .ctor 0 [] => some .boom
  | .ctor 1 [.nat c] => some (.tag c)
  | _ => none

/-- `Env.Err` at the generated rule. -/
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

/-- `ServiceKey` (`Machine/Key.lean`) at the generated rule: the pair of the two one-field
structures, each `ctor 0 [nat]`. -/
def serviceKeyImage : Image ServiceKey :=
  (Image.ctor2 (Image.nat.ctor1 0) (Image.nat.ctor1 0) 0).equiv
    (fun p => ⟨⟨p.1⟩, ⟨p.2⟩⟩) (fun k => (k.name.value, k.service.value))
    (fun _ => rfl) (fun _ => rfl)

theorem serviceKeyImage_toVal (k : ServiceKey) :
    serviceKeyImage.toVal k =
      .ctor 0 [.ctor 0 [.nat k.name.value], .ctor 0 [.nat k.service.value]] := rfl

theorem serviceKeyImage_handleFree : Image.HandleFree serviceKeyImage :=
  Image.equiv_handleFree _ _ _ _ _
    (Image.ctor2_handleFree _ _ _ (Image.ctor1_handleFree _ _ Image.nat_handleFree)
      (Image.ctor1_handleFree _ _ Image.nat_handleFree))

def ofDefect : Store.Val → Option Defect
  | .ctor 0 [] => some .notImplemented
  | .ctor 1 [] => some .asyncFiber
  | .ctor 2 [] => some .badName
  | .ctor 3 [k] => (serviceKeyImage.ofVal k).map .serviceNotFound
  | .ctor 4 [.nat i] => some (.unknownLayer i)
  | _ => none

/-- `Env.Defect` at the generated rule; `serviceNotFound key` carries the key's image. -/
def Defect.image : Image Defect where
  toVal
    | .notImplemented => .ctor 0 []
    | .asyncFiber => .ctor 1 []
    | .badName => .ctor 2 []
    | .serviceNotFound k => .ctor 3 [serviceKeyImage.toVal k]
    | .unknownLayer i => .ctor 4 [.nat i]
  ofVal := ofDefect
  ofVal_toVal d := by
    cases d
    case serviceNotFound k =>
      show (serviceKeyImage.ofVal (serviceKeyImage.toVal k)).map Defect.serviceNotFound =
        some (.serviceNotFound k)
      rw [Image.ofVal_toVal, Option.map_some]
    all_goals rfl
  ofVal_exact := by
    intro v d h
    unfold ofDefect at h
    split at h <;> first
      | (injection h with h; subst h; rfl)
      | (next k =>
          obtain ⟨key, hk, hj⟩ := Option.map_eq_some_iff.mp h
          subst hj
          show Store.Val.ctor 3 [k] = Store.Val.ctor 3 [serviceKeyImage.toVal key]
          rw [serviceKeyImage.ofVal_exact hk])
      | exact nomatch h

theorem Defect.image_handleFree : Image.HandleFree Defect.image := by
  intro d
  cases d
  case serviceNotFound k =>
    show (Store.Val.ctor 3 [serviceKeyImage.toVal k]).handles = []
    rw [Store.Val.handles, Store.Val.handlesList_cons, serviceKeyImage_handleFree k,
      Store.Val.handlesList_nil]
    rfl
  all_goals rfl

/-- The cause carrier at this instantiation (`Ann = Unit`). -/
def causeImage : Image CauseV :=
  Value.cause Err.image Defect.image Value.fiberIdentity Image.unit

theorem causeImage_handleFree : Image.HandleFree causeImage :=
  Value.cause_handleFree _ _ _ _ Err.image_handleFree Defect.image_handleFree
    Value.fiberIdentity_handleFree Image.unit_handleFree

/-! ## `Env.Val` -/

/-- The items of a `list` frame. -/
def listItems? : Store.Val → Option (List Store.Val)
  | .list xs => some xs
  | _ => none

theorem listItems?_exact {w : Store.Val} {xs : List Store.Val} (h : listItems? w = some xs) :
    w = Store.Val.list xs := by
  unfold listItems? at h
  split at h
  · injection h with h
    subst h
    rfl
  · exact nomatch h

/-- The entries of a service-context frame. -/
def spineEntries? : Store.Val → Option (List Store.Val)
  | .ctor 5 es => some es
  | _ => none

theorem spineEntries?_exact {w : Store.Val} {es : List Store.Val} (h : spineEntries? w = some es) :
    w = Store.Val.ctor 5 es := by
  unfold spineEntries? at h
  split at h
  · injection h with h
    subst h
    rfl
  · exact nomatch h

namespace Val

/-- The old carrier written on the shared one (the table in the module header). -/
def toStore : Val → Store.Val
  | .unit => .unit
  | .nat n => .nat n
  | .bool b => .bool b
  | .fiber id => Value.fiber id.value
  | .fibers ids => Value.fiberSnapshot ((Image.list Value.fiberHandle).toVal ids)
  | .scopeHandle s => Value.scope s
  | .memoMap id => Value.memoMap id
  | .promise cell => Value.promise cell
  | .pair a b => Store.Val.pair (toStore a) (toStore b)
  | .exitOk v => Value.exitOk (toStore v)
  | .exitErr c => Value.exitErr (causeImage.toVal c)
  | .exitNil => Store.Val.list []
  | .exitCons h t =>
    match listItems? (toStore t) with
    | some xs => Store.Val.list (toStore h :: xs)
    | none => Store.Val.ctor 4 [toStore h, toStore t]
  | .ctxNil => Value.serviceContext []
  | .ctxCons key value rest =>
    match spineEntries? (toStore rest) with
    | some es =>
      Value.serviceContext (Store.Val.pair (serviceKeyImage.toVal key) (toStore value) :: es)
    | none => Store.Val.ctor 6 [serviceKeyImage.toVal key, toStore value, toStore rest]

/-- One context entry, written. -/
def entryStore (key : ServiceKey) (value : Val) : Store.Val :=
  Store.Val.pair (serviceKeyImage.toVal key) (toStore value)

mutual
/-- The shared carrier read back as the old one; `none` outside the image. -/
def ofStore : Store.Val → Option Val
  | .unit => some .unit
  | .nat n => some (.nat n)
  | .bool b => some (.bool b)
  | .handle b n =>
    match HandleKind.ofByte? b with
    | some .fiber => some (.fiber ⟨n⟩)
    | some .scope => some (.scopeHandle n)
    | some .memoMap => some (.memoMap n)
    | some .promise => some (.promise n)
    | _ => none
  | .pair a b =>
    match ofStore a, ofStore b with
    | some x, some y => some (.pair x y)
    | _, _ => none
  | .ctor i args => ofCtor i args
  | .list vs => ofChain vs
  | _ => none
/-- One context entry, read: a `pair` of a key and a value. -/
def ofEntry : Store.Val → Option (ServiceKey × Val)
  | .pair k v =>
    match serviceKeyImage.ofVal k, ofStore v with
    | some key, some value => some (key, value)
    | _, _ => none
  | _ => none
/-- A `ctor` frame by its runtime index. -/
def ofCtor : Nat → List Store.Val → Option Val
  | 0, [v] => (ofStore v).map .exitOk
  | 1, [c] => (causeImage.ofVal c).map .exitErr
  | 3, [hs] => ((Image.list Value.fiberHandle).ofVal hs).map .fibers
  | 4, [h, t] =>
    if (listItems? t).isSome then none
    else
      match ofStore h, ofStore t with
      | some h', some t' => some (.exitCons h' t')
      | _, _ => none
  -- The service-context entries as the spine cells (`ofCtor 5` is the spine reader; a call
  -- on the whole list would not be structural).
  | 5, [] => some .ctxNil
  | 5, e :: es =>
    match ofEntry e, ofCtor 5 es with
    | some (key, value), some rest => some (.ctxCons key value rest)
    | _, _ => none
  | 6, [k, v, r] =>
    if (spineEntries? r).isSome then none
    else
      match serviceKeyImage.ofVal k, ofStore v, ofStore r with
      | some key, some value, some rest => some (.ctxCons key value rest)
      | _, _, _ => none
  | _, _ => none
/-- A `list` frame as the exit-list cells. -/
def ofChain : List Store.Val → Option Val
  | [] => some .exitNil
  | v :: vs =>
    match ofStore v, ofChain vs with
    | some h, some t => some (.exitCons h t)
    | _, _ => none
end

theorem ofEntry_entryStore (key : ServiceKey) (value : Val)
    (ih : ofStore (toStore value) = some value) :
    ofEntry (entryStore key value) = some (key, value) := by
  show (match serviceKeyImage.ofVal (serviceKeyImage.toVal key), ofStore (toStore value) with
    | some key, some value => some (key, value)
    | _, _ => none) = some (key, value)
  rw [Image.ofVal_toVal, ih]

theorem ofStore_toStore : ∀ v : Val, ofStore (toStore v) = some v
  | .unit => rfl
  | .nat _ => rfl
  | .bool _ => rfl
  | .fiber _ => rfl
  | .fibers ids => by
    show ((Image.list Value.fiberHandle).ofVal ((Image.list Value.fiberHandle).toVal ids)).map
      Val.fibers = some (.fibers ids)
    rw [Image.ofVal_toVal, Option.map_some]
  | .scopeHandle _ => rfl
  | .memoMap _ => rfl
  | .promise _ => rfl
  | .pair a b => by
    show (match ofStore (toStore a), ofStore (toStore b) with
      | some x, some y => some (Val.pair x y)
      | _, _ => none) = some (.pair a b)
    rw [ofStore_toStore a, ofStore_toStore b]
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
    show ofStore (match listItems? (toStore t) with
      | some xs => Store.Val.list (toStore h :: xs)
      | none => Store.Val.ctor 4 [toStore h, toStore t]) = some (.exitCons h t)
    cases hl : listItems? (toStore t) with
    | some xs =>
      rw [listItems?_exact hl] at iht
      have iht' : ofChain xs = some t := iht
      show (match ofStore (toStore h), ofChain xs with
        | some h', some t'' => some (Val.exitCons h' t'')
        | _, _ => none) = some (.exitCons h t)
      rw [ihh, iht']
    | none =>
      show (if (listItems? (toStore t)).isSome then none
        else match ofStore (toStore h), ofStore (toStore t) with
          | some h', some t'' => some (Val.exitCons h' t'')
          | _, _ => none) = some (.exitCons h t)
      rw [hl]
      show (match ofStore (toStore h), ofStore (toStore t) with
        | some h', some t'' => some (Val.exitCons h' t'')
        | _, _ => none) = some (.exitCons h t)
      rw [ihh, iht]
  | .ctxNil => rfl
  | .ctxCons key value rest => by
    have ihv := ofStore_toStore value
    have ihr := ofStore_toStore rest
    show ofStore (match spineEntries? (toStore rest) with
      | some es => Value.serviceContext (entryStore key value :: es)
      | none => Store.Val.ctor 6 [serviceKeyImage.toVal key, toStore value, toStore rest]) =
      some (.ctxCons key value rest)
    cases hs : spineEntries? (toStore rest) with
    | some es =>
      rw [spineEntries?_exact hs] at ihr
      have ihr' : ofCtor 5 es = some rest := ihr
      show (match ofEntry (entryStore key value), ofCtor 5 es with
        | some (key, value), some rest => some (Val.ctxCons key value rest)
        | _, _ => none) = some (.ctxCons key value rest)
      rw [ofEntry_entryStore key value ihv, ihr']
    | none =>
      show (if (spineEntries? (toStore rest)).isSome then none
        else match serviceKeyImage.ofVal (serviceKeyImage.toVal key), ofStore (toStore value),
            ofStore (toStore rest) with
          | some key, some value, some rest => some (Val.ctxCons key value rest)
          | _, _, _ => none) = some (.ctxCons key value rest)
      rw [hs]
      show (match serviceKeyImage.ofVal (serviceKeyImage.toVal key), ofStore (toStore value),
          ofStore (toStore rest) with
        | some key, some value, some rest => some (Val.ctxCons key value rest)
        | _, _, _ => none) = some (.ctxCons key value rest)
      rw [Image.ofVal_toVal, ihv, ihr]

/-- Exactness of the value reader at a tree. -/
def ExactV (w : Store.Val) : Prop := ∀ v : Val, ofStore w = some v → w = toStore v

/-- Exactness of the entry reader at a tree. -/
def ExactE (w : Store.Val) : Prop :=
  ∀ (key : ServiceKey) (value : Val), ofEntry w = some (key, value) → w = entryStore key value

theorem ofChain_exact : ∀ (vs : List Store.Val), (∀ x ∈ vs, ExactV x) →
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
      show (match listItems? (toStore t') with
        | some ys => Store.Val.list (toStore h' :: ys)
        | none => Store.Val.ctor 4 [toStore h', toStore t']) = Store.Val.list (x :: xs)
      rw [hxs, ← hx']
      rfl
    · exact nomatch h

theorem ofSpine_exact : ∀ (es : List Store.Val), (∀ e ∈ es, ExactE e) →
    ∀ v : Val, ofCtor 5 es = some v → toStore v = Value.serviceContext es
  | [], _, v, h => by
    simp only [ofCtor] at h
    cases h
    rfl
  | e :: es, ih, v, h => by
    simp only [ofCtor] at h
    split at h
    · next key value rest he hes =>
      injection h with h
      subst h
      have hes' := ofSpine_exact es (fun y hy => ih y (by simp [hy])) rest hes
      have he' := ih e (by simp) key value he
      show (match spineEntries? (toStore rest) with
        | some es' => Value.serviceContext (entryStore key value :: es')
        | none => Store.Val.ctor 6 [serviceKeyImage.toVal key, toStore value, toStore rest]) =
        Value.serviceContext (e :: es)
      rw [hes', ← he']
      rfl
    · exact nomatch h

theorem ofStore_exact_aux : ∀ w : Store.Val, ExactV w ∧ ExactE w := by
  intro w
  induction w using Store.Val.ind with
  | unit =>
    refine ⟨?_, (fun _ _ h => nomatch h)⟩
    intro v h
    simp only [ofStore] at h
    cases h
    rfl
  | bool b =>
    refine ⟨?_, (fun _ _ h => nomatch h)⟩
    intro v h
    simp only [ofStore] at h
    cases h
    rfl
  | nat n =>
    refine ⟨?_, (fun _ _ h => nomatch h)⟩
    intro v h
    simp only [ofStore] at h
    cases h
    rfl
  | str s => exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | bytes bs => exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | none => exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | some a _ => exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | ref k d => exact ⟨(fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  | pair a b iha ihb =>
    constructor
    · intro v h
      simp only [ofStore] at h
      split at h
      · next x y hx hy =>
        injection h with h
        subst h
        show Store.Val.pair a b = Store.Val.pair (toStore x) (toStore y)
        rw [iha.1 x hx, ihb.1 y hy]
      · exact nomatch h
    · intro key value h
      simp only [ofEntry] at h
      split at h
      · next key' value' hk hv =>
        injection h with h
        injection h with hk' hv'
        subst hk' hv'
        unfold entryStore
        rw [serviceKeyImage.ofVal_exact hk, ihb.1 _ hv]
      · exact nomatch h
  | list xs ih =>
    refine ⟨?_, (fun _ _ h => nomatch h)⟩
    intro v h
    simp only [ofStore] at h
    exact (ofChain_exact xs (fun x hx => (ih x hx).1) v h).symm
  | handle b n =>
    refine ⟨?_, (fun _ _ h => nomatch h)⟩
    intro v h
    simp only [ofStore] at h
    split at h <;> first
      | (next hk =>
          injection h with h
          subst h
          rw [HandleKind.ofByte?_exact hk] <;> rfl)
      | exact nomatch h
  | ctor i args ih =>
    refine ⟨?_, (fun _ _ h => nomatch h)⟩
    intro v h
    simp only [ofStore] at h
    unfold ofCtor at h
    split at h
    · next x =>
      obtain ⟨y, hy, hj⟩ := Option.map_eq_some_iff.mp h
      subst hj
      show Store.Val.ctor 0 [x] = Value.exitOk (toStore y)
      rw [(ih x (by simp)).1 y hy]
      rfl
    · next c =>
      obtain ⟨cause, hc, hj⟩ := Option.map_eq_some_iff.mp h
      subst hj
      show Store.Val.ctor 1 [c] = Value.exitErr (causeImage.toVal cause)
      rw [causeImage.ofVal_exact hc]
      rfl
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
          have hx' := (ih x (by simp)).1 x' hx
          have ht' := (ih t (by simp)).1 t' ht
          show Store.Val.ctor 4 [x, t] = (match listItems? (toStore t') with
            | some ys => Store.Val.list (toStore x' :: ys)
            | none => Store.Val.ctor 4 [toStore x', toStore t'])
          rw [← ht', ← hx']
          cases hl : listItems? t with
          | some ys => exact absurd (by rw [hl]; rfl) hnl
          | none => rfl
        · exact nomatch h
    · cases h
      rfl
    · next e es =>
      exact (ofSpine_exact (e :: es) (fun x hx => (ih x hx).2) v h).symm
    · next k x r =>
      split at h
      · exact nomatch h
      · next hns =>
        split at h
        · next key value rest hk hv hr =>
          injection h with h
          subst h
          have hv' := (ih x (by simp)).1 value hv
          have hr' := (ih r (by simp)).1 rest hr
          show Store.Val.ctor 6 [k, x, r] = (match spineEntries? (toStore rest) with
            | some es => Value.serviceContext (entryStore key value :: es)
            | none => Store.Val.ctor 6 [serviceKeyImage.toVal key, toStore value, toStore rest])
          rw [← hr', ← hv', ← serviceKeyImage.ofVal_exact hk]
          cases hs : spineEntries? r with
          | some es => exact absurd (by rw [hs]; rfl) hns
          | none => rfl
        · exact nomatch h
    · exact nomatch h

theorem ofStore_exact (w : Store.Val) (v : Val) (h : ofStore w = some v) : w = toStore v :=
  (ofStore_exact_aux w).1 v h

/-- The Layer machine's value alphabet as an exact image of the shared carrier. -/
def image : Image Val := ⟨toStore, ofStore, ofStore_toStore, fun h => ofStore_exact _ _ h⟩

/-- A written context spine reads back as the same entries: `Context.lean`'s `decode_encode`
on the shared carrier. -/
theorem ofSpine_entries (c : Ctx) :
    ofCtor 5 (c.entries.map fun s => entryStore s.key s.valueVal) = some (encode c) := by
  have : ∀ es : List (Service ValU),
      ofCtor 5 (es.map fun s => entryStore s.key s.valueVal) = some (encodeEntries es) := by
    intro es
    induction es with
    | nil => rfl
    | cons s rest ih =>
      show (match ofEntry (entryStore s.key s.valueVal),
          ofCtor 5 (rest.map fun s => entryStore s.key s.valueVal) with
        | some (key, value), some rest => some (Val.ctxCons key value rest)
        | _, _ => none) = some (Val.ctxCons s.key s.valueVal (encodeEntries rest))
      rw [ofEntry_entryStore s.key s.valueVal (ofStore_toStore s.valueVal), ih]
  exact this c.entries

end Val

/-- The exit carrier at this instantiation. -/
def exitImage : Image ExitV := Value.exit Val.image causeImage

/-! ## Receipts -/

#guard Val.toStore .ctxNil = Value.serviceContext []
#guard Val.toStore (.ctxCons ⟨⟨1⟩, ⟨2⟩⟩ (.nat 7) .ctxNil) =
  Value.serviceContext [.pair (.ctor 0 [.ctor 0 [.nat 1], .ctor 0 [.nat 2]]) (.nat 7)]
#guard Val.ofStore (Value.serviceContext [.pair (.ctor 0 [.ctor 0 [.nat 1], .ctor 0 [.nat 2]]) (.nat 7)]) =
  some (.ctxCons ⟨⟨1⟩, ⟨2⟩⟩ (.nat 7) .ctxNil)
#guard Val.ofStore (Value.serviceContext [.nat 7]) = none
#guard Val.ofStore (Value.serviceContext [.pair (.nat 1) (.nat 7)]) = none
#guard Val.toStore (.ctxCons ⟨⟨1⟩, ⟨2⟩⟩ (.nat 7) (.nat 0)) =
  .ctor 6 [.ctor 0 [.ctor 0 [.nat 1], .ctor 0 [.nat 2]], .nat 7, .nat 0]
#guard Val.ofStore (.ctor 6 [.ctor 0 [.ctor 0 [.nat 1], .ctor 0 [.nat 2]], .nat 7, .nat 0]) =
  some (.ctxCons ⟨⟨1⟩, ⟨2⟩⟩ (.nat 7) (.nat 0))
#guard Val.ofStore (.ctor 6 [.ctor 0 [.ctor 0 [.nat 1], .ctor 0 [.nat 2]], .nat 7, .ctor 5 []]) = none
#guard Val.toStore (.memoMap 3) = Value.memoMap 3
#guard Val.ofStore (Value.cell 3) = none
#guard Val.toStore (.pair (.promise 1) (.memoMap 2)) = .pair (Value.promise 1) (Value.memoMap 2)
#guard (Val.toStore (.exitErr (Cause.die (Defect.serviceNotFound ⟨⟨1⟩, ⟨2⟩⟩)))).handles = []

#print axioms Err.image
#print axioms Defect.image
#print axioms serviceKeyImage
#print axioms causeImage
#print axioms Val.image
#print axioms Val.ofSpine_entries
#print axioms exitImage

end Effect4.Machine.Env
