import Effect4.Laws.Machine.Handles

/-!
# Machine.StoresValue — the handle image, and the receipts of the value cutover

Owner: what remains of the U0 view of `Machine.Val` after the cutover (U1a,
`docs/research/2026-09-07-u1-cutover-dispatch.md`). `Machine.Val` *is* the shared carrier
(`Machine/Stores.lean`: `abbrev Val := Effect4.Store.Val`), so the view's `toStore`/`ofStore`
were the identity and are gone; the images of the alphabets (`Err.image`, `Defect.image`,
`causeImage`, `ctxImage`, `exitImage`, the handle images) live beside the alphabets in
`Machine/Stores.lean`. What still has a consumer here is the image of `Machine/Handles.lean`'s
`Handle`, and the receipts: the spellings are the U0 table's shapes by `rfl`, and the key
discipline (`Val.keys`) is the carrier's `handles` read through `Handle.ofCode`.

## The table, now by `rfl`

| `Machine.Val` | `Store.Val` |
| --- | --- |
| `unit`, `nat n`, `bool b` | the carrier's own |
| `fiber id` | `Value.fiber id.value` (`handle 1`) |
| `fibers ids` | `Value.fiberSnapshot (list [Value.fiber …])` (`ctor 3`) |
| `cell k`, `promise k`, `scopeHandle s` | `Value.cell`, `Value.promise`, `Value.scope` (`handle 2/3/4`) |
| `context ctx` | `Value.fiberContext (serviceContext entries) (nat budget) (bool preventYield)` (`ctor 2`) |
| `exitOk v` | `Value.exitOk v` (`ctor 0`) |
| `exitErr c` | `Value.exitErr (causeImage.toVal c)` (`ctor 1`) |
| an exit list, a tuple | one `list` frame |

The snapshot and a list of exits are distinct on purpose: rc.112's `fiber.children` is a
`Set` (`internal/effect.ts:534`, `:703-704`), an exit list is an array, and the truth wire
renders them differently (`harness/truth/Truth.lean`); review R5 refused the collapse. The
U0 rows for improper tails are gone with the arms that could spell them.
-/

set_option autoImplicit false

namespace Effect4.Machine

open Effect4.Store (Image)

/-! ## The handle image -/

def Handle.toStore : Handle → Store.Val
  | .fiber id => Val.fiber id
  | .cell k => Val.cell k
  | .promise k => Val.promise k
  | .scope s => Val.scopeHandle s
  | .memoMap id => Val.memoMap ⟨id⟩
  | .external key => Value.external key

def Handle.ofStore : Store.Val → Option Handle
  | .handle kind index => Handle.ofCode (kind, index)
  | _ => none

/-- `Machine/Handles.lean`'s `Handle` as a value, including external allocations at byte 7;
an unregistered byte is refused. -/
def Handle.image : Image Handle where
  toVal := Handle.toStore
  ofVal := Handle.ofStore
  ofVal_toVal h := by cases h <;> rfl
  ofVal_exact := by
    intro v h hv
    unfold Handle.ofStore at hv
    split at hv
    · next kind index =>
      unfold Handle.ofCode at hv
      split at hv <;> first
        | (next hk =>
            injection hv with hv
            subst hv
            have hk' : kind = _ := HandleKind.ofByte?_exact hk
            subst hk'
            rfl)
        | exact nomatch hv
    · exact nomatch hv

theorem Handle.keys_toStore (h : Handle) : Val.keys (Handle.toStore h) = [h] := by
  cases h <;> rfl

theorem Handle.handles_toStore (h : Handle) : (Handle.toStore h).handles = [h.code] := by
  cases h <;> rfl

/-! ## Receipts: the spellings are the table's shapes -/

theorem Val.fiber_eq (id : FiberId) : Val.fiber id = Value.fiber id.value := rfl
theorem Val.cell_eq (k : RefKey) : Val.cell k = Value.cell k.index := rfl
theorem Val.promise_eq (k : DeferredKey) : Val.promise k = Value.promise k.index := rfl
theorem Val.scopeHandle_eq (s : Nat) : Val.scopeHandle s = Value.scope s := rfl
theorem Val.exitOk_eq (v : Val) : Val.exitOk v = Value.exitOk v := rfl
theorem Val.exitErr_eq (c : CauseV) : Val.exitErr c = Value.exitErr (causeImage.toVal c) := rfl
theorem Val.exitNil_eq : Val.exitNil = Store.Val.list [] := rfl
theorem Val.context_eq' (ctx : Ctx) : Val.context ctx = ctxImage.toVal ctx := rfl
theorem exitsVal_eq (exits : List ExitV) : exitsVal exits = Store.Val.list (exits.map reifyExitVal) := rfl

/-- Codes that all read back are the codes of the handles they read back to. -/
theorem Handle.codes_of_all (codes : List (UInt8 × Nat))
    (hall : ∀ c ∈ codes, (Handle.ofCode c).isSome) :
    codes = (codes.filterMap Handle.ofCode).map Handle.code := by
  induction codes with
  | nil => rfl
  | cons c rest ih =>
    rw [List.filterMap_cons]
    have hc' := hall c (List.mem_cons_self ..)
    cases hc : Handle.ofCode c with
    | none => rw [hc] at hc'; exact nomatch hc'
    | some handle =>
      rw [List.map_cons, Handle.code_ofCode hc,
        ← ih (fun x hx => hall x (List.mem_cons_of_mem _ hx))]

/-- The migration check of the key discipline, restated on the identity: what U0 proved as
`(toStore v).handles = v.keys.map Handle.code` is now `Val.keys_eq_handles` plus this, on a
value whose handle frames are all frame-machine handles. -/
theorem Val.handles_eq_keys_code (v : Val) (hall : ∀ h ∈ v.handles, (Handle.ofCode h).isSome) :
    v.handles = v.keys.map Handle.code := by
  rw [Val.keys_eq_handles]
  exact Handle.codes_of_all v.handles hall

/-! ## Receipts -/

#guard Val.fiber ⟨3⟩ = Store.Val.handle 1 3
#guard Val.cell ⟨2⟩ = Value.cell 2
#guard Val.fibers [⟨1⟩, ⟨4⟩] = Value.fiberSnapshot (.list [Value.fiber 1, Value.fiber 4])
#guard Val.exitNil = Store.Val.list []
#guard exitsVal [Exit.success (Val.nat 5)] = Store.Val.list [Val.exitOk (Val.nat 5)]
#guard Val.snapshot? (Val.fibers [⟨1⟩, ⟨4⟩]) = some [⟨1⟩, ⟨4⟩]
#guard Val.snapshot? (Value.fiberSnapshot (.list [Val.nat 1])) = none
#guard Val.snapshot? (Store.Val.list [Value.fiber 1]) = none
#guard Val.context? (Val.context (emptyCtx.withScope 3)) = some (emptyCtx.withScope 3)
#guard (emptyCtx.withScope 3).ambientScope = some 3
#guard Val.context? (Value.fiberContext (.some (.nat 2)) (.nat 0) (.bool true)) = none
#guard Val.cause? (Val.exitErr (Cause.interrupt (some ⟨9⟩))) = some (Cause.interrupt (some ⟨9⟩))
#guard Val.cause? (Value.exitErr (Store.Val.ctor 0 [Store.Val.list [Store.Val.ctor 7 []]])) = none
#guard (Val.context (emptyCtx.withScope 3)).keys = [Handle.scope 3]
#guard (Val.context (emptyCtx.withScope 3)).handles = [(4, 3)]
-- the install keeps the cache law
#guard (emptyCtx.withScope 3).CacheAgrees
#guard (Val.exitErr (Cause.interrupt (some ⟨9⟩))).handles = []
#guard (Val.exitErr (Cause.interrupt (some ⟨9⟩))).keys = []
#guard Val.keys (Value.memoMap 3) = [Handle.memoMap 3]
#guard Val.keys (Store.Val.handle 9 3) = []
#guard Handle.image.ofVal (Value.memoMap 3) = some (Handle.memoMap 3)
#guard Handle.image.ofVal (.handle 7 3) = some (Handle.external 3)
#guard Handle.image.ofVal (Val.cell ⟨2⟩) = some (Handle.cell ⟨2⟩)
#guard (exitImage.encode? (Exit.success (Val.fibers [⟨1⟩]))).isSome

#print axioms Handle.image
#print axioms Val.keys_eq_handles
#print axioms Val.handles_eq_keys_code
#print axioms exitImage
#print axioms reifyExitVal_eq_exitImage

end Effect4.Machine
