import Effect4.Store.Image
import Effect4.Machine.Exit
import Effect4.Machine.Fiber

/-!
# Machine.Value — the shared value foundation, Machine side

Owner: what the runtime adds to the shared carrier `Effect4.Store.Val` and nothing else: the
handle-kind byte table, the runtime constructor-index table, the pattern spellings of the
runtime's shapes over the carrier, and the images of the semantic records every value
alphabet shares — fiber identity, reason annotations, reasons, causes and exits.

Plan: `docs/research/2026-09-06-wave2-synthesis.md` §5 (U0/U1) as corrected by
`docs/research/2026-09-07-consolidation-review.md` R5; record
`docs/research/2026-09-07-u0-value-foundation.md`. This module imports the carrier and the
cause/exit records only; the views of `Machine.Val` (`Machine/StoresValue.lean`), `Env.Val`
(`Machine/ContextValue.lean`) and `Config.Val` (`Program/ConfigValue.lean`) build on it and
stay with their owners.

## Two things a value can name

A *handle* is a live allocation in a running machine's stores: rc.112's `FiberImpl`
(`internal/effect.ts:534`), `Ref` (`Ref.ts:142-146`), `Deferred` (`Deferred.ts:140-145`),
`Scope` (`internal/effect.ts:3914-3922`) and `MemoMap` (`Layer.ts:421-458`) objects. It is the
carrier's `handle` frame (tag 12) with a kind byte from `HandleKind`; the byte table is
separate from `Store.Kind`, which numbers *content* kinds, because a handle is not content
and no node carries one (`Store/Val.lean`). Distinct kinds stay distinct: the typing
(`Program/Typed.lean` `Val.hasTy`), the key discipline (`Machine/Handles.lean` `Val.keys`)
and the truth wire (`harness/truth/Truth.lean`) all read the kind.

A *record* — an exit, a cause, a reason, a context — is ordinary first-order data and is
written at the generated rule (`src/Effect4/Program/Derived.lean`): a structure is
`ctor 0 [fields…]`, a case of a sum is `ctor i [args…]` with `i` the declaration index. rc.112
distinguishes an `Exit` by its `_tag` (`Exit.ts:119`, `:155`), a structural mark on an
otherwise ordinary object; the constructor index is that mark. The indices the runtime reads
at the top of a value are `RuntimeCtor`; nested records carry their own local indices, read
only after the enclosing index has been seen.

## What is deliberately two images

`FiberId` has two images. As a *value* a fiber is a handle (`fiberHandle`, tag 12 kind 1):
`Val.keys` counts it, the machine must have minted it. As the *interruptor recorded in a
cause* it is an identity (`fiberIdentity`, `ctor 0 [nat]`, the generated rule for the
structure): `Val.keys` does not count it — "a reified failed exit carries a cause only" — and
`cause_handleFree` is that fact on the shared carrier.
-/

set_option autoImplicit false

namespace Effect4.Machine

open Effect4.Store (Val Image)

/-! ## Handle kinds -/

/-- The kinds of live handle, in `Machine/Handles.lean`'s `Handle` order with `MemoMap`
(`Machine/Context.lean` `Env.Val.memoMap`) after them. Byte 6 is reserved for `Queue`
(`docs/research/2026-09-05-stdlib-primitives-ingestion.md`). Bytes are identity: appended,
never renumbered. -/
inductive HandleKind
  | fiber
  | cell
  | promise
  | scope
  | memoMap
  | external
deriving DecidableEq, Repr

namespace HandleKind

/-- The kind byte. -/
def byte : HandleKind → UInt8
  | fiber => 1
  | cell => 2
  | promise => 3
  | scope => 4
  | memoMap => 5
  | external => 7

/-- The kind of a byte; an unregistered byte is no kind. -/
def ofByte? (b : UInt8) : Option HandleKind :=
  if b = 1 then some fiber
  else if b = 2 then some cell
  else if b = 3 then some promise
  else if b = 4 then some scope
  else if b = 5 then some memoMap
  else if b = 7 then some external
  else none

theorem ofByte?_byte (k : HandleKind) : ofByte? k.byte = some k := by
  cases k <;> rfl

theorem ofByte?_exact {b : UInt8} {k : HandleKind} (h : ofByte? b = some k) : b = k.byte := by
  unfold ofByte? at h
  split at h
  · next h1 =>
    injection h with h
    subst h
    exact h1
  split at h
  · next h2 =>
    injection h with h
    subst h
    exact h2
  split at h
  · next h3 =>
    injection h with h
    subst h
    exact h3
  split at h
  · next h4 =>
    injection h with h
    subst h
    exact h4
  split at h
  · next h5 =>
    injection h with h
    subst h
    exact h5
  split at h
  · next h7 =>
    injection h with h
    subst h
    exact h7
  exact nomatch h

def ofHandle (k : HandleKind) : Val → Option Nat
  | .handle b n => if b = k.byte then some n else none
  | _ => none

/-- The index of a handle of kind `k`, as the `handle` frame with `k`'s byte. -/
def handleOf (k : HandleKind) : Image Nat where
  toVal n := .handle k.byte n
  ofVal := ofHandle k
  ofVal_toVal n := by
    show (if k.byte = k.byte then some n else none) = some n
    rw [if_pos rfl]
  ofVal_exact := by
    intro v n h
    unfold ofHandle at h
    split at h
    · next b m =>
      split at h
      · next hb =>
        injection h with h
        subst h
        show Val.handle b m = Val.handle k.byte m
        rw [hb]
      · exact nomatch h
    · exact nomatch h

end HandleKind

/-! ## The runtime constructor table -/

/-- The constructor indices the runtime reads at the top of a value, in index order.
`improperCons` (index 4) spelled the tail the old `Machine.Val.exitCons h t` could build with
`t` not a list cell; U1a retired the arm and nothing writes the index, which stays reserved so
`serviceContext` keeps index 5. The matching `improperServiceCons` row (index 6, the old
`Env.Val.ctxCons` with a rest that was no spine) went with U1b's arms. -/
inductive RuntimeCtor
  | exitSuccess
  | exitFailure
  | fiberContext
  | fiberSnapshot
  | improperCons
  | serviceContext
deriving DecidableEq, Repr

/-- The index of a runtime constructor. -/
def RuntimeCtor.index : RuntimeCtor → Nat
  | .exitSuccess => 0
  | .exitFailure => 1
  | .fiberContext => 2
  | .fiberSnapshot => 3
  | .improperCons => 4
  | .serviceContext => 5

/-! ## Spellings

The runtime's shapes over the shared carrier, as definitions a `match` may use
(`@[match_pattern]`): the runtime writes `Value.cell k` in patterns and in terms alike, and
the constructor index or kind byte is written once, here. They are reducible (`abbrev`), so
a `simp` lemma stated on one spelling matches a term written on another or on the raw
constructor, and `Machine/Stores.lean`'s spellings at the old argument types
(`Val.cell (k : RefKey)`) unfold to these. -/

namespace Value

@[match_pattern] abbrev fiber (index : Nat) : Val := .handle 1 index
@[match_pattern] abbrev cell (index : Nat) : Val := .handle 2 index
@[match_pattern] abbrev promise (index : Nat) : Val := .handle 3 index
@[match_pattern] abbrev scope (index : Nat) : Val := .handle 4 index
@[match_pattern] abbrev memoMap (index : Nat) : Val := .handle 5 index
/-- An external resource handle (`HandleKind.external`, byte 7; byte 6 stays reserved): the
index is the allocation's position in the store's table, which records its target spelling. -/
@[match_pattern] abbrev external (index : Nat) : Val := .handle 7 index
/-- `Exit.success value`. -/
@[match_pattern] abbrev exitOk (value : Val) : Val := .ctor 0 [value]
/-- `Exit.failure cause`, the cause already written. -/
@[match_pattern] abbrev exitErr (cause : Val) : Val := .ctor 1 [cause]
/-- rc.112 Result.ts:66: the failure branch in the existing binary sum image. -/
@[match_pattern] abbrev resultFailure (err : Val) : Val := .ctor 0 [err]
/-- rc.112 Result.ts:66: the success branch in the existing binary sum image. -/
@[match_pattern] abbrev resultSuccess (val : Val) : Val := .ctor 1 [val]
/-- The empty list of awaited exits (`fiberAwaitAll`, rc.112 internal/effect.ts:779).
One exit list is one list frame; there is no cons arm. -/
@[match_pattern] abbrev exitNil : Val := .list []
/-- The fiber's cached context (`Machine.Ctx`): the ambient scope as an option of a scope
handle, `MaxOpsBeforeYield`, `PreventSchedulerYield`. -/
@[match_pattern] abbrev fiberContext (ambient budget preventYield : Val) : Val :=
  .ctor 2 [ambient, budget, preventYield]
/-- `awaitAllChildren`'s snapshot of `fiber.children`, a `Set` in rc.112
(`internal/effect.ts:534`, `:703-704`), not an array: the list of fiber handles under its own
index, distinct from a list of exits. -/
@[match_pattern] abbrev fiberSnapshot (fibers : Val) : Val := .ctor 3 [fibers]
/-- A service context (`Env.Val`'s spine, rc.112's `Context` map): the `pair key value`
entries as the constructor's arguments, in binding order. -/
@[match_pattern] abbrev serviceContext (entries : List Val) : Val := .ctor 5 entries

end Value

/-! ## Images of the shared records -/

namespace Value

variable {ε δ ι α : Type}

/-- A fiber identity as a value: the handle. -/
def fiberHandle : Image FiberId :=
  (HandleKind.handleOf .fiber).equiv FiberId.mk FiberId.value (fun _ => rfl) (fun _ => rfl)

/-- A fiber identity recorded in a cause: the structure at the generated rule, `ctor 0 [nat]`.
Not a handle: `Val.keys` does not count an interruptor. -/
def fiberIdentity : Image FiberId :=
  (Image.nat.ctor1 0).equiv FiberId.mk FiberId.value (fun _ => rfl) (fun _ => rfl)

theorem fiberHandle_toVal (id : FiberId) : fiberHandle.toVal id = fiber id.value := rfl

theorem fiberIdentity_toVal (id : FiberId) : fiberIdentity.toVal id = .ctor 0 [.nat id.value] :=
  rfl

theorem fiberIdentity_handleFree : Image.HandleFree fiberIdentity :=
  Image.equiv_handleFree _ _ _ _ _ (Image.ctor1_handleFree _ _ Image.nat_handleFree)

/-- `ReasonAnnotations` (`Machine/Cause.lean`): the entry list under `ctor 0`, the `Prop`
field re-derived by decision on reading. The generator cannot write this instance (a `Prop`
field is not a carrier); the bytes are the ones it would write for the data field. -/
def annotations (A : Image α) : Image (ReasonAnnotations α) :=
  (((Image.list (Image.pair Image.string A)).ctor1 0).subtype
      fun es : List (String × α) => (es.map Prod.fst).Nodup).equiv
    (fun s => ⟨s.val, s.property⟩) (fun r => ⟨r.entries, r.keysNodup⟩)
    (fun _ => rfl) (fun _ => rfl)

theorem annotations_handleFree (A : Image α) (hA : Image.HandleFree A) :
    Image.HandleFree (annotations A) :=
  Image.equiv_handleFree _ _ _ _ _
    (Image.subtype_handleFree _ _
      (Image.ctor1_handleFree _ _
        (Image.list_handleFree _ (Image.pair_handleFree _ _ Image.string_handleFree hA))))

/-- `Reason` at the generated rule: `fail` is `ctor 0 [error, annotations]`, `die` is
`ctor 1 [defect, annotations]`, `interrupt` is `ctor 2 [option interruptor, annotations]`. -/
def toReason (E : Image ε) (D : Image δ) (I : Image ι) (A : Image α) : Reason ε δ ι α → Val
  | .fail e anns => .ctor 0 [E.toVal e, (annotations A).toVal anns]
  | .die d anns => .ctor 1 [D.toVal d, (annotations A).toVal anns]
  | .interrupt who anns => .ctor 2 [(Image.option I).toVal who, (annotations A).toVal anns]

def ofReason (E : Image ε) (D : Image δ) (I : Image ι) (A : Image α) :
    Val → Option (Reason ε δ ι α)
  | .ctor 0 [e, a] =>
    match E.ofVal e, (annotations A).ofVal a with
    | some e, some a => some (.fail e a)
    | _, _ => none
  | .ctor 1 [d, a] =>
    match D.ofVal d, (annotations A).ofVal a with
    | some d, some a => some (.die d a)
    | _, _ => none
  | .ctor 2 [w, a] =>
    match (Image.option I).ofVal w, (annotations A).ofVal a with
    | some w, some a => some (.interrupt w a)
    | _, _ => none
  | _ => none

def reason (E : Image ε) (D : Image δ) (I : Image ι) (A : Image α) : Image (Reason ε δ ι α) where
  toVal := toReason E D I A
  ofVal := ofReason E D I A
  ofVal_toVal r := by
    cases r with
    | fail e anns =>
      show (match E.ofVal (E.toVal e), (annotations A).ofVal ((annotations A).toVal anns) with
        | some e, some a => some (Reason.fail e a)
        | _, _ => none) = some (.fail e anns)
      rw [E.ofVal_toVal, (annotations A).ofVal_toVal]
    | die d anns =>
      show (match D.ofVal (D.toVal d), (annotations A).ofVal ((annotations A).toVal anns) with
        | some d, some a => some (Reason.die d a)
        | _, _ => none) = some (.die d anns)
      rw [D.ofVal_toVal, (annotations A).ofVal_toVal]
    | interrupt who anns =>
      show (match (Image.option I).ofVal ((Image.option I).toVal who),
          (annotations A).ofVal ((annotations A).toVal anns) with
        | some w, some a => some (Reason.interrupt w a)
        | _, _ => none) = some (.interrupt who anns)
      rw [(Image.option I).ofVal_toVal, (annotations A).ofVal_toVal]
  ofVal_exact := by
    intro v r h
    unfold ofReason at h
    split at h
    · next e a =>
      split at h
      · next e' a' he ha =>
        injection h with h
        subst h
        show Val.ctor 0 [e, a] = Val.ctor 0 [E.toVal e', (annotations A).toVal a']
        rw [E.ofVal_exact he, (annotations A).ofVal_exact ha]
      · exact nomatch h
    · next d a =>
      split at h
      · next d' a' hd ha =>
        injection h with h
        subst h
        show Val.ctor 1 [d, a] = Val.ctor 1 [D.toVal d', (annotations A).toVal a']
        rw [D.ofVal_exact hd, (annotations A).ofVal_exact ha]
      · exact nomatch h
    · next w a =>
      split at h
      · next w' a' hw ha =>
        injection h with h
        subst h
        show Val.ctor 2 [w, a] = Val.ctor 2 [(Image.option I).toVal w', (annotations A).toVal a']
        rw [(Image.option I).ofVal_exact hw, (annotations A).ofVal_exact ha]
      · exact nomatch h
    · exact nomatch h

theorem reason_handleFree (E : Image ε) (D : Image δ) (I : Image ι) (A : Image α)
    (hE : Image.HandleFree E) (hD : Image.HandleFree D) (hI : Image.HandleFree I)
    (hA : Image.HandleFree A) : Image.HandleFree (reason E D I A) := by
  intro r
  cases r with
  | fail e anns =>
    show (Val.ctor 0 [E.toVal e, (annotations A).toVal anns]).handles = []
    rw [Val.handles, Val.handlesList_cons, Val.handlesList_cons, hE, annotations_handleFree A hA,
      Val.handlesList_nil]
    rfl
  | die d anns =>
    show (Val.ctor 1 [D.toVal d, (annotations A).toVal anns]).handles = []
    rw [Val.handles, Val.handlesList_cons, Val.handlesList_cons, hD, annotations_handleFree A hA,
      Val.handlesList_nil]
    rfl
  | interrupt who anns =>
    show (Val.ctor 2 [(Image.option I).toVal who, (annotations A).toVal anns]).handles = []
    rw [Val.handles, Val.handlesList_cons, Val.handlesList_cons, Image.option_handleFree I hI,
      annotations_handleFree A hA, Val.handlesList_nil]
    rfl

/-- `Cause` (`Machine/Cause.lean`, one field): the reason list under `ctor 0`. -/
def cause (E : Image ε) (D : Image δ) (I : Image ι) (A : Image α) : Image (Cause ε δ ι α) :=
  ((Image.list (reason E D I A)).ctor1 0).equiv (fun rs => ⟨rs⟩) Cause.reasons
    (fun _ => rfl) (fun _ => rfl)

theorem cause_handleFree (E : Image ε) (D : Image δ) (I : Image ι) (A : Image α)
    (hE : Image.HandleFree E) (hD : Image.HandleFree D) (hI : Image.HandleFree I)
    (hA : Image.HandleFree A) : Image.HandleFree (cause E D I A) :=
  Image.equiv_handleFree _ _ _ _ _
    (Image.ctor1_handleFree _ _ (Image.list_handleFree _ (reason_handleFree E D I A hE hD hI hA)))

/-- `Exit` (`Machine/Exit.lean`) at the generated rule: `success` is `ctor 0 [value]`,
`failure` is `ctor 1 [cause]` — `Value.exitOk` and `Value.exitErr`. -/
def toExit {β : Type} (B : Image β) (C : Image (Cause ε δ ι α)) : Exit β ε δ ι α → Val
  | .success v => .ctor 0 [B.toVal v]
  | .failure c => .ctor 1 [C.toVal c]

def ofExit {β : Type} (B : Image β) (C : Image (Cause ε δ ι α)) : Val → Option (Exit β ε δ ι α)
  | .ctor 0 [v] => (B.ofVal v).map .success
  | .ctor 1 [c] => (C.ofVal c).map .failure
  | _ => none

def exit {β : Type} (B : Image β) (C : Image (Cause ε δ ι α)) : Image (Exit β ε δ ι α) where
  toVal := toExit B C
  ofVal := ofExit B C
  ofVal_toVal e := by
    cases e with
    | success v =>
      show (B.ofVal (B.toVal v)).map Exit.success = some (.success v)
      rw [B.ofVal_toVal, Option.map_some]
    | failure c =>
      show (C.ofVal (C.toVal c)).map Exit.failure = some (.failure c)
      rw [C.ofVal_toVal, Option.map_some]
  ofVal_exact := by
    intro v e h
    unfold ofExit at h
    split at h
    · next w =>
      obtain ⟨x, hx, hj⟩ := Image.map_eq_some_inv h
      subst hj
      show Val.ctor 0 [w] = Val.ctor 0 [B.toVal x]
      rw [B.ofVal_exact hx]
    · next w =>
      obtain ⟨x, hx, hj⟩ := Image.map_eq_some_inv h
      subst hj
      show Val.ctor 1 [w] = Val.ctor 1 [C.toVal x]
      rw [C.ofVal_exact hx]
    · exact nomatch h

end Value

/-! ## Receipts -/

#guard RuntimeCtor.exitSuccess.index = 0
#guard RuntimeCtor.exitFailure.index = 1
#guard RuntimeCtor.fiberContext.index = 2
#guard RuntimeCtor.fiberSnapshot.index = 3
#guard RuntimeCtor.improperCons.index = 4
#guard RuntimeCtor.serviceContext.index = 5
#guard HandleKind.fiber.byte = 1
#guard HandleKind.memoMap.byte = 5
#guard HandleKind.ofByte? 6 = none
#guard HandleKind.ofByte? 0 = none
#guard (Value.fiber 3).handles = [(1, 3)]
#guard (Value.exitOk (Value.cell 2)).handles = [(2, 2)]
#guard Value.fiberHandle.toVal ⟨7⟩ = Value.fiber 7
#guard Value.fiberIdentity.toVal ⟨7⟩ = .ctor 0 [.nat 7]
#guard Value.fiberHandle.ofVal (Value.fiber 7) = some ⟨7⟩
#guard Value.fiberHandle.ofVal (Value.cell 7) = none
#guard Value.fiberIdentity.ofVal (Value.fiber 7) = none

#print axioms HandleKind.ofByte?_exact
#print axioms HandleKind.handleOf
#print axioms Value.fiberHandle
#print axioms Value.fiberIdentity
#print axioms Value.annotations
#print axioms Value.reason
#print axioms Value.cause
#print axioms Value.exit
#print axioms Value.cause_handleFree

end Effect4.Machine
