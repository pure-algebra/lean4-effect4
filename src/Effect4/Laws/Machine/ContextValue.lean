import Effect4.Machine.Context

/-!
# Machine.ContextValue — the Layer machine's value alphabet on the shared carrier

Owner: the `Image` of `Env.Val` — the identity, since U1b made `Env.Val` the shared carrier
`Effect4.Store.Val` (`Machine/Context.lean`) — the exit carrier built on it, and the receipts
of the alphabet at the table of `Machine/Value.lean`
(`docs/research/2026-09-07-u0-value-foundation.md`, `2026-09-07-u1-cutover-dispatch.md` U1b).

## The table

| `Env.Val` | `Store.Val` |
| --- | --- |
| `unit`, `nat n`, `bool b` | the carrier's own |
| `fiber ⟨id⟩` / `fibers ids` | `Value.fiber` / `Value.fiberSnapshot` |
| `scopeHandle s`, `memoMap id`, `promise cell` | `Value.scope`, `Value.memoMap`, `Value.promise` (`handle 4/5/3`) |
| `pair a b` | the carrier's `pair` |
| `exitOk v`, `exitErr c`, `exitNil` | `ctor 0`, `ctor 1` over `causeImage`, `list []` |
| a service context | `Value.serviceContext [pair key value, …]` (`ctor 5`, `encode`/`decode`) |

A service context is rc.112's `Context` map (`Context.ts`), keyed by `ServiceKey` at the
generated rule (`Machine/Key.lean`). It is distinct from the frame machine's cached `Ctx`
(`Value.fiberContext`, `ctor 2`); the join makes the one carry the other
(`docs/research/2026-09-07-join-dispatch.md` §2).
-/

set_option autoImplicit false

namespace Effect4.Machine.Env

open Effect4.Store (Image)

/-- The Layer machine's value alphabet as an image of the shared carrier: the identity. -/
def Val.image : Image Val := ⟨id, some, fun _ => rfl, fun h => Option.some.inj h⟩

/-- A written context spine reads back as its entries: `Context.lean`'s `spine_encodeEntries`
at a context, the statement `decode_encode` rests on. -/
theorem Val.ofSpine_entries (c : Ctx) : spine (encode c) = some c.entries :=
  spine_encodeEntries c.entries

/-- The exit carrier at this instantiation. -/
def exitImage : Image ExitV := Value.exit Val.image causeImage

/-! ## Receipts -/

/-- The key `{1, 2}` written. -/
private def key12 : Store.Val := .ctor 0 [.ctor 0 [.nat 1], .ctor 0 [.nat 2]]

#guard encode (Context.empty : Ctx) = Value.serviceContext []
#guard encode ((Context.empty : Ctx).addV ⟨⟨1⟩, ⟨2⟩⟩ (.nat 7)) =
  Value.serviceContext [.pair key12 (.nat 7)]
#guard decode (Value.serviceContext [.pair key12 (.nat 7)]) =
  some ((Context.empty : Ctx).addV ⟨⟨1⟩, ⟨2⟩⟩ (.nat 7))
#guard decode (Value.serviceContext [.nat 7]) = none
#guard decode (Value.serviceContext [.pair (.nat 1) (.nat 7)]) = none
-- a spine binding one key twice is no context
#guard decode (Value.serviceContext [.pair key12 (.nat 7), .pair key12 (.nat 8)]) = none
#guard decode (Value.fiberContext (.none) (.nat 2048) (.bool false)) = none
#guard Val.memoMap 3 = Value.memoMap 3
#guard Val.promise 1 = Value.promise 1
#guard (Val.pair (Val.promise 1) (Val.memoMap 2)).handles = [(3, 1), (5, 2)]
#guard (Val.exitErr (Cause.die (Defect.serviceNotFound ⟨⟨1⟩, ⟨2⟩⟩))).handles = []
#guard exitImage.ofVal (Val.exitErr (Cause.fail (Err.tag 3))) =
  some (Exit.failure (Cause.fail (Err.tag 3)))

#print axioms Err.image
#print axioms Defect.image
#print axioms serviceKeyImage
#print axioms causeImage
#print axioms Val.image
#print axioms Val.ofSpine_entries
#print axioms exitImage
#print axioms decode_encode

end Effect4.Machine.Env
