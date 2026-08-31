import Cas.Values.Json

/-!
# The lift taxonomy — refusal codes and the spectrum

The first-order data of the effect-lift lane (the read face of the
store language): the closed v0 refusal taxonomy, its wire spellings,
and the spectrum rollup that grades every refusal by the computation
class the offending form would need (applicative gap / selective /
monadic / instrument / classification).

This module is the authoring surface the TypeScript contract mirrors
(interchange law R11: one manifest, both surfaces generated). Totality
of `spectrum` is by construction — it is a function on an inductive,
not a partial map — which is precisely the statement the mirrored
TypeScript `Record` cannot make for itself.

Deviation, held (differential-testing spec): `branch` maps to
`monadic` because v0 does not attempt the arms; nothing lands in
`selective` until arms are attempted.
-/

namespace Cas.Lift

/-- The closed v0 refusal taxonomy. Wire spellings in
`RefusalCode.wire`; the closed set grows only by manifest revision.

Every per-constructor example below elides the standard candidate
frame — the fragment shown replaces the corresponding piece of:

```ts
import * as E from "effect";
export const p = (store: S) => E.gen(function* () {
  const a = yield* store.put({
    kind: { version: 0, tag: 71 }, payload: hex("ff"), refs: [] });
  return [a];
});
```
-/
inductive RefusalCode where
  /-- The arrow takes anything but exactly one plain store parameter:
  ```ts
  export const p = (store, log) => E.gen(function* () { /* … */ })
  ```
  -/
  | paramShape
  /-- The spine escapes the recognized form — block-bodied arrow, body
  not a call, callee not import-resolved `Effect.gen`, or the `gen`
  argument not a generator function:
  ```ts
  export const p = (store) => { return E.gen(function* () { /* … */ }) }
  ```
  -/
  | spineEscape
  /-- A yield outside the one recognized position (the binding), or a
  `yield*` of a non-call:
  ```ts
  yield* store.put({ /* … */ });   // bare statement, answer discarded
  ```
  -/
  | yieldPosition
  /-- The binder is not a single plain identifier:
  ```ts
  const { id } = yield* store.put({ /* … */ });
  ```
  -/
  | bindShape
  /-- A statement outside the recognized shapes — binding without
  `yield*`, multiple declarators, a return before final position, an
  optional-chained spine (ruling R2), or any foreign statement kind:
  ```ts
  const a = store.put({ /* … */ });   // no yield*
  const b = yield* store?.put({ /* … */ });   // optional chain
  ```
  -/
  | stmtShape
  /-- The operation's receiver is not the bound store parameter:
  ```ts
  const a = yield* other.put({ /* … */ });
  ```
  -/
  | opReceiver
  /-- The member is not a documented signature operation (`get`, a
  not-yet-documented `load`, or any import-resolved non-store op):
  ```ts
  const a = yield* store.get(addr);
  ```
  -/
  | opUnknown
  /-- A branch in statement position — v0 does not attempt the arms
  (spectrum deviation: graded `monadic`, not `selective`):
  ```ts
  if (flag) { /* … */ }
  ```
  -/
  | branch
  /-- A loop in the body:
  ```ts
  for (const n of nodes) { /* … */ }
  ```
  -/
  | loop
  /-- A handler in the body:
  ```ts
  try { /* … */ } catch (e) { /* … */ }
  ```
  -/
  | handler
  /-- The return is not the dense array of the binders, in order:
  ```ts
  return a;   // must be: return [a];
  ```
  (A body with no return at all lands here too.)
  -/
  | returnShape
  /-- The `put` argument is not the closed `{ kind, payload, refs }`
  object-literal shape, or a nested piece breaks it:
  ```ts
  const a = yield* store.put(node);   // not an object literal
  ```
  -/
  | nodeShape
  /-- A value in literal position is not the pinned literal form —
  non-literal or non-canonical nat (R6), template or non-hex payload
  (R1/R7), computed refs:
  ```ts
  payload: hex(data)   // must be: hex("ff") — plain, lowercase, even
  ```
  -/
  | argDynamic
  /-- A function-valued operation argument:
  ```ts
  const a = yield* store.put(() => node);
  ```
  -/
  | argClosure
  /-- A ref names no earlier binder:
  ```ts
  refs: [{ id: phantom, expectedTag: 71 }]
  ```
  -/
  | refUnbound
  /-- Declared unreachable in v0 (ruling R9): a ref to a binder
  declared LATER in the body also lands in `refUnbound`, because v0
  resolves refs against earlier binders only. Revival: the two-pass
  binder walk.
  ```ts
  const a = yield* store.put({ /* … */ refs: [{ id: b, expectedTag: 71 }] });
  const b = yield* store.put({ /* … */ });
  ```
  -/
  | refForward
  /-- An earlier answer used as an operation receiver:
  ```ts
  const b = yield* a.put({ /* … */ });   // a is a previous binder
  ```
  -/
  | answerHigherOrder
  /-- A fail-shaped `yield*` in return position — failure is not yet
  documented in the v0 language:
  ```ts
  return yield* store.put({ /* … */ });
  ```
  -/
  | failNotDocumented
  /-- Declared unreachable in v0 (ruling R9): a binding form import
  resolution cannot see — v0 admits every effect-module binding form
  alike, so nothing classifies here yet. Revival: import-form rules.
  ```ts
  const E = await import("effect");
  ```
  -/
  | importOpaque
  /-- Declared unreachable in v0 (ruling R9): Rule 7 (hex pinning) is
  disabled, so an unpinned in-file `hex` helper marks the Lift with
  `helperUnpinned: true` instead of refusing. Revival: Rule 7 landing.
  ```ts
  const hex = (s: string) => myDecoder(s);   // unpinned helper
  ```
  -/
  | helperUnpinned
  deriving DecidableEq

/-- The wire spelling (recognition proposal §8, codes verbatim). -/
def RefusalCode.wire : RefusalCode → String
  | .paramShape => "E-PARAM-SHAPE"
  | .spineEscape => "E-SPINE-ESCAPE"
  | .yieldPosition => "E-YIELD-POSITION"
  | .bindShape => "E-BIND-SHAPE"
  | .stmtShape => "E-STMT-SHAPE"
  | .opReceiver => "E-OP-RECEIVER"
  | .opUnknown => "E-OP-UNKNOWN"
  | .branch => "E-BRANCH"
  | .loop => "E-LOOP"
  | .handler => "E-HANDLER"
  | .returnShape => "E-RETURN-SHAPE"
  | .nodeShape => "E-NODE-SHAPE"
  | .argDynamic => "E-ARG-DYNAMIC"
  | .argClosure => "E-ARG-CLOSURE"
  | .refUnbound => "E-REF-UNBOUND"
  | .refForward => "E-REF-FORWARD"
  | .answerHigherOrder => "E-ANSWER-HIGHER-ORDER"
  | .failNotDocumented => "E-FAIL-NOT-DOCUMENTED"
  | .importOpaque => "E-IMPORT-OPAQUE"
  | .helperUnpinned => "E-HELPER-UNPINNED"

/-- Every code, in taxonomy order. -/
def RefusalCode.all : List RefusalCode :=
  [.paramShape, .spineEscape, .yieldPosition, .bindShape, .stmtShape,
   .opReceiver, .opUnknown, .branch, .loop, .handler, .returnShape,
   .nodeShape, .argDynamic, .argClosure, .refUnbound, .refForward,
   .answerHigherOrder, .failNotDocumented, .importOpaque,
   .helperUnpinned]

theorem RefusalCode.all_complete (c : RefusalCode) : c ∈ RefusalCode.all := by
  cases c <;> decide

-- Wire spellings collide with nothing: injectivity of the wire on
-- the taxonomy, checked at elaboration time.
#guard decide ((RefusalCode.all.map RefusalCode.wire).Nodup)

/-- The spectrum: which computation class the refused form would need. -/
inductive SpectrumClass where
  | applicativeGap | selective | monadic | instrument | classification
  deriving DecidableEq

def SpectrumClass.wire : SpectrumClass → String
  | .applicativeGap => "applicative-gap"
  | .selective => "selective"
  | .monadic => "monadic"
  | .instrument => "instrument"
  | .classification => "classification"

/-- The spectrum rollup — total by construction. -/
def spectrum : RefusalCode → SpectrumClass
  | .bindShape => .applicativeGap
  | .branch => .monadic
  | .loop => .monadic
  | .handler => .monadic
  | .argClosure => .monadic
  | .answerHigherOrder => .monadic
  | .spineEscape => .monadic
  | .yieldPosition => .monadic
  | .failNotDocumented => .classification
  | .opReceiver => .classification
  | .opUnknown => .classification
  | .stmtShape => .classification
  | .returnShape => .classification
  | .nodeShape => .classification
  | .argDynamic => .classification
  | .refUnbound => .classification
  | .refForward => .classification
  | .paramShape => .classification
  | .importOpaque => .instrument
  | .helperUnpinned => .instrument

end Cas.Lift
