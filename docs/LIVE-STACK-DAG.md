# Live-stack assurance graph

This graph owns the additive live-stack traversal and its guarded connection
to the existing frame machine. The independent contract is
`test/contracts/live-stack.contract.md`. It does not own the underlying
primitive, fiber, cause, event or result types and does not replace any old
frame declaration or theorem.

## Authored declaration and existing-type record

All eight new declarations belong to `Effect4/Runtime/LiveStack.lean`, have
native origin in the new contract, and use the `derived` relationship to
`Effect4.FrameFiber` and its canonical hooks. Their disposition is
`derivedExpansion` within the existing separate frame calculus. They are not
copied TypeScript or Foldlab declarations. Their assurance route is the one
graph `LIVE-STACK-PG`; there is no new leaf or type requiring another owner.

| Stable public declaration | Role and related canonical declaration | Graph node |
| --- | --- | --- |
| `Effect4.FrameFiber.popLive` | Live-stack implementation of `FrameFiber.popFrom` over the existing `FrameFiber` and `FramePop`. | `LIVE-POP` |
| `Effect4.FrameFiber.getContLive` | Derived deferred-first entry over `popLive`; deliberately differs from the old fused entry on deferred states. | `LIVE-ENTRY` |
| `Effect4.FrameFiber.popLive_eq_popFrom` | Whole-result compatibility for every existing primitive, arm and skip flag. | `LIVE-LEGACY` |
| `Effect4.FrameFiber.getContLive_eq_getCont` | Whole-result entry compatibility under `deferredInterrupt=false`. | `LIVE-LEGACY` |
| `Effect4.FrameFiber.getContLive_false_eq_getCont` | Whole-result false-skip compatibility without a state restriction. | `LIVE-LEGACY` |
| `Effect4.FrameFiber.getContLive_deferred_kept` | Exact retained deferred answer, event and state. | `LIVE-DEFERRED` |
| `Effect4.FrameFiber.getContLive_deferred_discarded` | Exact discarded deferred event followed by the live pop. | `LIVE-DEFERRED` |
| `Effect4.FrameFiber.getContLive_while` | The inner-call/outer-loop equation with complete chronological observations. | `LIVE-WHILE` |

| Reused type | Existing owner and unchanged role | Duplicate prevention |
| --- | --- | --- |
| `Effect4.Prim` | `Runtime/Runtime.lean`; the current fourteen-constructor primitive syntax. | No constructor extension, substitute opcode alphabet or erased control carrier. |
| `Effect4.FrameFiber` | `Runtime/Runtime.lean`; the five-field single-fiber state. | All input and output states use this exact type. |
| `Effect4.FramePop` | `Runtime/Runtime.lean`; answer, popped frames, events and returned fiber. | Both entries return this exact type; no result-only replacement. |
| `Effect4.ContAnswer` | `Runtime/Runtime.lean`; deferred, replacement, selected frame or empty. | No new answer shape or collapsed frame identity. |
| `Effect4.FrameEvent` | `Runtime/Runtime.lean`; chronological stack events. | Deferred events remain visible even when their answer is discarded. |
| `Effect4.Arm` | `Runtime/Runtime.lean`; the three slot names. | Every model arm remains in the theorem domain; source calls use the demandable pair. |
| `Effect4.Cause`, `Effect4.Reason`, `Effect4.ReasonAnnotations` | `Semantics/Cause.lean`; ordered reasons with per-reason annotation maps. | No cause normalization, set conversion, annotation erasure or new cause type. |

The module exports no authored declaration beyond the eight listed names.
Private helpers do not acquire an independent semantic owner. Compiler-created
companions must be enumerated by the implementation's declaration receipt,
not mistaken for extra authored API or omitted from the trust inspection.

## Proof route

The current `Prim.ensure`, `Prim.answerOf` and `Prim.passEvents` are inputs to
`LIVE-POP`. A private continuation-decrease argument establishes totality on
the actual post-hook stack. `LIVE-LEGACY` compares the full result with the
old detached traversal. `LIVE-ENTRY` adds deferred-first control;
`LIVE-DEFERRED` preserves the first event; `LIVE-WHILE` proves the relation
between one inner call and the conditional outer loop. Independent payload
and checkpoint witnesses constrain every node. The host prefix regression is
evidence at the source boundary, not a substitute for any Lean edge.

## Edge ledger

All required edges are open at breaker freeze. The builder's evidence report
may close only the named evidence it actually supplies; the frozen contract
and this graph are not rewritten to fit the implementation.

| Edge | State | Closure requirement |
| --- | --- | --- |
| identity | `required-open` | The eight exact declaration ascriptions, unique module ownership and unchanged canonical-owner hashes. |
| construction | `not-applicable` | No new type, constructor, admission judgment or first-order representation is introduced. Totality is a laws obligation. |
| semantics | `required-open` | Live post-hook traversal, post-hook interruption tests, deferred-first entry and full chronological observations. Executable dependency checks must exclude calls to the old traversal, including helper/fallback routes. |
| laws | `required-open` | All six public theorem statements, the private termination argument and the independent payload-sensitive targets. |
| representation | `not-applicable` | There is no encoding, decoding, erasure or alternate representation; every result uses the canonical carriers unchanged. |
| counterexamples | `required-open` | `E4-RUN-CE-022` through `024`, accepted controls, compiled semantic negatives and restored controls. The AsyncFinalizer witness remains explicitly outside the current primitive theorem domain. |
| bridges | `required-open` | Exact internal compatibility and the source-loop equation are local receipts. A universal relation to actual JavaScript executions, source-state reachability, scheduler state and executing finalizers remains required-open. |
| targets | `required-open` | Pinned, directly typechecked public Effect prefix witnesses and isolated runtime mutations. No generated-code theorem or compiler correctness is claimed. |
| trust | `required-open` | Axiom receipts for both functions and all six public theorems, independent test receipts, the relevant repository trust gate and independent review. No new trust exemption. |
| coverage | `required-open` | Exact authored/module declaration census, root imports, nonempty test discovery and unchanged old packet. No runtime percentage or old coverage row is changed by this graph. |

## Explicit open boundaries

`getContLive_eq_getCont` is guarded because the old entry can discard a
deferred answer in a masked state and does not retain its deferred event.
The false-skip theorem is unrestricted. The source's while-loop order is a
model obligation; it does not prove that every representable deferred state
is reachable through public Effect programs.

`FRAME-FB-ASYNC-FINALIZER` remains open. The current profile's proof that every
continuing pop decreases stack length cannot be carried unchanged into a
constructor that pushes without answering. The later extension must revisit
the measure, frame-arm census, interpretation, execution and source relation.
Its source prefix witness must remain executable after that extension.

`FRAME-FB-FINALIZER-EFFECT`, `FRAME-FB-NONNULL`, the raw-fiber and host-error
boundaries, cause stack annotations and the scheduler/mask-carrier connection
remain unchanged. Neither this graph nor a passing host regression closes
those edges. The existing `FrameFiber.getCont`, `resumeCause`, `step` and
`run` remain the default runtime path.

## Verification route

Run the narrow new contract, axiom report and counterexample module, then the
unchanged frame battery and the default package build. The builder's
`scripts/check-live-stack.mjs` and `scripts/test-live-stack-mutations.mjs`
must retain exact command results, source/tool identities, controls and
semantic-rejection results. The new register rows change an existing
fiber-assurance input digest; regenerating that separately owned projection
is not part of the breaker fence.
