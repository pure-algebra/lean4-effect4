# Effect runtime ground-truth extraction scope

Status: pinned-source breadth scoping report  
Research snapshot: 2026-08-24  
Source gate: G0 (source snapshot identified; no runtime-conformance or Lean claim)

## Scope and evidence boundary

This report scopes an extraction/modeling effort against Effect commit
`0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07`, package `effect` version
`4.0.0-rc.111` (the repository identity and revision recorded in
[`sources.lock.json`](../../.reference/provenance/sources.lock.json)).
The repository owner is [Effect-TS/effect](https://github.com/Effect-TS/effect).
All Effect source links below use that commit, so those implementation links
are immutable primary-source links. Runtime-core file identities should be
added to the source lock before a formal or conformance claim depends on them.

Implementation facts describe what the TypeScript source does. “Model choice”
means a proposed Foldlab abstraction and is not a claim about Effect. Nothing
here claims JavaScript-host, compiler, whole-library, performance, or semantic
preservation conformance. The charter explicitly defers fibers, interruption,
scheduling, resources, and service environments until separately modeled
([`CHARTER.md`](../../CHARTER.md)).

## Scoping result

A conditionally proved model is feasible, but “extract the Effect runtime” must
not mean serializing arbitrary runtime values or copying every internal object
shape into Lean. The pinned runtime is an open evaluator protocol implemented by
JavaScript objects and closures. A defensible bootstrap therefore needs four
separate artifacts:

```text
pinned Effect implementation facts
        |
        v
accepted source/descriptor subset --rejections--> unsupported source
        |
        v
Foldlab-owned typed Effect Core
        |                         \
        v                          v
direct denotation          continuation machine
        \                         /
         +-- proved equivalence --+
                    |
                    v
generated Effect programs + differential runtime evidence
```

The first material vertical slice should cover the runtime's success and
failure continuation discipline, not concurrency:

- `succeed` and a restricted typed `fail`;
- `flatMap` / the `OnSuccess` frame;
- `catchCause` restricted to a single typed-failure reason / the `OnFailure`
  frame;
- terminal `Exit.Success` and `Exit.Failure`;
- named, first-order, total callbacks over a closed value language; and
- final-`Exit` observation only.

This slice is enough to prove that a direct algebraic semantics and a
defunctionalized stack machine agree. It is not enough to prove that arbitrary
`Effect<A, E, R>` values, JavaScript closures, custom `Effectable` instances, or
the hosted runtime conform. Those are separate accepted-source and conformance
bridges.

### What “ground truth” should mean

| Layer | Ground-truth authority | Output | Licensed conclusion |
|---|---|---|---|
| Source identity | `.reference/provenance/sources.lock.json`, Git commit, package metadata, file hashes | source snapshot manifest | exact implementation revision is known |
| Implementation inventory | TypeScript compiler AST/symbol analysis plus pinned source review | primitive/symbol inventory and source ledger | named implementation paths and shapes are known |
| Formal meaning | Foldlab-owned syntax, typing, denotation, machine, and observations | Lean definitions and theorems | laws hold for the model under stated assumptions |
| Runtime relation | generated fixtures, raw observations, normalized traces, named runtime/compiler | conformance evidence | the pinned implementation agrees on the stated tested domain |

Static extraction can automate provenance, inventory, rejection, and fixture
generation. It cannot infer the meaning of arbitrary JavaScript callbacks or
turn tests into a preservation theorem.

## Runtime path (implementation facts)

### Public surface to primitives

The public module exports `succeed`, `sync`, `fail`, `failCause`, `yieldNow`,
`flatMap`, `catchCause`, `fork*`, `scoped`, and `acquireRelease`; these are
delegated to internal implementations in the public source:

- [`Effect.ts` constructors and aliases](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Effect.ts#L969-L1010),
  [`sync`/`yieldNow`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Effect.ts#L1170-L1175),
  [`fail` and `failCause`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Effect.ts#L1507-L1575),
  [`flatMap`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Effect.ts#L2001-L2030),
  and [`fork/scoped/acquireRelease` exports](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Effect.ts#L6466-L6595).
- `makePrimitiveProto` installs an operation identifier plus `evaluate`,
  success/failure continuations, and an optional `contAll` hook; `makePrimitive`
  creates object instances whose arguments live under a private symbol
  ([`internal/core.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/core.ts#L388-L459)).
- `flatMap` creates an `OnSuccess` primitive. Its evaluator pushes itself onto
  the fiber stack and returns the left operand; `catchCause` does the analogous
  `OnFailure` operation ([`internal/effect.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L1662-L1689),
  [failure handler](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L2474-L2501)).

### The runtime protocol is open, not an opcode enum

The public `Effect<A, E, R>` interface carries covariant phantom parameters,
but those parameters are erased at execution. Runtime effects are objects with
symbol-named fields for an identifier, arguments, evaluator, success
continuation, failure continuation, and ensure/finalizer continuation
([`internal/core.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/core.ts#L31-L63),
[`Primitive`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/core.ts#L365-L459)).

This protocol is intentionally extensible. Public
[`Effectable.Prototype`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Effectable.ts#L16-L49)
accepts a caller-defined label and evaluator with access to the current fiber;
`Effectable.Class` exposes the class-based route. Context service keys and
`Exit` values are also Effects. The evaluator loop dispatches through the
private evaluator symbol rather than matching a closed tag union.

Consequences:

1. an inventory of built-in `op` strings is useful provenance, not a complete
   runtime grammar;
2. structural assignability or `Effect.isEffect` is not an accepted-source
   proof;
3. a source extractor must resolve the exact constructor/combinator symbol and
   recursively classify operands, callbacks, and captures;
4. custom `Effectable` instances must be rejected, represented as opaque
   external operations, or admitted through a separately trusted semantic
   plugin; and
5. diagnostic `toJSON()` output cannot reconstruct evaluators or closures.

The built-in protocol inventory for this pin includes at least:

| Runtime role | Built-in identifiers / protocol paths | Initial status |
|---|---|---|
| Terminal dispatch | `Success`, `Failure` | admit restricted forms |
| Sequential frames | `OnSuccess`, `OnFailure`, `OnSuccessAndFailure`, `OnExit` | first two initially; defer the rest |
| Deferred computation | `Sync`, `Suspend`, `Iterator`, `While` | reject initially; admit under separate callback/termination rules |
| Fiber access/state | `WithFiber`, `SetInterruptible`, `Exit` capture | defer |
| Suspension/concurrency | `Yield`, `Async`, `AsyncFinalizer` | defer |
| Open extension | arbitrary `Effectable` label/evaluator | reject or semantic plugin |

Eager combinators are another separate path. For example, `flatMapEager` can
invoke its callback while constructing a combinator when its input is already
an `Exit`; ordinary `flatMap` installs an `OnSuccess` frame for execution
([`flatMapEager`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L1728-L1750)).
The first core must exclude eager variants rather than silently identify their
construction-time behavior with runtime evaluation.

### Fiber evaluation and continuations

`FiberImpl` owns a numeric id, context, operation counter, interruptibility,
mutable primitive stack, observers, optional exit, child set, pending interrupt
cause, yielded value/callback, and run-state flags
([`internal/effect.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L505-L555)).
`evaluate` invokes `runLoop`; on a terminal `Exit` it records metrics, notifies
observers, clears stack/children, and empties context
([same file](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L599-L628)).

The loop installs the current fiber globally, checks deferred interruption,
increments the operation count, asks the scheduler whether to yield, evaluates
the current primitive (or tracer context wrapper), and handles `Yield`. A
yielded `Exit` returns immediately; a yielded callback may be resumed, including
when an interrupt became pending ([`runLoop`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L629-L679)).
`getCont` pops frames, gives each `contAll` a chance to install/transform a
continuation, and then selects `contA` or `contE`; a deferred interrupt has a
synthetic continuation ([`getCont`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L680-L743)).
Thus “continuation” is an object protocol plus mutable stack, not a serializable
AST or a JS call-stack theorem.

`Exit.Success` and `Exit.Failure` are themselves effect primitives. Success
looks up `contA`; failure annotates a current stack frame, skips failure
continuations while an interrupt is pending and interruptible, then invokes
`contE` or yields the exit ([`internal/core.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/core.ts#L508-L553)).

### Cause and Exit

Public `Cause` exposes empty, typed failure, defect, interrupt, and combination
operations ([`Cause.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Cause.ts#L75-L90),
[constructors](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Cause.ts#L458-L530),
[combine](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Cause.ts#L692-L730)).
Internal causes are represented by a `CauseImpl` containing reason objects
([`internal/core.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/core.ts#L138-L176));
`Exit` wraps success or a cause and is the terminal/intermediate carrier
([reason constructors](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/core.ts#L278-L322),
[Exit constructors](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Exit.ts#L73-L170)).
Typed failure, defect, and interruption are therefore distinct source cases;
the fact that a cause arose during finalization additionally affects how it is
combined with the primary exit. Collapsing these to one `Result` error loses
behavior.

For this revision, `CauseImpl` is a flat `ReadonlyArray` of `Fail`, `Die`, and
`Interrupt` reasons. [`causeCombine`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L242-L260)
uses array union/deduplication; it is not the sequential/parallel cause tree
used by some earlier Effect presentations.
“Finalizer failure” is also not a fourth reason constructor: a finalizer can
produce an ordinary typed failure, defect, or interrupt whose cause is combined
with the primary cause. The model must specify the flat reason equivalence,
deduplication, annotations, and any ordering observation rather than importing
an older cause algebra.

### Context and service lookup

`Context` exposes a string-keyed service map. Internally it uses a base map plus
an overlay chain, flattening after depth/base-hit thresholds; lookup walks
overlays and can retain a shared cache root
([`Context.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Context.ts#L467-L547)).
`FiberImpl.setContext` refreshes cached scheduler, tracer, logging, stack-frame,
yield-limit, and metrics fields when the cache root changes
([`setContext`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L709-L731)).
Context values are persistent structures; the fiber holds a mutable reference
to a current Context plus derived caches. A faithful service slice must also
decide how to treat string-key collisions and lazy cached defaults supplied by
`Context.Reference`. The initial semantics should use an abstract typed finite
map and defer overlay/cache representation, while recording that correspondence
as a later conformance obligation.

### Async, fork, yield, scheduler, interruption

The scheduler interface supplies execution mode, `shouldYield`, and a task
dispatcher. `MixedScheduler` yields at `currentOpCount >= maxOpsBeforeYield`
and dispatches priority buckets FIFO within a priority via host microtask or
`setImmediate`/timer ([`Scheduler.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Scheduler.ts#L32-L60),
[default implementation](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/Scheduler.ts#L83-L190)).
`forkUnsafe` inherits context and (optionally) interruptibility, evaluates
immediately or schedules a task at priority zero, and links non-daemon children
to the parent ([`internal/effect.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L5263-L5284)).
`yieldWith` stores an `Exit` or callback and returns the singleton `Yield`
marker ([`yieldWith`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L699-L702)).

Interrupt requests combine causes. If interruptible and running, the request is
deferred; otherwise evaluation immediately starts with an interrupt failure.
Uninterruptible regions push a restoring frame, and re-enabling interruption
releases a pending cause ([`interruptUnsafe`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L574-L595),
[masks](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L4294-L4367)).

### Scope and finalization

Scopes transition `Empty -> Open -> Closed`, retain either one optimized
finalizer or a keyed map, and execute finalizers in reverse insertion order.
Closing records the exit before running finalizers; sequential strategy runs
them in the current fiber, while parallel strategy forks daemon fibers and joins
them. Finalizer causes combine with the original failure
([`scopeCloseUnsafe`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L3775-L3827),
[registration/removal](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L3847-L3904)).
`acquireRelease` masks acquisition and registers a release finalizer receiving
the eventual `Exit` ([`acquireRelease`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L3971-L3987)).

### Tracing

Fiber context caches an optional tracer context and current/parent span. During
each loop iteration, a tracer context can wrap the primitive evaluator
([fiber fields](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L540-L550),
[loop hook](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L653-L656)).
Span completion is registered as a scope finalizer and receives the `Exit`, so
tracing observes both success and failure paths ([`internal/effect.ts`](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/internal/effect.ts#L5790-L5815)).

## Recommended formal architecture

The model should deliberately contain two semantics and one external relation.

```text
EffectCore descriptor
   |-- denote ------------> direct Outcome / event-tree semantics
   |
   `-- initialize --------> explicit continuation machine
                                  |
                                  `-- Runs / terminal Exit / trace

machine-direct theorem:     machine and denotation agree
runtime conformance bridge: pinned Effect agrees for declared observations
```

### Fit with the current Foldlab repository

The canonical semantic authorities already live in the Effect TypeScript
[`CONTEXT.md`](../effect-typescript-semantics/CONTEXT.md),
[`CLAIM-GATES.md`](../effect-typescript-semantics/CLAIM-GATES.md), and
[`IMPLEMENTATION-PLAN.md`](../effect-typescript-semantics/IMPLEMENTATION-PLAN.md).
This report is research input to those documents; it does not amend their
vocabulary, select a claim, or ratify a Runtime Core artifact.

The current `formal/` tree does not contain a shared Effect machine,
translation, or Result scaffold. Runtime Core should therefore begin as its own
Lake effort after its carriers and observations are ratified, following the
repository rule of one Lake project per formal effort. Its generic relational
vocabulary—configurations, labels, multi-step runs, refinement, trace
projection, simulation, and adequacy—should be designed for later reuse without
being prematurely promoted into `formal/lib/`.

The source authority is
[`sources.lock.json`](../../.reference/provenance/sources.lock.json), not a
working checkout. The runtime model must retain typed failure separately from
later defect and interruption causes, and the admitted source surface must be
recorded through the repository's provenance context before any G3 claim.

### Core syntax and typing

Use a serializable untyped descriptor at ingestion and validate it into an
indexed Lean syntax. The first typed core can be sketched as:

```text
ValueType  ::= unit | bool | int | text | product ValueType ValueType
PureFn a b ::= named, total first-order expressions over ValueType

Eff A E R ::=
  | succeed    : A -> Eff A E R
  | fail       : E -> Eff A E R
  | flatMap    : Eff A E R -> PureK A B E R -> Eff B E R
  | catchFail  : Eff A E R -> PureK E A E2 R -> Eff A E2 R
```

`PureK` must be syntax or a closed table of named blocks, not an arbitrary Lean
or JavaScript function. This makes well-formed programs enumerable,
serializable, content-addressable, and suitable for code generation. Keep the
success, typed-failure, and service indices even when the first slice fixes
`R = empty`; TypeScript erasure is a later boundary, not a reason to erase the
model.

Start with integers rather than JavaScript `number`, a pinned Unicode/text
policy, and immutable finite products. Admit lists, records, JSON values,
floating point, `undefined`, cyclic objects, identity, and prototypes only after
their encoding and equality observations are frozen.

### Direct semantics

For the terminating first slice:

```text
denote : Eff A E Empty -> ExitPure A E
ExitPure A E := success A | failure E
```

Also define an embedding into the richer runtime-facing carrier:

```text
CausePure E := singleton (Fail E)
embed : ExitPure A E -> Exit A (Cause E)
```

This preserves the distinction between an intentionally restricted first proof
and the pinned runtime's `Fail` / `Die` / `Interrupt` reasons. Defects must enter
as a later syntax/semantics extension, not be silently identified with `E`.

### Continuation machine

The first machine needs only named frames:

```text
Frame ::= onSuccess block | onFailure block
Config ::= evaluating term stack | returning exit stack | terminal exit
```

Operationally, `flatMap` pushes `onSuccess`; `catchFail` pushes `onFailure`;
success pops until a success frame; failure pops until a failure frame. This is
the defunctionalized analogue of the pinned `_stack` / `contA` / `contE`
protocol. A later `ensure` frame can model `contAll` / `OnExit` and interruption
mask restoration.

Required first theorems:

1. validation produces only well-typed descriptors;
2. each machine step preserves configuration well-formedness;
3. the finite machine has progress and terminates;
4. transition and terminal results are deterministic;
5. machine evaluation agrees with `denote`;
6. identity and associativity hold for the declared total callback language;
7. failure does not evaluate a success continuation, and success does not
   evaluate a failure continuation; and
8. normalization/codec round trips preserve denotation.

Once requests or scheduling are visible, replace equality of final outcomes by
a parameterized trace relation. Interaction Trees are a good deterministic
event denotation; Choice Trees or an LTS are appropriate when scheduler or
environment choice becomes nondeterministic. DimSum's independent-machine plus
event-wrapper architecture is the right precedent for relating Lean, Effect
TypeScript, and later Wasm states without asserting one shared heap or runtime.

### Conditional theorem envelope

The first meaningful claim should be stated approximately as follows:

> For every closed, well-typed EffectCore descriptor in the admitted finite
> value and callback language, the defunctionalized continuation machine
> terminates and returns the same final `ExitPure` as the direct denotation.

Its conditions are substantive:

- callbacks are named, total, deterministic, non-throwing, and close only over
  encoded values;
- callbacks return only admitted EffectCore terms;
- no `Effectable`, service lookup, fiber inspection, mutation, reflection,
  identity observation, host API, tracing hook, eager combinator, or unsafe cast
  is admitted;
- the initial failure is a single typed `Fail`, not a defect or interruption;
  and
- divergence, scheduling, allocation, and wall-clock cost are outside the
  observation.

This is a strong G2 theorem about the model. Relating it universally to the
actual JavaScript runtime requires an additional source/runtime semantics or a
verified bridge. Differential fixtures alone support only the stated G3 domain.

## Candidate extraction tiers

| Tier | Candidate slice | Evidence needed | Main risk |
|---|---|---|---|
| T0 | Closed descriptor, named total callbacks, `succeed`/typed `fail` | direct denotation, validation, codec laws | value/callback language is too weak or underspecified |
| T1 | `flatMap`/`catchFail` plus defunctionalized success/failure frames | machine preservation, determinism, machine-direct equivalence | accidentally admitting raw closures, eager variants, defects, or custom Effectables |
| T2 | `Cause` with `Die`/`Interrupt`, `sync`/`suspend`, full cause handlers | exception/defect and cause-collection laws | arbitrary host exceptions and callback behavior |
| T3 | Context service requests and `provide` | environment typing, lookup/provision laws, conformance fixtures | string-key collisions, lazy defaults, mutable services |
| T4 | `OnExit`, interruption masks, sequential scopes/finalizers | exactly-once cleanup, reverse order, cause combination | pending-interrupt timing and cleanup failure precedence |
| T5 | `yieldNow`, callback suspension, deterministic abstract scheduler | scheduler-parameterized traces and resume/cancel invariants | host task order, single-shot callback discipline, fairness |
| T6 | child fibers, fork/await/join/race, parallel finalizers | multi-fiber LTS, refinement, bounded interleaving checks | state explosion and cleanup-sensitive nondeterminism |
| T7 | tracing, metrics, performance/cost | observation projection plus cost semantics | instrumentation changes the runtime path |

Recommended first extraction is T0/T1. T2–T7 should remain separate modules
and claim gates; do not encode scheduler, host timing, or tracing into the pure
core by default.

## Implementation specification catalogue

These specifications should be written before or alongside code. “Required
now” means required for the T0/T1 vertical slice; later specifications can be
stubbed with explicit exclusions.

### Provenance and admission

| ID | Specification | Required content | Timing |
|---|---|---|---|
| `SRC-001` | Source snapshot | repository, commit, package/version/path, origin, file hashes, TypeScript config/compiler, extractor version | now |
| `SRC-002` | Source-symbol ledger | public symbol, resolved internal symbol, declarations, selected overload, imports, spans, hashes, runtime role | now |
| `SRC-003` | Runtime-protocol inventory | primitive symbol fields, built-in identifiers, evaluator/continuation shape, open extension paths | now |
| `ACC-001` | Accepted-source judgment | recursive whitelist, callee identity, operand closure, callback/capture closure, result/rejection type | now |
| `ACC-002` | Rejection taxonomy | stable codes for unknown call, custom Effectable, unsafe cast, mutation, host access, throw, async, service, eager form, unsupported value | now |
| `ACC-003` | Semantic plugin contract | how a future custom primitive can declare syntax, typing, denotation, observations, generator, and proof/conformance evidence | later |

The acceptance judgment should have the shape:

```text
Accept : TSNode -> TypeFacts -> Policy -> Either Rejection Descriptor
```

and must fail closed. An expression's apparent `Effect<A, E, R>` type is not
enough; its declaration symbol, overload, callbacks, captures, yielded
expressions, and provider edges must all be classified.

### Core language and formal semantics

| ID | Specification | Required content | Timing |
|---|---|---|---|
| `VAL-001` | Canonical value universe | constructors, equality, number/text policy, codec, canonical order, size limits | now |
| `FUN-001` | Callback/block language | named operators, typing, captures, totality/termination, evaluation order, no-throw condition | now |
| `TYP-001` | Effect indices | success, typed failure, service signature; well-formedness and closedness judgments | now |
| `COR-001` | Effect Core grammar | `succeed`, `fail`, `flatMap`, restricted catch; constructor and serialization schema | now |
| `CAU-001` | Exit/Cause model | pure single-failure carrier now; later flat reason collection, deduplication, annotations, defect and interrupt | now/later |
| `DEN-001` | Direct denotation | environments, terminal/divergent result, visible operations, evaluation order | now |
| `FRM-001` | Frame grammar | success/failure frames; later ensure, interrupt-restore, async-finalizer, exit-capture frames | now/later |
| `MCH-001` | Machine dynamics | configurations, initial/terminal states, small steps, administrative steps, stuck/defect policy | now |
| `OBS-001` | Observation profiles | final exit, full cause, requests, resources, schedule, tracing/cost; visibility and normalization | now |
| `REL-001` | Equivalence/refinement | equality for deterministic T0/T1; weak bisimulation/trace inclusion for later nondeterminism | now/later |
| `THM-001` | Theorem contract | progress, preservation, termination, determinism, adequacy, simulation, algebraic laws, codec laws | now |

### Extraction, generation, and conformance

| ID | Specification | Required content | Timing |
|---|---|---|---|
| `EXT-001` | TypeScript extractor | pinned `Program`/`TypeChecker`, module resolution, symbol identity, overload/generic facts, callback AST and captures | now |
| `CAN-001` | Canonicalization | schema id, deterministic field/tag order, encoding version, digest domain, normalization laws | now |
| `GEN-001` | Effect program generator | descriptor-to-public-API translation, named callbacks, source map, generated-file ownership | now |
| `FIX-001` | Fixture manifest | case id, descriptor hash, inputs, expected observation, rejection state, source/runtime/tool pins | now |
| `TRC-001` | Raw trace | lossless runner events, terminal exit, runtime metadata; no proof claim | now |
| `TRC-002` | Normalized observation | canonical fiber names, hidden host ids/timestamps, declared event projection, normalization version | now/later |
| `HAR-001` | Runtime runner | public root import, deterministic scheduler option, completion observer, timeout/resource controls | now |
| `ADP-001` | Internal observation adapter | optional pin-coupled test build, events exposed, perturbation analysis, separate evidence class | later |
| `DIF-001` | Differential oracle | independent model/runner outputs, comparison relation, mismatch corpus, shrinking/replay | now |
| `DRF-001` | Version drift | old/new symbol, signature, AST, primitive, test, and behavior diffs plus impacted claims | now |
| `LIN-001` | Lineage/evidence bundle | input hashes, generator/extractor versions, output hashes, theorem/fixture/claim links | now |

### Concurrency and runtime extensions

| ID | Specification | Required content | Timing |
|---|---|---|---|
| `SCH-001` | Scheduler algebra | task queue, priority/FIFO policy, yield budget, fixed schedule, nondeterministic alternative, fairness assumptions | T5 |
| `ASY-001` | Callback suspension | pending/resumed/cancelled states, synchronous-resume buffering, single-shot rule, cancellation finalizer | T5 |
| `INT-001` | Interruption | interrupt cause collection, interruptible points, masking/restoration, pending delivery | T4/T5 |
| `SCP-001` | Scope/resource state | Empty/Open/Closed, registration/removal, reverse sequential order, close idempotence, exit-aware finalizers | T4 |
| `FIB-001` | Fiber topology | parent/child/daemon ownership, observer lifecycle, fork/await/join, terminal cleanup | T6 |
| `RAC-001` | Race/concurrent choice | winner condition, loser interruption/await, all-failure behavior, permitted trace quotient | T6 |

Every specification must name its observation and exclusions. For example,
`SCH-001` cannot say “deterministic scheduler” without saying whether operation
budget, priority, dispatch, host promises, timers, and callback reentrancy are
visible or abstracted.

## Decisions Foldlab must freeze

| Decision | Options | Recommendation for the first slice | Revisit when |
|---|---|---|---|
| Subject of modeling | raw runtime objects; public API; Foldlab descriptor | descriptor semantics related to a whitelisted public API slice | primitive-level G3/G4 bridge |
| Ingestion direction | arbitrary TS -> Core; Core -> generated TS; both | generator-first, then fail-closed extraction of the generated subset | generator/fixture path is stable |
| Canonical syntax | internal op labels; source AST; owned Effect Core | owned typed Core; internal labels remain provenance only | never identify labels with semantics automatically |
| Function representation | raw closures; opaque oracle; named blocks | named first-order total blocks | explicit closure conversion project |
| Value universe | arbitrary JS; JSON; small algebra | small integer/text/Boolean/product algebra | codec/equality laws are proved |
| Initial observation | primitive steps; traces; final `Exit` | final `ExitPure` only | T2 requests/causes or T4 resources |
| Failure model | collapse to `E`; full cause immediately; staged | single `Fail E` plus proved embedding into a future flat `Cause` | `sync`, defects, interrupts, finalizers |
| Machine | higher-order continuation functions; list of named frames | named typed frames and explicit configurations | stored/multi-shot or higher-order effects |
| Termination | assume; fuel; finite syntax/total blocks | finite syntax and total block evaluator | recursion/suspend/divergence |
| Eager forms | normalize silently; model construction time; reject | reject as a separate semantic tier | construction-time observation is defined |
| Custom Effectable | treat as built-in; opaque event; reject | reject with stable reason; design plugin interface only | a primitive has its own semantics/evidence package |
| Context | runtime overlays/caches; abstract map | defer; later abstract typed map | T3 service slice |
| Source analysis | regex; tree-sitter; TS compiler API | pinned TypeScript `Program` and `TypeChecker`; optional CST for provenance | compiler version changes |
| Runtime harness | internal imports; monkeypatch loop; public APIs | generated public Effect programs plus `runPromiseExit`/`runFork` | internal event evidence is explicitly needed |
| Scheduler | default host; deterministic queue; nondeterministic relation | absent T0/T1; explicit deterministic scheduler T5; nondeterministic relation T6 | concurrency begins |
| Tracing/metrics | semantic events; hidden hooks | excluded and disabled/ignored where possible | instrumentation becomes the research subject |
| G4 target | TypeScript without semantics; descriptor translation; runtime | prove Core-to-machine/normalization translations first | an accepted source semantics exists |

### G4 prerequisite

G4 is unavailable merely because a tool maps TypeScript nodes to Lean data. A
semantics-preservation theorem requires:

1. a formal source domain;
2. a source observation/semantics;
3. a target observation/semantics;
4. a translation and accepted-domain judgment; and
5. a theorem relating the two.

Source links plus passing G3 fixtures do not supply item 1. The first honest G4
target should therefore be a Foldlab-owned translation—such as descriptor
normalization, descriptor-to-machine initialization, or a verified Core
lowering. A TypeScript-to-Core G4 claim should wait for an explicit semantics of
the admitted TypeScript expression language.

## Proposed project and artifact layout

The actual names should be accepted through an ADR before implementation, but a
concrete layout makes the work estimable:

```text
docs/effect-typescript-semantics/runtime-core/
  CONTEXT.md
  CLAIMS.md
  resources/
    SOURCE-LEDGER.md
    ACCEPTED-SUBSET.md
    OBSERVATIONS.md
    TRACEABILITY.md
    FIXTURES.md
    DECISIONS/

formal/effect-runtime-core/
  lakefile.toml
  lean-toolchain
  EffectRuntimeCore.lean
  EffectRuntimeCore/
    Value.lean
    Block.lean
    Syntax.lean
    Typing.lean
    Exit.lean
    Denotation.lean
    Frame.lean
    Machine.lean
    Simulation.lean
    Codec.lean
    Proofs.lean

experiments/effect-runtime-extract/
  package.json
  tsconfig.json
  src/sourceSnapshot.ts
  src/symbolInventory.ts
  src/accept.ts
  src/canonicalize.ts
  src/generateEffect.ts
  src/runFixtures.ts
  src/normalizeTrace.ts
  src/changeReport.ts
```

Suggested generated artifacts:

| Artifact | Purpose |
|---|---|
| `source-snapshot.json` | source, compiler, config, and file hashes |
| `symbol-inventory.json` | declarations, overloads, type facts, spans, imports, acceptance state |
| `runtime-protocol.json` | built-in primitive fields/identifiers and open extension points |
| `descriptor.json` | canonical accepted EffectCore program and digest |
| `fixture-manifest.json` | cases, pins, expected observations, rejection reasons |
| `raw-trace.jsonl` | unnormalized runner evidence |
| `normalized-observation.json` | declared comparison projection |
| `lineage.json` | input -> tool -> output -> theorem/fixture/claim hashes |
| `change-report.json` | version-to-version semantic inventory and claim impact |

Generated files should never overwrite handwritten specifications. CI should
regenerate to a temporary directory, compare canonical hashes, and fail on
unreviewed drift.

## Runtime conformance harness

The package blocks public imports of `./internal/*`, so the default harness
should not import or monkeypatch `FiberImpl`. Use only public constructors and
execution APIs. `runPromiseExit` retains the complete terminal `Exit`; `runFork`
permits a custom scheduler and a public completion observer. Primitive
`toJSON()` is a diagnostic shape, not an executable serialization because it
omits private symbols and closure meaning.

Recommended runner topology:

1. validate a fixture and its source/tool pins;
2. compile its descriptor to public Effect combinators;
3. install no scheduler for T0/T1, or a recorded deterministic scheduler for a
   later scheduler fixture;
4. execute via `runPromiseExit` or `runFork`;
5. record raw terminal data and permitted public events;
6. normalize only according to `OBS-001`;
7. compare with the independent Lean/reference result;
8. persist mismatches as replayable counterexamples; and
9. record all hashes in the lineage bundle.

An optional internal adapter can expose operation/frame events from a
pin-coupled test build, but it is a separate evidence class. Instrumenting
`runLoop`, global schedulers, or primitive evaluators can change reentrancy,
yield, interruption, and observer ordering, so an instrumented result cannot be
silently substituted for the unmodified runtime.

### Initial fixture matrix

| Family | Positive cases | Negative/near-miss cases |
|---|---|---|
| terminal | success/failure for each value constructor | unsupported value, malformed descriptor |
| success frames | one and nested `flatMap`, left/right identity, associativity instances | left failure must not invoke block; block throws/reaches host |
| failure frames | recover one `Fail`, nested recovery, success bypasses handler | defect/interrupt cause rejected; handler returns custom Effectable |
| callbacks | each named block and closed capture | mutable/global capture, unknown function, reflection, unsafe cast |
| source forms | data-first/data-last public calls selected by exact symbol/overload | alias to unknown callable, forged structural Effect, eager variant |
| provenance | correct pin and hashes | revision/compiler/config mismatch |

Later concurrency fixtures should enumerate small schedules rather than trust
wall-clock sleeps: budgets 0–3, at most two child fibers, one callback with
resume/cancel permutations, up to three finalizers, and two-way races to a
bounded depth.

## Staged work breakdown and exit criteria

### M0 — source inventory and decisions

Deliver `SRC-*`, `ACC-*`, the two ADRs for observation and defunctionalization,
and examples/near misses for every admitted form.

Exit only when the checkout resolves to the lock, every admitted public symbol
maps to exact pinned declarations, and all unsupported constructs have stable
rejection codes.

### M1 — T0/T1 Lean core

Implement the finite value/block language, syntax, direct denotation, frames,
and continuation machine. Prove the T0/T1 theorem inventory and perform an
axiom audit.

Exit only when machine-direct equivalence, determinism, termination, callback
branching laws, and codec/normalization laws pass without `sorry`/`admit`.

### M2 — generated runtime fixtures

Generate public Effect programs from the descriptor and compare final `Exit`
observations against the pinned runtime. Retain raw data and normalized
observations separately.

Exit only when clean-checkout reproduction passes, mismatches are classified,
and the G3 wording is explicitly limited to the enumerated/accepted fixture
domain.

### M3 — fail-closed TypeScript ingestion

Use the pinned compiler API to accept only the generated source grammar first.
Extend manually with negative tests. Prove preservation only for a formally
defined source expression language; otherwise keep this as traceability and G3
evidence.

Exit only when regeneration is deterministic, unsupported callbacks and
Effectables are rejected, and source maps/lineage connect every descriptor node
to source facts.

### M4 — defects and services

Add the flat Cause model, `sync`/throw-to-`Die`, then typed service requests and
an abstract environment. Keep defects and environment operations in separate
increments.

Exit only when typed catch cannot absorb defects/interruption accidentally and
environment provision/lookup laws and mutable-service boundaries are explicit.

### M5 — resources and interruption

Add `OnExit`, sequential scopes, finalizers, mask restoration, and pending
interrupt delivery. Prove exactly-once cleanup, reverse sequential order, close
idempotence, and cause combination. Parallel finalizers remain later.

### M6 — async and fibers

Add a scheduler-parameterized event semantics, callback single-shot states,
fork/await/join, and bounded multi-fiber checks. Move from outcome equality to
weak/branching bisimulation or trace refinement. State fairness only as an
assumption; the runtime permits yield suppression.

### Stop/go rules

- Stop if a closure, custom Effectable, host effect, or eager callback enters
  T0/T1 without a named semantic rule.
- Stop if `E`, `Die`, and `Interrupt` are collapsed to one error.
- Stop if a model theorem is being used as source/runtime conformance evidence.
- Stop before G4 if the source observation relation is absent.
- Stop before concurrency if scheduler, cancellation, finalizer, and fairness
  observations are not frozen.
- Go to the next tier only after the previous tier's assumptions remain visible
  in theorem statements, fixtures, source ledgers, and claim records.

## Candidate claim registry

These IDs are proposals, not current claims. They should be added only when the
corresponding project resources and evidence exist.

| ID | Candidate wording | Gate | Minimum evidence |
|---|---|---|---|
| `RUN-001` | The admitted continuation-core source symbols and observations are specified against the pinned Effect revision. | G1 | source ledger, accepted subset, Lean declarations |
| `RUN-002` | The continuation-core syntax, frames, configurations, and final-Exit observation are modeled. | G1 | elaborating model and traceability |
| `RUN-003` | Continuation-machine steps preserve configuration well-formedness. | G2 | kernel theorem and axiom audit |
| `RUN-004` | The admitted finite continuation machine terminates and is deterministic. | G2 | termination/determinism theorems |
| `RUN-005` | The machine and direct denotation agree for every admitted descriptor. | G2 | simulation/adequacy theorem |
| `RUN-006` | The admitted model satisfies identity, associativity, and handler branch laws under final-Exit observation. | G2 | kernel laws with callback conditions |
| `RUN-007` | Canonical encoding, decoding, and normalization preserve the admitted denotation. | G2 | codec/normalization theorems |
| `RUN-008` | The pinned Effect implementation agrees with the model for the enumerated accepted fixture domain and final-Exit observation. | G3 | pinned reproducible differential suite |
| `RUN-009` | Translation T between two explicitly defined formal domains preserves observation O. | G4 | source/target semantics and preservation theorem |
| `RUN-010` | Named compiled artifact and host runtime R agree for observation O on the covered domain. | G5 | artifact hashes, compiler/host pins, integration evidence |

Do not word `RUN-008` as universal runtime conformance. Do not instantiate
`RUN-009` with TypeScript source until an admitted TypeScript semantics exists.

## Trust boundary and risk register

| Boundary | Main risk | Required mitigation |
|---|---|---|
| Git/source lock | wrong checkout, origin, or dirty source | verify origin/commit/path/version and hash admitted files |
| TypeScript frontend | overload/module-resolution/type-inference drift | pin compiler and config; emit selected symbols/signatures; negative tests |
| Accepted-subset elaborator | silently classifies an unsupported closure/call | fail closed, stable rejection reasons, mutation/host/capture analysis |
| Canonical codec/hash | different bytes for same intended descriptor or collision domain ambiguity | versioned schema and domain separator; prove round trips/canonicalization |
| Lean statement | theorem proves the wrong informal requirement | requirement traceability, examples and near-miss counterexamples, quantifier review |
| Generated TypeScript | generator changes evaluation order or chooses eager API | source maps, generated golden fixtures, public-symbol checks, independent review |
| Runtime oracle | one implementation is compared with itself | independent descriptor evaluator; retain raw observations; cross-check generated cases |
| Instrumentation | hooks perturb yields, interruption, or callbacks | public uninstrumented runner is primary; internal adapter is separately labeled |
| Node/compiler/host | erased types and host queues differ from model | name versions/config/artifact hash; exclude host events until modeled |
| Concurrency reduction | bounded schedules miss behavior | state bounds in results, counterexample replay, proof or sound abstraction before universal claims |

The trusted computing base must list the Lean kernel and dependencies,
extractor/generator, TypeScript compiler, canonical codec, Node/host, source
checkout, and any solver or native evaluator. Their roles are different: a
trusted generator can invalidate correspondence even when every generated Lean
theorem kernel-checks.

## Prior-art patterns to reuse

- [Interaction Trees](https://www.cis.upenn.edu/~stevez/papers/XZHH%2B20.pdf)
  separate event syntax, handlers, and weak bisimulation. Use this pattern once
  visible requests or suspension enter; do not use an ITree as a wire format.
- [Choice Trees](https://arxiv.org/abs/2211.06863) separate internal and external
  nondeterminism. Use their distinction when scheduler choice enters T6.
- [DimSum](https://doi.org/10.1145/3571220) connects independently defined
  language machines through events and wrappers. This is the right pattern for
  Lean-machine-to-JavaScript and later Wasm relations.
- [A Relational Separation Logic for Effect Handlers](https://doi.org/10.1145/3776676)
  shows how a simple specification can refine a continuation-bearing,
  stateful/concurrent implementation. Its restrictions on bind/context
  reasoning warn against assuming congruence for arbitrary handler contexts.
- [Generalized Evidence Passing](https://doi.org/10.1145/3473576) and Effekt's
  [implementation pipeline](https://github.com/effekt-lang/effekt-website/blob/main/docs/implementation.md)
  demonstrate staged, semantics-related lowering rather than identifying an
  effect calculus with one representation.
- [Iris-WasmFX](https://doi.org/10.1145/3808271) is later proof-architecture
  guidance for stored continuations and stack switching. It supplies no bridge
  from Effect TypeScript to WasmFX.
- [Lean-MLIR](https://arxiv.org/abs/2407.03685) is a useful model for a semantic
  IR, checked rewrites, and translation validation. Use it for later optimizer
  certificates, not as evidence about Effect.

## Immediate scoping deliverables

The next implementation-oriented pass should produce these ten artifacts in
order:

1. runtime-core project charter and two ADRs: final-Exit observation and named
   defunctionalized callbacks;
2. pinned source ledger for `Effect`, `Primitive`, `FiberImpl`, `Exit`, and
   `Cause` symbols used by T0/T1;
3. accepted grammar plus stable rejection taxonomy and twenty near-miss source
   examples;
4. canonical value/block/descriptor schema with codec and digest policy;
5. Lean syntax, typing, direct denotation, frames, and machine skeletons;
6. theorem statement review before proof work, including callback side
   conditions and full exclusions;
7. generator from descriptors to public Effect combinators;
8. public runtime runner with raw and normalized final-Exit fixtures;
9. lineage/change-report tooling tied to the source lock; and
10. proposed `RUN-*` claim entries, added to the registry only as their evidence
    gates are actually satisfied.

## Exclusions and unknowns

Excluded from this report’s claims: arbitrary TypeScript ingestion; semantic
reconstruction of JavaScript closures; custom `Effectable` evaluators;
compiler erasure, bundling/minification, and JavaScript engine semantics; timers
and I/O; allocation/performance; exact async callback behavior beyond the cited
implementation facts; modules outside the admitted source slice; and any
whole-library theorem.

Unknowns requiring a dedicated source slice: eager construction-time behavior;
throwing/recursive callbacks; `sync`/`suspend`; full cause annotations and
reason deduplication observations; context-reference defaults; request batching
and caches; stream/channel machines; managed-runtime shutdown; platform
clock/randomness; custom schedulers; tracer implementations; and the complete
async primitive surface. Tests are useful behavioral evidence but do not
substitute for a source semantics or proof. The tests named in the current
source lock remain Result tests, not runtime-core conformance tests.

## Claim posture

This document supports only “source snapshot identified” (G0) and a research
inventory. A Lean definition of any tier would be G1; a kernel theorem about it
would be G2; implementation conformance requires reproducible fixtures (G3),
translation preservation G4, and named host/runtime evidence G5, as prescribed
by [`CLAIM-GATES.md`](../effect-typescript-semantics/CLAIM-GATES.md).
