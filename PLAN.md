# Effect4 extraction and cutover plan

Status: active bootstrap, 2026-08-31

## Objective

Extract the reusable effect algebra from Foldlab into a native Lean library,
then extend it to a closed first-order model of Effect Schema, services and
contexts, layers, runtimes and managed runtimes, scopes and resources, fibers,
arbitrary control flow, classification, and checked TypeScript generation.

The cutover is additive. Foldlab remains buildable throughout and adopts
Effect4 through downstream compatibility modules only after each moved type's
proof graph is closed.

## Non-negotiable semantic boundaries

- Authored programs and schemas are first-order, finite, versioned data.
- Sequential proof syntax and general cyclic flow are separate layers related
  by embeddings; one is not silently serialized as the other.
- Full execution meaning is a relation over configurations, decisions, and
  observations. A fixed compatible tape yields one replay path.
- Live frontiers are distinct from typed failure, defects, interruption, and
  domain-specific refusal.
- Resource finalization observes the state produced before any failure.
- Schema is a first-class portable description with separate decoded,
  encoded, and representation types, plus explicit effectful transforms.
- Pure calculation stays outside the effect program carrier.
- TypeScript tooling and runtime observations are evidence targets; Lean owns
  the model and theorem statements.

## Phase gates

| Phase | Deliverable | Exit gate |
| --- | --- | --- |
| P0 — bootstrap | independent Lake package, exact toolchain, root routing, source pin | clean `lake build`; no Foldlab dependency |
| P1 — inventory | mechanical declaration/test/surface manifest and source-to-destination dispositions | every source row classified; incompatible workshop carriers excluded |
| P2 — breadth scaffold | empty modules for every major category, central contracts/counterexamples, generated closure schema | no semantic declarations; scaffold build and declaration scan green |
| P3 — algebra substrate | signature, program, handler, interpretation, lawful composition, universe policy | breaker battery green; monad/handler laws proved; axiom receipts recorded |
| P4 — first-order flow | checked finite graph around sequential bodies, explicit decisions/frontiers, relational runs | checker soundness and relative completeness; incompatible S2 designs resolved |
| P5 — effect data | rows, cause/exit, Schema codecs/refinements/transforms, portable protocol identities | round trips and normalization proved; identity owners unique |
| P6 — environment | Context keys, services, environment provision, Layer graph/build, Scope/resource, Runtime/ManagedRuntime | service discharge, layer composition, acquisition/finalization laws proved |
| P7 — concurrency | fibers, scheduler, interruption/masks, races, Deferred/Queue/Ref and coordination | replay determinism under fixed tape; cleanup laws; safety fairness-free |
| P8 — structured flow | Channel, Stream/Sink/Pull/Take, Schedule, transactions as separate calculi | each calculus has explicit embedding or direct semantics and closure rows |
| P9 — analysis | independent abstract domains, products, fixpoints, may/must transfer | concretization soundness per domain; no unjustified whole-product invariance |
| P10 — targets | typed TypeScript IR, lowering, render/decode, Effect v4 profile | typing and simulation proofs; deterministic bytes; exact source coverage |
| P11 — host evidence | Effect runtime/replay and `@effect/tsgo` language-service harnesses | positive, negative, mutation, coverage, and drift gates green at exact pins |
| P12 — integration | Foldlab compatibility adapter and staged retirement of duplicated generic code | both repositories build; per-type compatibility proofs; no semantic drift |
| P13 — cutover | generated type-closure and cutover decision | every required row closed; no manual completeness override |

## Broad-before-deep representatives

Before deep work, freeze one representative contract in each group:

1. algebra: one operation and one handler;
2. admission: one invalid raw graph with first-error diagnostics;
3. Schema: one structure codec with one effectful transform;
4. environment: one service built by one scoped layer;
5. runtime: one managed runtime executing one checked program;
6. concurrency: one fork/join/interruption lifecycle;
7. structured flow: one finite stream/channel embedding;
8. classification: one independent may/must domain;
9. target: one generated Effect v4 program checked by the language service;
10. compatibility: one Foldlab CAS operation related in both directions.

## Dependency policy

Lean core and Std are the default substrate. A third-party Lean dependency is
added only after an exact-pin acceptance probe shows that it builds on the
pinned Lean version, has acceptable licensing and transitive cost, supplies a
materially deeper public abstraction, and does not force the library's result
universe or first-order representation to narrow accidentally. Borrowed API
ideas are credited even when their implementation is not imported.

## Current phase

P0 is in progress. The generated Lake project builds at Lean 4.33.1. The next
actions are to freeze the Foldlab source pin, land the mechanical port manifest,
replace the generated example module with the empty breadth scaffold, and have
an independent breaker commit the first algebra compatibility packet before
any carrier is implemented.
