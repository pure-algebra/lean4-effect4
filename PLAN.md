# Effect4 extraction and cutover plan

Status: active bootstrap, 2026-08-31

## Objective

Extract the reusable effect algebra from Foldlab into a native Lean library,
then extend it to a closed first-order model of Effect Schema, services and
contexts, layers, runtimes and managed runtimes, scopes and resources, fibers,
arbitrary control flow, classification, and checked TypeScript generation.

The cutover is additive. Foldlab remains buildable throughout and adopts
Effect4 through downstream compatibility modules only after each moved type's
declared assurance route is closed. Semantic or cutover-bearing types require
a proof graph; passive finite leaf declarations close with their exact local
receipts and any named parent-graph edge. Trivial leaves do not receive empty
ceremonial graphs.

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
| P2 — breadth scaffold | empty modules for every major category, central contracts/counterexamples, generated assurance schema | no semantic declarations; scaffold build and declaration scan green |
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
| P13 — cutover | generated declaration-assurance and cutover decision | every required graph edge and leaf receipt closed; no manual completeness override |

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

P0, P2, and the native P3 algebra substrate are complete. The repository is
an independent Lean 4.33.1 package, all planned category modules exist, every
module is reached by the default build, and breadth stubs contain no semantic
declarations. The retained algebra declarations now have exact signature
checks, kernel-checked proofs, exhaustive module and axiom gates, and an
independent assurance review. That review found no duplicate generic carrier
and approved the native algebra proof graph. Foldlab compatibility spellings,
adapters, and interpretation-preservation results remain P12 obligations; they
do not keep the independent P3 substrate open.

P1 remains open as a recurring exhaustiveness gate rather than a prose-only
inventory. The current manifest pins Foldlab, Effect rc.112, the resolved npm
package, TypeScript, tsgo, the language-service clone, the sampled wild-type
corpus, and PolyFun prior art. The next inventory deliverable is a generated
declaration/source-disposition join; missing rows fail cutover.

The broad sweep now proceeds in this order:

1. keep the closed algebra declarations frozen while recording downstream
   compatibility rows separately;
2. freeze one checked Flow/admission representative and its refusal/frontier
   counterexamples;
3. freeze the 22-case Schema representation and four-index directional codec
   packet without introducing a temporary Schema effect carrier;
4. freeze one Context/Service/Layer/Scope/ManagedRuntime representative;
5. freeze one Fiber/scheduler/interruption representative; and
6. introduce declarations only after each owning breaker packet is green
   against the empty stub and red against its rejected mutations.
