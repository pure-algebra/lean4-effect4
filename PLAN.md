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

The broad sweep proceeds in this order. Items 1 and 2 are closed. Items 3 and
4 are in progress on disjoint owners.

1. **Closed.** The algebra declarations stay frozen and downstream
   compatibility rows are recorded separately.
2. **Closed.** One checked Flow/admission representative and its
   refusal/frontier counterexamples are frozen, with a mutation gate.
3. **In progress.** The Schema representation slice. The 22-tag census alphabet and
   its five sub-alphabets are frozen and implemented; the payload carrier —
   the mutually recursive `Representation`/`Check` tree, the document
   envelopes, and the field-admission surface — is implemented against a
   frozen breaker packet whose theorem battery is green. No temporary Schema
   effect carrier was introduced. Independent assurance found that the
   payload-surface gate still accepts an unallocated public alias and a D7
   owner drift, and the generated proof/receipt join does not exist. Those two
   blockers keep both payload graphs and Schema cutover open.
4. **In progress.** One Context/Service/Layer/Scope/ManagedRuntime
   representative. `docs/ENVIRONMENT-DAG.md` owns the build order, its fences,
   and what crosses each edge. Layer L0 node `Context/Key` is closed: a
   context key is frozen as first-order data, not type-indexed, with a
   decidable strict linear order and a supplied `ServiceUniverse` as its only
   type-reading boundary. Its sibling L0 node `Data/Row` is open and blocks
   all of L1.
5. freeze one Fiber/scheduler/interruption representative; and
6. introduce declarations only after each owning breaker packet is green
   against the empty stub and red against its rejected mutations.

## Near-term proof burden

This is the ordered burden from the current tree through the first complete
environment representative. It distinguishes theorem work from closure
machinery so a passing local battery is never mistaken for an exhaustive
cutover decision.

| Order | Owner | Assurance route | Required work before advancing |
| ---: | --- | --- | --- |
| 0 | Schema payload surface | gate repair, not a new proof graph | Reject unallocated public aliases, check every D7 name is absent at the Payload-only boundary, inspect every D7 owner, and kill duplicate-declaration and owner-drift mutants. The current Lean payload equations are green, but independent assurance showed the existing surface gate accepts both defect classes. |
| 1 | `SCHEMA-PG-PAYLOAD` and `SCHEMA-PG-FIELD-ADMISSION` | two existing graphs plus attached leaf receipts | Join the exact declaration census, theorem receipts, axiom receipts, counterexample witnesses, and repaired surface evidence mechanically. Recursive JSON/payload equality and recursive field admission carry the graphs. `Float64`, scalar sums, plain records, and document containers retain local receipts. No denotation, wire, or host-equivalence claim is part of this closure. |
| 2 | `Effect4.ServiceKey` | standalone leaf receipt | The key carrier, exact name-major order, collision relation, universe-relative carrier, explicit transport, carrier-collision witness, and axiom receipt are implemented and green. Before `Data.Row` freezes, probe a bridge to Lean 4.33's standard lawful-order package. Adopt that bridge if it preserves the frozen relation; do not mint an Effect4-specific order-law carrier. |
| 3 | `Effect4.Data.Row` | `DATA-PG-ROW`, required graph | Freeze the generic carrier and its raw-list boundary; prove sorted insertion preserves strict ascent, normalization preserves membership, normalization produces a canonical row, canonical extensionality, and normalization idempotence. Then prove union membership, associativity, commutativity, idempotence, and requirement weakening. Retain executable counterexamples showing that order-preserving dedup is not normalization, raw member equality does not imply raw-list equality, and normalization erases multiplicity and therefore proves no denotational preservation by itself. |
| 4 | `Context.Service` and `Context.Requirement` | local receipts attached to `DATA-PG-ROW` and the environment graph unless their breaker adds a semantic claim | Reuse `ServiceKey` and `Data.Row`; no second key, row, type-code, or order carrier. Freeze the universe-relative service-value shape, the exact `Requirement = Row ServiceKey` relationship or a named view, transport coherence, membership, empty requirement, union, and weakening. Close the `ENV-KEY-INTERP` edge only for the exact supplied-universe hypotheses proved here. |
| 5 | `Context.Environment` | `ENV-PG-ENVIRONMENT`, required graph | Freeze raw versus admitted environment entries, the conflict rule, lookup, provision, and requirement satisfaction. Prove admission soundness/reflection, lookup type safety relative to one supplied universe, lookup after provision at the same key, lookup frame at distinct keys, conflict exclusion, discharge monotonicity under requirement weakening, and extensional equality at the chosen observation. Counterexamples must cover nominal collision, carrier collision, mixed universes, duplicate keys, and proof-free casts. |
| 6 | `Layer.Description` plus `Runtime.Scope` representative | separate graph-bearing owners when composition/resource meaning appears | Freeze only after the environment graph closes. Layer then owes identity and associative composition at its declared merge operation, requirement/output accounting, and later memo agreement. Scope then owes acquisition/finalization order and the law that finalization observes state produced before failure. These are graphs; the passive identifier and record leaves beneath them are not. |

### `DATA-PG-ROW` proposed theorem spine

Names remain provisional until the breaker freezes their exact signatures, but
the dependency order is fixed:

```text
strict-order bridge
  -> mem_insert
  -> ascending_insert
  -> mem_normalize + ascending_normalize
  -> canonical_extensionality
  -> normalize_of_canonical
  -> normalize_idempotent
  -> mem_union
  -> union_associative + union_commutative + union_idempotent
  -> subset/weakening reflexive + transitive
  -> union-left weakening + union-right weakening
```

The carrier must expose one canonical spelling. If raw input remains a plain
`List`, checked construction returns the existing canonical `Row`; it does not
create a second checked row type. The graph's construction edge owns the
normalizer and admission boundary, the laws edge owns union, and the
representation edge owns list membership/extensionality. No theorem in this
graph may be named as preserving program meaning; that bridge belongs to the
first calculus that interprets a requirement row.

### Immediate go/no-go gates

Work advances to the next row only when all gates in the current row are green:

1. frozen declaration signatures and negative names;
2. focused theorem battery;
3. relevant counterexample and mutation reactions;
4. clean package build;
5. exported-theorem axiom receipt;
6. independent assurance; and
7. the generated declaration/obligation/receipt join for graph-bearing or
   cutover-bearing owners.

Items 1 through 6 close a standalone leaf. A graph-bearing owner additionally
requires item 7 and every applicable graph edge; trivial helpers do not receive
empty graphs.

## Two rules the Schema slice paid for

Both are enforced for the remaining slices and both are recorded in
`docs/ENVIRONMENT-DAG.md`.

**Lay out the dependency DAG before dispatching concurrent builders.** The
Schema payload slice was built without one. Two builders worked against a
contract that grew while they worked; two obligations landed after one
builder had measured its work and finished, and no fence owned them. The
battery stayed red on a seam nobody was assigned. A DAG now names every node's
fence and every edge's crossing declarations, shared receipt files are
coordinator-owned rather than inside any fence, and a layer's contract is
frozen before that layer is dispatched and is not edited while it is in
flight.

**A gate that has not been shown to react is not evidence.** Three gates in
the Schema slice passed while accepting the defect they existed to catch, each
confirmed by executing the attack: a census gate whose union extractor stopped
at the first comment, a battery that pinned tag spellings only up to a
permutation of seventeen constructors, and a trust gate whose detector never
ran at all because an earlier module failed to build. Each is now paired with
a reaction test that names its mutants, and the declared-red list the trust
gate consults is self-checking in both directions.
