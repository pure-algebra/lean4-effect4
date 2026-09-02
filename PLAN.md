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

The P5 Cause/Exit data packet is implemented. Its frozen contract, seven
registered counterexamples (`E4-SEM-CE-001` through `E4-SEM-CE-007`), and public
theorem axiom report are green. `PORT-MANIFEST.md` "Cause and Exit declaration
dispositions" now mirrors the six native type allocations from
`docs/CAUSE-DAG.md`; that DAG remains the owner of `CAUSE-PG-FLAT` and its
host-boundary obligations. The runtime witness wiring has landed separately in
`Effect4Test/Audit/RuntimeCoverage.lean`. The generated Cause/Exit declaration
and assurance join and direct host evidence remain open. Treating Exit itself
as an executable primitive still needs the continuation-machine calculus.
This records progress within P5, not closure of P5, the graph, or cutover.

The fork/supervision continuation of P9 is implemented against independent
breaker checkpoint `5568f00`: all 294 exact checks and 136 public theorem
obligations pass, as do the fifteen registered finite counterexamples
(`E4-CONC-CE-012` through `E4-CONC-CE-026`). `PORT-MANIFEST.md` mirrors the 27
type/judgment dispositions, and the existing Fiber assurance join includes
all 705 compiler-owned declarations, 19 exact shapes, and three finite leaves.
`docs/SUPERVISION-IMPLEMENTATION.md` records verification and boundaries.
The generated supervision graph closes six local edges while source bridges,
target interpretation, and binding the full repository trust receipt remain
required-open. All fifteen related runtime rows remain partial. The independent
binary race packet is unchanged; this is not concurrency or cutover closure.

The broad sweep proceeds in this order. Items 1, 2, and 5 are closed. Items 3
and 4 are in progress on disjoint owners. Item 6 is frozen and clean red for
its independent builder.

1. **Closed.** The algebra declarations stay frozen and downstream
   compatibility rows are recorded separately.
2. **Closed.** One checked Flow/admission representative and its
   refusal/frontier counterexamples are frozen, with a mutation gate.
3. **Structurally closed; denotation remains next.** The Schema representation
   slice now has a generated declaration/proof join over all 1,298 declarations
   owned by its seven source modules, all 493 theorem and kernel-dependency
   receipts, 32 registered counterexamples, nine duplicate-prevention names,
   the exact rc.112 tag and field pins, and the repaired 13-case payload-surface
   detector. This closes every applicable edge of
   `SCHEMA-PG-REPRESENTATION-TAG`, all of
   `SCHEMA-PG-FIELD-ADMISSION`, and the declaration, equality, tag-projection,
   leaf, and general-recursor shares of `SCHEMA-PG-PAYLOAD`. The fixed recursor
   battery covers all 24 constructor equations and both rebuild laws; the
   retained route trace detects omission, duplication, and reordering across
   all 13 recursive positions. Document interpretation, wire semantics, codecs,
   and host conformance remain their separately owned graphs; no temporary
   Schema effect carrier was introduced.
4. **In progress.** One Context/Service/Layer/Scope/ManagedRuntime
   representative. `docs/ENVIRONMENT-DAG.md` owns the build order, its fences,
   and what crosses each edge. Layer L0 node `Context/Key` is implemented with
   a green frozen battery and axiom receipt: a context key is first-order data,
   not type-indexed, with a decidable strict linear order and a supplied
   `ServiceUniverse` as its only type-reading boundary. Its generated exact
   owned-declaration/API/owner/theorem/axiom join and five mutation reactions
   are green, so `ENV-LEAF-KEY-IDENTITY` is closed. The additive Std order
   bridge has its own green local receipt, `ENV-LEAF-KEY-ORDER-BRIDGE`, and is
   routed only to `DATA-PG-ROW/ORDER`; it creates no carrier, proof graph, or
   competing edge status. The mechanically generated Data.Row join closes all
   ten `DATA-PG-ROW` edges from an exact 60-declaration census, separate
   34-name authored API, 23 theorem and axiom receipts, nine counterexamples,
   and five detector reactions. `ENV-KEY-INTERP` remains the one open semantic
   attachment to the shared Context graph, so L1 may now begin without
   claiming Context interpretation closure.
5. **Closed.** The Fiber/scheduler/interruption representative. Its generated
   assurance join covers the exact 504 declarations owned by the three source
   modules, a separate 185-name authored API, all 92 public theorem and kernel
   dependency receipts, 16 existing-type rows, 14 passive-leaf receipts, 12
   duplicate-prevention names, all seven registered concurrency attacks, and
   every edge of `FIBER-PG-REPRESENTATIVE`. The seven applicable edges are
   derived `required-closed`; representation, bridges, and targets remain the
   three authored `not-applicable` edges for this bounded representative. This
   closes the representative only, not the full concurrency category or host
   cutover; and
6. **Frozen / RED.** The binary `raceFirst` representative. Its breaker reuses
   the closed Fiber machine and scheduler, adds only an explicit winner choice
   and race-level result envelopes, and keeps first-success racing outside the
   packet until terminal-result classification exists. Four executable attacks
   force winner-choice reification, first-completion separation, loser cleanup,
   and live masked-frontier handling. The builder must close
   `RACE-PG-BINARY-FIRST-COMPLETION`; and
7. introduce declarations only after each owning breaker packet is green
   against the empty stub and red against its rejected mutations.

## Near-term proof burden

This is the ordered burden from the current tree through the first complete
environment representative. It distinguishes theorem work from closure
machinery so a passing local battery is never mistaken for an exhaustive
cutover decision.

| Order | Owner | Assurance route | Required work before advancing |
| ---: | --- | --- | --- |
| 0 | Schema payload surface | gate repair, not a new proof graph | **Closed.** The gate rejects aliases and ordinary type-valued definitions, proves the Payload-only D0-D3/D4-D7 boundary, checks every D7 owner, and kills all 13 specified shape, duplication, owner, import, and override defects. |
| 1 | Schema payload, field admission, optics, and annotation data | four required graphs plus attached local receipts | **Closed.** The generated join covers 1,298 owned declarations, 493 theorem/axiom receipts, 32 counterexamples, exact source pins, all leaf routes, the complete general recursor, lawful optic composition, and exhaustive annotation traversal. The annotation host gate also checks the generated field-admission witness with TypeScript, Effect, and the Effect language service. No denotation, document-reference, wire, or host-equivalence claim is part of this structural closure. |
| 1a | `SCHEMA-PG-EFFECTFUL-FIELD` | additive generated-program graph over existing Schema/effect carriers | **Lean core implemented.** Exact marker codec/admission, alphabet and operation identity agreement, effectful `get`/`set`/`modify`, interpreter-order laws, and `E4-SCHEMA-CE-049`..`052` are present. The next forward slice generates and checks the TypeScript field API from wild-type property annotations. |
| 2 | `Effect4.ServiceName`, `ServiceTypeCode`, `ServiceKey`, and `ServiceUniverse` | local key-family and Std-order-bridge receipts; `ENV-KEY-INTERP` alone attaches to the Context graph | **Closed locally.** `ENV-LEAF-KEY-IDENTITY` and `ENV-LEAF-KEY-ORDER-BRIDGE` are generated from the exact 97-name module census, separate 25-name Key API, separate 14-name Std bridge API, theorem/axiom receipts, and five detector reactions. The bridge is a delegated route into the now-closed `DATA-PG-ROW/ORDER`; only Data.Row assigns that parent edge's status. `ServiceUniverse` remains the sole open Context semantic attachment at `ENV-KEY-INTERP`. |
| 3 | `Effect4.Data.Row` | `DATA-PG-ROW`, required graph | **Closed.** The fixed battery and generated join cover the sole proof-carrying carrier, raw-list normalization boundary, sorted insertion, canonical extensionality, union algebra, subset/weakening, exact owners and hypotheses, 23 theorem/axiom receipts with no choice, eight duplicate-name exclusions, nine counterexamples, all ten graph edges, and five detector reactions. This closes the reusable row algebra only; it deliberately proves no downstream denotational preservation. |
| 4 | `Context.Service` and `Context.Requirement` | local carrier receipts plus nodes in `ENV-PG-CONTEXT` | Reuse `ServiceKey`, `Program`, `Signature`, and `Data.Row`; no second key, row, program, type-code, or order carrier. Prefer a derived `ServiceSignature U` and `request = Program.perform` over a duplicate service program. Make `Requirement` an alias or named view of `Row ServiceKey`. The graph-bearing part is `Program.UsesOnly`: prove its pure, visit, perform, bind-by-union, and weakening laws. Do not claim a finite `Program.requirements` function for arbitrary higher-order continuations; synthesis belongs to checked first-order Flow. |
| 5 | `Context.Environment` | shared `ENV-PG-CONTEXT`, required graph | Freeze environment lookup, right-biased provision/merge, requirement satisfaction, and service discharge relative to one supplied universe. Prove pointwise extensionality, lookup at the same and distinct keys, merge associativity and identities, shadowing, satisfaction for empty/singleton/union, weakening, handler agreement, and total interpretation for `UsesOnly` programs under a satisfying environment. Counterexamples must cover nominal collision, carrier collision, mixed universes, missing lookups, right-biased noncommutativity, hidden defaults, and proof-free casts. |
| 6 | `Layer.Description` plus `Runtime.Scope` representative | separate graph-bearing owners when composition/resource meaning appears | Freeze only after the environment graph closes. Layer then owes identity and associative composition at its declared merge operation, requirement/output accounting, and later memo agreement. Scope then owes acquisition/finalization order and the law that finalization observes state produced before failure. These are graphs; the passive identifier and record leaves beneath them are not. |

### `DATA-PG-ROW` closed theorem spine

The breaker froze the exact signatures and the generated assurance join now
closes this dependency order:

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
