# Checked cached answers and graph queries

The first slice adapts the upstream reconstruction technique to existing Effect4 carriers.
It keeps `Eff` as the program IR and uses derived data for analysis.
The research prototypes change no production code.
The later prepared-codec slice owns separate paths in the isolated review worktree.

Proof role: proposed tool laws and their research prototypes.
Evidence status: planned, then measured by the commands in the receipt.
Scope: finite dependency analyses, type folds, and selected proof dependencies.

## Acyclic fold answers

Concept: `initial-algebras-folds`.
Proposed claim: `fold-cache-local-agreement`.
Consumer: D6 in `docs/research/2026-10-09-program-graph-design.md`, serving R14.
The statement compares cached answers with `cata_ty` for the same algebra and type.
Each row retains its constructor, payloads and ordered child occurrences.
Every required child appears earlier, and the selected root has an entry.
The cache checks local equations against those exact source rows.
The prototype uses `TyFoldExtras` and its existing constructor views.
It introduces no constructor match maintained separately from that generated view.

Helpers must serve the local-agreement claim or its finite controls.
A second property transports accepted answers to a changed input when the current local equations still hold.
Neither property promises execution speed, typing admission or equality between different programs.
A context-sensitive fold also binds every inherited input that its algebra reads.

## Cyclic dependency answers

Concept: `initial-algebras-folds`, as a tool law for the proof graph.
Proposed claim: `dependency-summary-exact`.
Consumer: the summaries produced by `reachedAxiomsMany` in `tools/ProofGraph/Axioms.lean`.
The observation is membership of a named reachable axiom or stopped planned goal.
The graph is finite extracted dependency data, not another program representation.
Its graph data consists of nodes, local labels and outgoing node references.
Extraction from Lean's environment is a separate adapter boundary.

The certificate must establish both directions of the observation.
Local seeds and outgoing answers must occur in each answer.
Each reported label must also have a descending distance witness to a local seed.
The distance belongs to a node-label pair.
A single decreasing rank for each node would wrongly exclude cycles.

Helpers for the two directions serve `dependency-summary-exact`.
Its consumers include existing axiom and planned-goal reports.
It can support R4, R10 and R14 evidence reports without proving those requirements.
It proves no theorem represented by a graph node.
It certifies neither omitted dependency edges nor an environment with unavailable declaration bodies.
Changing goal tags or the stopping policy changes the input problem.
Budget exhaustion remains an unanswered analysis, never an empty answer.

## Application graph connectedness

Concept: `initial-algebras-folds`, as a tool law for graph views.
Proposed claim: `view-forest-components`.
Consumers: `Graph.layout` and `Run.fiberGraph` in `tools/Tools/View`.
The observation is weak connectedness after selecting original edge occurrences.
The premises require valid endpoints and retain the original node and edge identities.
The full graph remains available for directed reachability and wait-cycle queries.
A smaller visible forest does not retain either observation in general.

A future source connector must say what each graph edge means.
Containment, data dependence, control order, waits and proof dependence remain distinct relations.
They may share checked reachability operations.
They may not silently share an edge relation or a meaning claim.

## Application reachability connector

Concept: `initial-algebras-folds`, as a tool law for graph views.
Proposed claim: `view-reachability-summary-exact`.
Consumers: directed queries for the application graph API, explanations and impact reports.
The connector uses `Tools.View.Flow.Reach` from `tools/Tools/View/FlowLaws.lean`.
Its input is a finite position bound and the existing `Flow.Edge` list.
Each node seeds its own position, and its children are exactly the outgoing edge targets.
Every edge endpoint must lie below the position bound.
The executable adapter refuses an invalid endpoint.

The certificate checker establishes membership exactly when the target is directed-reachable.
Helpers establish the adapter relation and serve that connector or its finite controls.
The existing proof-graph checker supplies both directions of cached-answer correctness.
The connector changes neither the edge direction nor the meaning of `Flow.Reach`.
It proves no scheduler, source admission, layout identity, forest or speed claim.
It serves R14 graph-query evidence without proving that requirement.

## Concrete consumer: prepared JSON codec

The user requests a concrete application of reusable folds to existing functionality.
This slice reuses the `Wire` carrier from `src/Effect4/Schema/Codec.lean`.
It keeps the existing type-directed interpretation and the exact value refusals.

Concept: `exact-codecs`, serving codec exact embedding under `Codec.normJ`.
Existing claims: `decode-encode`, `decode-iff` and `record-codec-layout`.
Requirements: R2 and R3.
Helpers: prepared encoding, decoding and codec-value checks agree with the existing public operations.
Consumers: repeated boundary operations and `harness/truth/schema-codec/Emit.lean`.
The exact observation is each `Option` result, including refusal, and the codec-value Boolean.
The theorem applies to every source type, value and JSON input.

The prepared data retains the normalized source and `wire (layout source.normalize)`.
Its proof fields bind those cached values to the exact source.
Methods receive the prepared data explicitly.
They never bind its table inside a returned closure.
The fold carrier can contain functions; canonical program syntax remains first-order data.

The existing public operations delegate to the shared prepared implementation.
The implementation retains membership checks and exact round-trip checks.
Structural support is a separate judgment and is not a new premise.
No type or value gains codec admission through this change.
The existing exact embedding theorems keep their statements.
Their proofs use the prepared connector or a named equation for the original boundary policy.

The numeric harness prepares once, then uses the same result for decoding and reencoding.
The retained pre-change output is the independent byte-comparison baseline.
Finite controls include literals, overlapping unions, optional fields, invalid numbers and unsupported handles.
A source review checks that repeated methods receive the retained wire interpretation.
A bounded compiler inspection checks their bodies and the harness use pattern.
No elapsed-time speedup is claimed without a separate measurement.

Owned production paths in the isolated worktree:

- `src/Effect4/Schema/Codec.lean`;
- `src/Effect4/Laws/Schema/Codec.lean`;
- `harness/truth/schema-codec/Emit.lean`;
- `Test/Codegen/DataCodec.lean`, extending the existing battery without changing root imports;
- `src/Effect4/Laws/Program/Typed/AnswerSchema.lean`, using the named decoding policy in its existing membership proof.

Research controls remain in this directory.
The primary checkout, owner rulings and root imports remain untouched.
