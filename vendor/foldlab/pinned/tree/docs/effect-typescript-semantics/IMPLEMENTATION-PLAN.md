# Implementation plan

Status: organizational sequence only; semantic scope not selected  
Prepared: 2026-08-24

This plan describes the order in which a future implementation should establish ownership, types, proofs, and external seams. It does not choose Effect features, Schema constructors, JSON behavior, theorem statements, compiler targets, or hosted runtimes.

Every phase is governed by the global [development invariants](../DEVELOPMENT-INVARIANTS.md) and the generic [claim gates](CLAIM-GATES.md).

## Phase 0 — keep the reference corpus coherent

Deliverables:

- manifest.json and MANIFEST.md agree;
- every listed document exists;
- local Markdown links resolve;
- each canonical term has one owning CONTEXT.md;
- each source pin has one owner in provenance/sources.lock.json; and
- source inventories remain distinct from accepted domain decisions.

Completion gate:

- the manifest validation checks pass and no agent-bootstrap file is changed.

## Phase 1 — establish source provenance

Deliverables:

- project-owned provenance types;
- a resolver interface that returns a verified Resolved Evidence or typed failure;
- adapters only for genuinely distinct resolution mechanisms;
- immutable source-lock entries; and
- reproducible resolution receipts.

Completion gate:

- full commit, tree, blob, SHA-256, and byte-length identities verify for every source used by the next phase.

## Phase 2 — record a domain decision

This phase belongs to future domain work. It must produce a reviewed domain contract without borrowing implementation types as semantic definitions.

Required outputs:

- canonical terms and observables;
- positive, negative, boundary, and counterexample scenarios;
- accepted and rejected source forms;
- equality, refinement, and failure meanings;
- trust assumptions; and
- a dependency-ordered declaration and obligation ledger.

Completion gate:

- the decision is explicit enough to falsify and has not been inferred from this reference organization.

## Phase 3 — define the project-owned formal core

Deliverables:

- algebraic carriers and constructors;
- well-formedness and typing judgments;
- pure operations or explicit relations;
- typed results and failures;
- explicit state, environment, nondeterminism, or divergence when required; and
- no unvalidated external type at the semantic interface.

Completion gate:

- definitions elaborate under one pinned Lean toolchain and every public constructor and operation has a named invariant.

## Phase 4 — state and prove soundness obligations

Deliverables:

- construction soundness;
- invariant preservation;
- typing soundness where a typing judgment exists;
- totality/progress or explicit partiality;
- determinism or explicit nondeterminism;
- coherence, equivalence, or refinement as required by the domain decision; and
- recorded axiom and trust reports.

Completion gate:

- every use of sound, type safe, equivalent, verified, or semantics preserving points to an exact theorem and relation.

## Phase 5 — add boundary translations and adapters

Deliverables:

- raw external representations;
- checked translations into project-owned types;
- typed rejections;
- explicit external seams;
- separate adapters for production and local verification only when both are real; and
- translation-preservation obligations.

Completion gate:

- the formal core remains pure and independent of external implementation layout.

## Phase 6 — add conformance evidence

Deliverables:

- pinned implementation, compiler, runtime, and test-corpus identities as needed;
- normalized observation types;
- reproducible fixtures and receipts;
- supported, unsupported, disputed, and infrastructure-error outcomes kept distinct; and
- no promotion from sampled agreement to universal proof.

Completion gate:

- evidence states its highest satisfied claim gate and all stronger claims remain visibly pending.

## Phase 7 — promote a public module

A module becomes public only when:

- its interface is smaller than the complexity it hides;
- its project-owned types and invariants are stable;
- tests and proofs cross the same interface seam;
- its source and trust dependencies are reproducible;
- its claims match its completed gates; and
- its manifest, context, and maintenance triggers are current.
