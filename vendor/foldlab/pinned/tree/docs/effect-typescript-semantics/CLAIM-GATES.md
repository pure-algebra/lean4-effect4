# Claim gates

Status: reference gate vocabulary, not a selected project scope  
Snapshot: 2026-08-24

## Project thesis

Effect Schema is not treated as a loose collection of validators. At the pinned source revision, every public Schema carries a runtime SchemaAST.AST together with decoded Type and encoded Encoded views and their service requirements. The AST is a discriminated algebraic family whose nodes share annotations, checks, encoding links, and parsing context. It is the central representation used to construct expressive domain models and to drive parsing, encoding, inspection, transformation, arbitrary generation, equivalence, formatting, representation, and JSON Schema work.

“Algebraic” here means that the source representation is a tagged sum of node variants with structured products and recursive children. “Valid” is not inferred from the TypeScript shape. Any future formalization must define and prove the well-formedness, invariants, and laws it needs. No existing algebraic law, completeness result, or correspondence theorem is assumed merely because the runtime AST exists.

Pinned source: [SchemaAST.ts](https://github.com/Effect-TS/effect/blob/0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07/packages/effect/src/SchemaAST.ts).

Canonical terms are owned by the [Effect Language Semantics context](CONTEXT.md), the [Schema JSON Codec context](../schema-json/CONTEXT.md), and the [Source Provenance context](../provenance/CONTEXT.md).

## Required declaration shapes

The formal model should make the following families visible rather than hiding them in prose:

- carriers, constructors, and inductive well-formedness judgments;
- relations, preorders, equivalences, refinement, and deliberately separate subtyping judgments;
- operation signatures, preconditions, configurations, transitions, results, and typed failures;
- normalization and elaboration functions plus their observable outputs;
- equations, coherence conditions, algebraic laws, preservation statements, and trace properties; and
- explicit translation and conformance relations between source, model, compiled output, and hosted execution.

## Claim ladder

| Gate | Permitted public claim | Evidence required |
| --- | --- | --- |
| G0 Source identity | These exact bytes were selected as evidence. | Full commit, tree, blob, SHA-256, size, path, and a reproducible resolution receipt. |
| G1 Model | A theorem holds for the Lean definitions. | Kernel-checked theorem, pinned toolchain, imports, and axiom report. |
| G2 Specification | The model implements this cited project contract. | Requirement traceability, examples, counterexamples, reviewed quantifiers, and declared observables. |
| G3 Extraction | An admitted pinned source fragment translates to the model. | Accepted-source judgment, defined translation, and preservation or reflection theorem. |
| G4 Implementation conformance | A pinned Effect build agrees with the model on the stated domain and observations. | Reproducible differential and conformance results; sampled tests remain sampled evidence. |
| G5 Compilation preservation | Emitted JavaScript refines the source/model semantics. | Pinned compiler, configuration, source/target semantics, and a proved or separately validated translation. |
| G6 Hosted execution | A named engine and host preserve the modeled observations. | Engine and host versions, host contracts, platform assumptions, and runtime evidence or proof. |

Each artifact must state its highest satisfied gate. Passing a later test does not silently promote an earlier proof.

## Organization state

No project claim or accepted semantic scope is selected by this reference organization. A future domain decision may adopt one gate only after its required evidence and counterexamples are recorded.
