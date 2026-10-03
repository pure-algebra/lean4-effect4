# Structural target types for data

Base: `80accbbd`.
Files: `src/Effect4/Codegen/Types.lean` and focused target type fixtures.

The record wrapper needs the pinned TypeScript printer's structural object type and optional field flag.
The same projection covers readonly tuples, string-keyed maps, null, undefined, numbers and bytes.
A map key must normalize to string.
Unresolved type parameters and nominal applications with arguments remain refusals.
A nullary application retains its existing normalization to a legacy handle.
The projection retains its existing normalization step.
Raw formation remains the separate public admission check from decisions rows 192 and 193.

Concept: Exact Codecs & Data Plane Embeddings.
Consumer: the record print/read wrapper and checked declaration emission.
Role: target type projection, not an exact embedding.
Observation: the projected structural type and its rendered text.
Scope: supported normalized data types under rows 125, 164, 195 and 196.
Numeric types can share the target's number spelling.
This projection establishes no value membership, codec admission or target execution property.
Requirement: R2 and R3.
The existing `ofTy_normalize` theorem remains the connector for normalization.

Narrow Lean builds and rendering fixtures check the implementation.
Pinned tsgo 7 checks representative target assignments and rejected alternatives.
