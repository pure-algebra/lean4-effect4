# TypeScript reader preparation

Base: `f188fce3`. This slice prepares the pinned 0.7.0 target forms for record operations.
It updates `ts/eff/read.ts` and adds focused parser fixtures.

The parser adapter retains optional object type fields, literal and union type arguments, tuples, element access and object spreads.
It keeps plain, quoted and computed object keys distinct.
It refuses mixed key forms, methods, getters, shorthand fields and optional access.
These forms do not bypass the existing Eff and term readers.
The record slices add their semantic reading rules with the corresponding Lean proofs.

Concept: Exact Codecs & Data Plane Embeddings.
Consumer: record print/read reconstruction and the `type-metadata-exact` claim's target fixtures.
Role: finite parser controls, not a new theorem.
Reach: the pinned `oxc-parser` output and the structural forms printed by `lean4-typescript` 0.7.0.
Observation: the retained target expression and each refusal.
Exclusions: no source typing, target execution theorem or foreign-program admission follows from parsing.
Requirements: R2 and R3; decisions rows 195 and 196.

Verification uses focused Bun tests, the existing reader tests and pinned tsgo 7.
Each new form has a refused alternative and an accepted structural example.
