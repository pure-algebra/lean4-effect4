# Effect TypeScript semantics

This reference pack prepares carefully bounded formal semantics for selected public behavior of the Effect TypeScript project. Its long-term purpose is to support tooling for robust and higher-order verified data structures.

The project treats four layers as distinct:

1. the pinned Effect public source surface;
2. a library-owned semantic model and its Lean proofs;
3. emitted JavaScript under a pinned TypeScript or Effect tsgo configuration; and
4. execution in a named JavaScript engine and host.

The separate [Schema JSON reference context](../schema-json/README.md) inventories a possible proving-ground area. This organization pass does not select its semantic subset or establish claims about Effect internals, performance, scheduling, TypeScript soundness, JavaScript engine correctness, or JSON Schema conformance.

## Resource index

- [Context vocabulary](CONTEXT.md)
- [Claim-gate vocabulary](CLAIM-GATES.md)
- [Implementation plan](IMPLEMENTATION-PLAN.md)
- [Source provenance](../provenance/README.md)
- [Reference catalog](../../.reference/catalog/REFERENCES.md)
- [Effect module surface](../../.reference/catalog/EFFECT-SURFACE.md)

The repository's existing agent and Lean-skill setup is intentionally unchanged.
