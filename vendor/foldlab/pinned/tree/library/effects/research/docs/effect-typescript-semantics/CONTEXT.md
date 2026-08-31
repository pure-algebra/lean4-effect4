# Effect Language Semantics

This context names the semantic layers and claim strengths used when relating selected Effect TypeScript behavior to a library-owned formal model.

## Language

**Subject Source**:
The pinned public Effect source selected as implementation evidence.
_Avoid_: Effect itself, upstream

**Semantic Model**:
The library-owned carriers, judgments, operations, and observations whose properties may be proved in Lean.
_Avoid_: Formalized Effect, verified implementation

**Semantic Layer**:
One separately interpreted stage: Subject Source, Semantic Model, emitted JavaScript, or named hosted execution.
_Avoid_: Stack, whole system

**Observation**:
A declared result, failure, event, or trace element used to compare behavior at a Semantic Layer.
_Avoid_: Output, behavior

**Bridge**:
A typed translation or relation between two Semantic Layers.
_Avoid_: Mapping, converter

**Claim Gate**:
The evidence threshold that permits one precisely worded public claim.
_Avoid_: Confidence level, completion percentage

**Model Claim**:
A statement established only for the Semantic Model.
_Avoid_: Effect theorem, verified Effect

**Conformance Observation**:
A reproducible comparison between normalized observations from a pinned implementation and the Semantic Model.
_Avoid_: Conformance proof, equivalence proof

**Compilation Preservation**:
A proved or separately validated relation between admitted source behavior and emitted JavaScript behavior under one pinned compiler configuration.
_Avoid_: Compiles cleanly, type safe

**Hosted Execution Claim**:
A claim that names the JavaScript engine, host, version, platform, and observable host behavior it covers.
_Avoid_: Runtime correctness, works in JavaScript
