# Effect4 architecture

## Dependency direction

```text
first-order data and rows
  -> algebra and checked flow
  -> operational/relational semantics
  -> logic and classification
  -> portable protocol and typed targets
  -> host conformance harnesses

Schema ---------> checked values, transforms, target codecs
Context/Service -> requirements and environments
Layer ----------> scoped environment construction
Runtime --------> interpretation and managed ownership
Fiber ----------> scheduler/interruption/resource lifecycle
```

Effect4 has no dependency on Foldlab. Foldlab's later adapter depends on the
public Effect4 algebra and proves compatibility with its existing CAS-specific
types and observations.

## Planned source tree

| Area | Public responsibility |
| --- | --- |
| `Effect4/Algebra` | indexed signatures, free programs, handlers, interpreters, morphisms and laws |
| `Effect4/Data` | finite rows, IDs, canonical forms, typed values and shared codecs |
| `Effect4/Flow` | raw and checked first-order graphs, blocks, regions, decisions and admission |
| `Effect4/Semantics` | cause/exit, configurations, steps, runs, approximations, observations and logic |
| `Effect4/Schema` | decoded/encoded/representation types, codecs, refinements, transformations and portability |
| `Effect4/Context` | stable keys, service requirements and environments |
| `Effect4/Layer` | dependency graphs, acquisition, provision, composition and scoped release |
| `Effect4/Runtime` | interpreters, scopes, managed runtimes and execution boundaries |
| `Effect4/Concurrency` | fibers, scheduling, interruption, races and supervision |
| `Effect4/Stateful` | Ref, Deferred, Queue and coordination primitives |
| `Effect4/Channel` | Channel/Stream/Sink/Pull/Take calculi and embeddings |
| `Effect4/Schedule` | pure recurrence descriptions and effectful stepping boundaries |
| `Effect4/Transaction` | atomic read/write/retry/orElse/commit calculus |
| `Effect4/Classification` | independent domains, concretizations, transfers, products and fixpoints |
| `Effect4/Protocol` | portable IDs, profile admission and canonical protocol bytes |
| `Effect4/Target/TypeScript` | typed target IR, lowering, rendering, decoding, simulation and Effect v4 profile |
| `Effect4/Meta` | environment extensions, declaration introspection, derivation and deterministic emitters |
| `Effect4/Audit` | axiom receipts, declaration snapshots, per-type closure and cutover refusal |

Tests mirror these areas under `Effect4Test/`. Durable attacks live under
`Effect4Test/Counterexamples/`, while their stable registry and algebraic
contracts live under `test/`.

## Public API principles

The public API exposes small semantic objects and strong composition:

- operations are indexed by their answer type;
- programs are abstract behind constructors and folds;
- handlers expose interpretation and composition laws, not representation;
- checked graphs expose erasure and certified observations, not unchecked
  internal tables;
- Schema exposes both encoded and decoded views and the laws connecting them;
- services expose keys and requirements, while layers own construction and
  cleanup;
- runtimes eliminate effect programs but never become canonical program data;
- metaprogramming emits first-order declarations and digests, never stores raw
  `Lean.Expr` as semantic content.

## Observation faces

The library keeps four faces distinct:

1. structural syntax for induction and construction;
2. first-order checked flow for identity, cycles, sharing, and generation;
3. relational big-step/small-step meaning for arbitrary choices;
4. executable bounded runners and host harnesses for decidable evidence.

Theorems relate these faces explicitly. No bounded runner is promoted into the
denotation merely because it executes.
