# Classification slice — dependency DAG

Status: drafted 2026-08-31. Owns the build order for `PLAN.md` phase P9 and
broad-before-deep item 8, "one independent may/must domain".

Claimed by Claude in `COORDINATION.md`. Follows the discipline of
`docs/ENVIRONMENT-DAG.md` and `docs/WIRE-DAG.md`: every node names its fence,
every edge names the declarations that cross it, receipts are
coordinator-owned, and a layer's contract freezes before that layer is
dispatched.

## Why now

`PLAN.md` requires that "every major category receives a frozen representative
contract before one category is developed far beyond the others". Schema is
closed through its payload carrier and the environment slice is three layers
in, while all five Classification modules are still empty. This slice exists to
restore that balance, not to develop P9 deeply.

## Node status — five empty stubs, zero declarations

```text
Classification/Domain.lean      Classification/Transfer.lean
Classification/Soundness.lean   Classification/Product.lean
Classification/Fixpoint.lean
```

## The inbound edge, checked rather than assumed

The previous two DAGs each asserted an inbound edge that did not hold. Both are
checked here before being drawn.

- **`Effect4/Flow/**` is real.** `Flow/Admission.lean` has 24 declarations,
  `Flow/Raw.lean` 15, `Flow/Block.lean` 8, and the graph carries
  `P4-FLOW-SEMANTICS-CLOSED`. This is a usable provider.
- **`Effect4/Semantics/**` is NOT.** All ten modules — `Step`, `Runs`,
  `Configuration`, `Observation`, `Frontier`, `Exit`, `Cause`, `Logic`,
  `Approximation`, `Equivalence` — declare nothing. Any edge from Semantics is
  unavailable.

That second fact decides the slice's shape. A classification is normally stated
over an execution semantics, and this repository has none yet. So this slice
must be stated over the **checked flow graph** that P4 closed, and it must not
claim anything about runs, observations, or frontiers, because no carrier for
those exists to quantify over.

```text
        Effect4/Flow/**  (P4 closed: Raw, Block, Admission)
                        │
                        ▼
              C0  Classification/Domain
                  (one abstract domain: carrier, order,
                   concretization into flow-graph facts)
                        │
          ┌─────────────┴─────────────┐
          ▼                           ▼
   C1 Classification/Transfer   C2 Classification/Soundness
   (may/must transfer over      (concretization statement
    the checked graph)           for THIS domain only)
          │                           │
          └─────────────┬─────────────┘
                        ▼
              C3 Classification/Fixpoint
                        │
                        ▼
              C4 Classification/Product
```

## Layers

| Layer | Nodes | Parallel builders |
| --- | --- | --- |
| C0 | `Domain` | 1 |
| C1 | `Transfer`, `Soundness` | 2 |
| C2 | `Fixpoint` | 1 |
| C3 | `Product` | 1 |

## Edge contents

Named as **instances a consumer will synthesize**, not as mathematical content
— the `Key → Requirement` edge in the environment slice was corrected three
times because it was written the other way.

| Edge | What crosses |
| --- | --- |
| `Flow → Domain` | the checked-flow carrier and its decidable equality; whatever `Flow/Admission.lean` exports as the admitted-graph type. The domain concretizes **into facts about that carrier**, so this edge fixes what a fact even is. |
| `Domain → Transfer` | the domain carrier, its order, and the decidability instances a transfer function needs to compute |
| `Domain → Soundness` | the concretization function and the order; the statement quantifies over both |
| `Transfer + Soundness → Fixpoint` | the transfer function and the per-step statement the iteration must preserve |
| `Fixpoint → Product` | the fixpoint operator and its termination or bound argument |

## Non-edges

- **`Effect4/Semantics/**` does not gate this slice**, because it cannot —
  every module there is empty. Any claim phrased over runs, steps,
  observations, or frontiers is out of scope until those carriers exist.
- **The Schema and Environment slices do not gate this slice.** No node here
  needs a codec, a key, or a row.
- **`Product` does not gate `Fixpoint`.** They are ordered the other way. The
  exit gate forbids "unjustified whole-product invariance", which is a
  statement *about* a product of independently-sound domains — so the product
  must come last, after each factor has its own statement.

## The word this slice may not use loosely

`AGENTS.md` forbids "sound" without naming the exact judgment, observation,
theorem or gate, assumptions, and remaining host boundary. One of these modules
is *called* `Soundness.lean`, so the packet must define precisely what it
claims and against what. `PLAN.md` states the exit gate as "concretization
soundness per domain; no unjustified whole-product invariance", which is
already the shape of the constraint: the claim is **per domain**, it is about
**concretization**, and generalising it across a product is exactly the thing
named as unjustified.

A packet here that says "the domain is sound" without naming the concretization
and the judgment has not stated an obligation.

## Open questions — settle before C0 freezes

1. **What is a fact?** The domain concretizes into something. Over a checked
   flow graph the candidates are: a set of admitted graphs, a predicate on
   nodes, or a predicate on edges. The choice decides what `Transfer` can
   even be a function of.
2. **May or must, or both?** Item 8 says "one independent may/must domain".
   Decide whether one carrier holds both readings, or whether may and must are
   two concretizations of one lattice. Two concretizations of one carrier is
   the cheaper design and makes the independence claim sharper; say which and
   what it gives up.
3. **Does the order need to be a lattice, or a preorder with joins?** Only what
   `Fixpoint` actually consumes should be demanded at C0. Demanding a full
   lattice up front is the classic way to make a domain unimplementable for a
   consumer that only needed joins.
4. **Termination of the fixpoint.** `AGENTS.md` requires that fuel exhaustion
   is a live frontier, never a typed error. A fixpoint iterated to a bound must
   state its frontier separately from any refusal, or prove ascent terminates
   on a finite height. Finite height is the cleaner answer if the domain admits
   one — say so at C0, since the domain's shape decides it.

## Fences

| Fence | Files |
| --- | --- |
| F-DOMAIN | `Effect4/Classification/Domain.lean` |
| F-TRANSFER | `Effect4/Classification/Transfer.lean` |
| F-SOUND | `Effect4/Classification/Soundness.lean` |
| F-FIXPOINT | `Effect4/Classification/Fixpoint.lean` |
| F-PRODUCT | `Effect4/Classification/Product.lean` |

`Effect4Test/Classification/AxiomReport.lean` is coordinator-owned and in no
builder's fence.
