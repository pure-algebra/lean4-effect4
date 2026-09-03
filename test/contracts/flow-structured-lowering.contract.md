# Contract: the structured form (P-T9b)

Light ceremony by operator ruling D2. Ruling R7: the dispatch form is the
default for every admitted graph; the structured form is an optimization
behind a reducibility check that must agree with it on every trace. Requires
lean4-typescript v0.4.1 (`TypeScript/Structure.lean`).

## Frozen surface

| Name | Shape |
| --- | --- |
| `TypeScript.Structure.{Graph, rpo, idom, dominates, reducible, isLoopHeader, isMerge, Shapes, emitWith}` | reverse postorder, Cooper–Harvey–Kennedy dominators, reducibility (every backward edge's target dominates its source), emission over the dominator tree |
| `Effect4.Target.EffectV4.structuredShapes` | the four shapes as tagged rules: `structured-loop`, `structured-merge`, `structured-continue`, `structured-break` |
| `Flow.graphOf`, `Flow.reducible`, `Flow.lowerStructured`, `Flow.lowerBest`, `Flow.structuredRuleSet` | plain flows; `lowerBest` falls back to the dispatch form (`dispatch-fallback`) |
| `Region.lowerStructured`, `Region.lowerBest` | region flows: each region's blocks are a graph of their own |
| `structuredModules?` | the structured module over the same families as `regionModules?` |
| `Flow.lowerBlockWith`, `Flow.dispatchTransfer` (`FlowLower.lean`) | a block body parametric in its control transfer; the dispatch form is unchanged byte for byte |

## Shape pinned

- A merge node or loop header `m` is laid out after the node that dominates it:
  `L<m>: { … everything emitted before … }` then `m`'s body, a loop header as
  `W<m>: while (true) { … }`; a forward transfer to it is `break L<m>`, a
  backward transfer `continue W<m>`; a single-predecessor successor is inlined
  at its use; an entry that is a loop header is wrapped in its loop.
- An irreducible graph (a cycle entered at two blocks; admitted because every
  cycle chooses) keeps the dispatch form.

## Evidence

- Every flow golden runs on the host against `structured-fixture.ts` as well as
  `flow-fixture.ts` (`scripts/check-trace-host.sh`, receipts under
  `harness/trace/receipts/structured/`); the property corpus runs against
  `property-structured-fixture.ts` as well (`scripts/check-lowering-property.sh`);
  a fourth planted mutant turns a `continue` into a `break`.
- `Effect4Test/Target/TypeScript/StructuredLowerContract.lean`: the swap loop
  byte for byte, the irreducible fallback, a label-free chain.
- Owed: a Lean theorem that the structured and dispatch forms agree on every
  flow (`docs/TRACE-DAG.md`, `structured-agreement`, `required-open`); the
  host evidence stands in for it on the harness and the corpus.

## Acceptance

```text
lake env lean Effect4Test/Target/TypeScript/StructuredLowerContract.lean
./scripts/check-trace-host.sh
./scripts/check-lowering-property.sh
./scripts/test-lowering-mutations.sh
./scripts/check-lowering-coverage.sh
```
