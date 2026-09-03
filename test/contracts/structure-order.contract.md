# Contract: structured order and conditional break scoping

Independent breaker continuation of `E4-TARGET-CE-018`, frozen 2026-09-03.
The production owner is the new module
`Effect4/Target/TypeScript/StructureOrder.lean`, importing `StructureLaws`.
Namespace: `Effect4.Target.Structured`. The pinned graph algorithms remain
`lean4-typescript` at `cc62799055b1af7ce22b083afcfb30155c1ed4d0`.

## Public declaration and ownership record

| Name | Required meaning and disposition |
| --- | --- |
| `rpo_nodup` | For every graph, computed reverse postorder has no duplicate node. Native derived theorem over `TypeScript.Structure.rpo`. |
| `rpo_index_order` | For every graph, computed reverse postorder is pairwise strictly increasing under `Structure.index`. Native derived theorem over the existing order/index definitions. |
| `children_index_order` | The same strict order for every graph and dominator-tree child list. Native derived theorem over `Structure.children`. |
| `BodyScopedOnEdges` | Native derived predicate over the existing graph, skeleton and scoping judgment. It is definitionally the corrected CE-018 test predicate; the original test witness retains its owner. |
| `DominatorFacts` | Native proof-premise record over `Structure.Graph`, containing exactly `childIndex` and `forwardJoinParent` below. It adds no graph carrier or algorithm. Constructors/projections inherit this record. |
| `emitWith_wellScoped_of_dominators` | General conditional empty-initial-scope theorem for the existing skeleton emitter, using the corrected body premise and explicit graph facts. Native derived theorem. |
| `skeletonBody_wellScoped_of_dominators` | General conditional theorem for the actual `Flow.skeletonBody`, all tables, block lists, entries and interrupt settings. Native derived theorem. |

All names have one owner, `StructureOrder`; their duplication relationship is
`derived` over the existing owners named above. `Graph`, `Skeleton`, the graph
algorithms, emitters and `Skel.wellScopedList` are reused unchanged. This packet
does not promote the CE-018 test helpers into a second public lowering API.
Traversal, placement, outer-scope and actual-body helpers remain private.

The mandatory assurance route is `docs/TRACE-DAG.md`, `structured-agreement`.
These declarations contribute order and conditional lexical-scope receipts to
that existing route; they do not close the whole route. The exact public
ascriptions, including constructor and field types, are in
`Effect4Test/Target/TypeScript/StructureOrderContract.lean`.

## Premises and conclusion

`BodyScopedOnEdges g body` says: for every node, transfer callback, outer block
and loop labels, and successfully emitted body, the body is well scoped if
every successful transfer along that node's declared successor edges is well
scoped. An undeclared transfer cannot borrow a scoping guarantee. The predicate
must be definitionally identical to the corrected predicate in the unchanged
`Effect4Test/Counterexamples/Target/BreakScoped.lean`.

`DominatorFacts g` contains exactly:

- `childIndex`: `idom g child = some parent` implies
  `index g parent ≤ index g child`, for every parent and child.
- `forwardJoinParent`: every declared forward edge to a merge or loop-header
  target has a computed immediate-dominator parent that dominates the source.
  The premise uses the existing computed `isBackEdge`, `idom` and `dominates`.

The general theorem quantifies over every graph, body and output. It assumes
`GraphClosed g`, source boundedness
`∀ source target, target ∈ g.succs source → source < g.size`, `DominatorFacts g`,
`BodyScopedOnEdges g body`, and successful `Structuring.emitWith` output. Its
conclusion is `Skel.wellScopedList [] [] out = true`, including both break and
continue binding. Successful emission already entails the emitter's existing
reducibility guard; this is not an additional algorithm or an assumed output
well-scoping fact.

The actual-lowerer theorem accepts every operation table, interrupt flag, raw
block list and entry. Its only semantic graph premise is
`DominatorFacts (Flow.graphOf blocks entry)`; given successful
`Flow.skeletonBody`, the same empty-scope conclusion follows. It may not add
flatness, admission, label-free, merge-free, loop-free or `interrupts = false`
restrictions. The block body must be the actual lowering with its parameter
moves, not a marker fixture substituted for it.

## Red battery and controls

The retained CE-018 kernel witness proves that the original `BreakScopedStatement`
is false. The new battery preserves its illicit emission and rejects
`illicitBody` under the new predicate. It transports the existing universal
actual-body receipt to the new predicate, testing that the correction admits
the actual lowerer for all inputs while rejecting the counterexample.

Finite controls cover the diamond's reverse-postorder and child order and the
real swap-loop skeleton with parameter moves and both interrupt settings. A
single-node graph has explicit proofs of both graph-premise fields and a
successful emission, establishing an inhabited premise domain. The constructor
ascription excludes additional hidden fields. General theorem ascriptions
separately require all graphs/bodies; finite controls do not replace them.

Before production exists, narrow scratch controls replace only the missing
module import and remove the marked `ORDER-SURFACE` section. They must pass.
A red copy replaces only the import and must reach the missing public names.
A mutant that declares the old orphan-break output well scoped must fail at
that exact expected result; restoring the control must pass again. A missing
module error alone is not declaration-red evidence.

## Open obligations and acceptance

No theorem here establishes `DominatorFacts` for every reducible graph or for
every computed `Flow.graphOf`. Correctness of the pinned immediate-dominator
computation remains open. The original unqualified corrected-break statement
therefore remains open; the old false statement remains refuted.

Full T4 also remains open: lexical label scope alone does not prove that each
transfer resumes at the correct node with correctly moved parameters, nor that
structured and dispatch skeletons denote the same `Program`. Merges, loop
fuel accounting, the general structured/dispatch relation and interrupt-point
denotation retain their separate obligations. The `interrupts = true` scoping
result closes no interrupt denotation claim. Host behavior remains executable
evidence only. Existing algorithms, lowering bytes and frozen old packets stay
unchanged.

Coordinator acceptance, sequentially after the module exists:

```text
lake build Effect4.Target.TypeScript.StructureOrder
lake env lean Effect4Test/Target/TypeScript/StructureOrderContract.lean
lake env lean Effect4Test/Target/TypeScript/StructureOrderAxiomReport.lean
```

Every public declaration receipt must stay within `propext` and `Quot.sound`;
no `sorryAx`, `Classical.choice`, `native_decide` or new axioms. The breaker
runs narrow Lean only; root imports, known-red entries, package builds and
proof-graph status updates are coordinator-owned.

### Breaker receipt, 2026-09-03

Verified before production exists, at
`a245fd2ebf0744641a46f73f820aaf479154f760`. Scratch copies are in
`/private/tmp/structure-order-breaker.os_34_v2`; their transformations are
specified above.

| Command | Observed result |
| --- | --- |
| `lake env lean /private/tmp/structure-order-breaker.os_34_v2/Controls.lean` | Exit 0: six guards, the preserved illicit and terminal emission equations, and both concrete graph-premise proofs pass. |
| `lake env lean /private/tmp/structure-order-breaker.os_34_v2/OrphanBreakMutant.lean` | Exit 1 only at the changed guard claiming the orphan-break output is scoped. |
| `lake env lean /private/tmp/structure-order-breaker.os_34_v2/Controls.lean` (restored) | Exit 0 again. |
| `lake env lean /private/tmp/structure-order-breaker.os_34_v2/Red.lean` | Exit 1 at the seven missing public names, generated constructor/projections and references to those same names; no control errors. |
| `lake env lean /private/tmp/structure-order-breaker.os_34_v2/AxiomsRed.lean` | Exit 1 at precisely the seven expected unknown constants. |
| `lake env lean Effect4Test/Target/TypeScript/StructureOrderContract.lean` | Exit 1: missing `StructureOrder.olean`, recorded separately from declaration-red evidence. |
| `lake env lean Effect4Test/Target/TypeScript/StructureOrderAxiomReport.lean` | Exit 1: same missing module. |

No production code, prior packet or CE-018 witness was changed. No package
build or host check ran. The coordination claim is append-only and remains
coordinator-owned for its commit; the breaker commit contains these three new
packet files only.

### Proof-only trust amendment, 2026-09-03

The coordinator's full trust self-test rejected the concrete
`terminal_childIndex` helper because its original simplification proof reached
`Classical.choice`. That rejection was independent of the seven production
receipts, which already met the frozen ceiling. The breaker replaces only this
helper's proof body: split the child into zero and successor cases, reduce its
impossible parent premise to `none = some parent`, then eliminate that equality
directly. Its statement, terminal graph, accepted domain, all controls and every
public ascription remain byte-identical. Production, the trust gate and its
allowlist are unchanged. The computed packet needs no repair.

Verified against base `f7cd8a18a93e35b846d84c926cf67e14b02db0cb` in
`/private/tmp/structure-packet-trust.ZshdVG`:

| Command | Observed result |
| --- | --- |
| `lake env lean -o .lake/build/lib/lean/Effect4Test/Target/TypeScript/StructureOrderContract.olean Effect4Test/Target/TypeScript/StructureOrderContract.lean` | Exit 0: saved packet and all unchanged controls pass; this is one module compilation, not a package build. |
| `lake env lean /private/tmp/structure-packet-trust.ZshdVG/Audit.lean` | Exit 0 after fresh compilation: all 25 constants owned by the order, computed and RegionTotal test modules, including private helpers and generated auxiliaries, use at most `propext` and `Quot.sound`. Both terminal premise proofs and `diamond_sourceBounded` use only `propext`. |
| `lake env lean /private/tmp/structure-packet-trust.ZshdVG/Control.lean` | Exit 0: unchanged full order packet plus a helper-specific axiom check. |
| `lake env lean /private/tmp/structure-packet-trust.ZshdVG/OriginalProofMutant.lean` | Exit 1 only at that check: restoring the original proof reaches `Classical.choice`; the packet itself still elaborates. |
| `lake env lean /private/tmp/structure-packet-trust.ZshdVG/Control.lean` (restored) | Exit 0 again, with helper receipt `[propext]`. |
| `lake env lean Effect4Test/Target/TypeScript/StructureComputedContract.lean` | Exit 0, unchanged packet. |
| `lake env lean Effect4Test/Target/TypeScript/StructureOrderAxiomReport.lean` | Exit 0: all seven production receipts remain within the frozen ceiling. |
| `lake env lean Effect4Test/Target/TypeScript/StructureComputedAxiomReport.lean` | Exit 0: all four production receipts remain within the frozen ceiling. |

The scratch audit selects constants by their actual owning module, so private
concrete-premise proofs are included. The before-repair audit rejected the old
compiled helper at the same axiom. The positive/mutant/restored source checks
separately establish that the detector responds to the changed proof body.
Only this amendment and the single helper proof are committed; shared
coordination and the full trust self-test rerun remain coordinator-owned. No
semantic obligation or host boundary changes through this repair.
