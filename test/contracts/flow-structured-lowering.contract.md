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
| `Effect4.Target.Structured.{wellScoped, wellScopedList, wellScopedCases, GraphClosed, BodyScoped, blockLabels, BreakScopedStatement}` (`StructureLaws.lean`) | label well-scoping of emitted statements, the two hypotheses of the emission law, and the statement of its open half |

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

## Laws (`Effect4/Target/TypeScript/StructureLaws.lean`)

| Theorem | Statement |
| --- | --- |
| `wellScoped`, `wellScopedList`, `wellScopedCases` | label well-scoping of a statement: a `break l` must sit inside a `label l:`, a `continue l` inside an `l: while (true)`; `scopedGen` is a function boundary and resets both scopes |
| `dominates_step`, `dominates_entry` | `Structure.dominates` is the fuel-bounded walk up the `idom` chain: it either stops at the node or continues from its immediate dominator, and nothing but the entry dominates the entry |
| `lt_size_of_transferTarget` | a `break` target is a merge node or a loop header, so it is the target of a declared edge, so it is a node of the graph |
| `emitNode_wellScoped`, `emitWith_wellScoped` | **for any `Shapes = structuredShapes` emission of a closed graph, every `continue l` sits inside its `while l`, and every `break l` names a block label of the graph** (`wellScopedList (blockLabels g) []`). Row `E4-TARGET-CE-013` is exactly the failure of the first half: the theorem needs `emitWith`'s wrapping of a loop-header entry, and is false for the emission without it. Neither reducibility nor the correctness of the dominator computation is used |
| `paramMove_wellScoped`, `lowerBlockWith_wellScoped` | Effect4's own block body introduces no label: it reaches the control transfers only through `transfer` |
| `graphOf_closed` | `Flow.graphOf` keeps every successor inside the node range |
| `structuredBody_wellScoped` | the two hypotheses discharged: **every structured lowering Effect4 emits is `continue`-scoped**, with no assumption left over |
| `BreakScopedStatement` | *the open half, stated exactly*: `wellScopedList [] []` — every `break L<t>` enclosed by its `label L<t>:` |

Axiom receipts: `Effect4Test/Target/TypeScript/StructureLawsAxiomReport.lean`.
Within `propext` and `Quot.sound`, except `lowerBlockWith_wellScoped` and
`structuredBody_wellScoped`, whose *statements* name `Flow.lowerBlockWith` and
`Flow.structuredBody`; those already reach `Classical.choice` through Lean's
UTF-8 folds, and are admitted by exact declaration in
`Effect4Test/Audit/AxiomGate.lean`.

## What `BreakScopedStatement` needs

Discharging it requires two facts about `lean4-typescript` v0.4.1 that Effect4
cannot establish over the package's definitions:

1. `Structure.idom t` lies on the `idom` chain of every predecessor of `t` —
   the correctness of the Cooper–Harvey–Kennedy iteration in `Structure.idoms`;
2. a forward edge's target comes later in `Structure.rpo` than its source, and
   `Structure.children` lists nodes in that order — so the child of `idom t` on
   the path to the source is folded *before* `t`, which is what puts the source
   inside `label L<t>:`.

With (1) and (2) the same induction closes, carrying the block scope
`(children g a).filter (isMerge ∨ isLoopHeader) |>.drop …` instead of the
permissive `blockLabels g`. Until then, executable receipts stand in on the
packet's own flows.

## The agreement statement, exactly

The owed theorem needs a control-flow interpreter for the emitted statement
skeleton. Stated over abstract node bodies, so that no lowering detail enters:

- a *node body* is `step : Nat → Choice → Option Nat` — from a node and the
  decision taken there, the next node, or `none` when the node returns;
- `graphWalk g step fuel start : List Nat` is the node sequence of the graph
  walk, exactly as `Effect4.Flow.loop` produces it;
- `exec : List Stmt → State → List Nat` interprets a statement list with a
  label stack: `labelled l body` pushes a break target, `whileTrue (some l)`
  pushes a continue target, `breakTo (some l)` and `continueTo (some l)`
  unwind to them, and the marker statement a node body emits appends its node;
- the theorem: for a reducible, closed `g` and the marker body
  `body n transfer = some ([marker n] ++ (transfer (step n c)).getD [])`,

  `Structure.emitWith g structuredShapes body = some out →`
  `exec out initial = graphWalk g step (fuelFor …) g.entry`.

Its proof needs (1) and (2) above as well — a `break L<t>` must be shown to
land at `t` — plus the interpreter and its unwinding lemmas. That is the whole
of `structured-agreement`; the well-scoping law above is its first half.

## Acceptance

```text
lake env lean Effect4Test/Target/TypeScript/StructuredLowerContract.lean
lake env lean Effect4Test/Target/TypeScript/StructureLawsContract.lean
lake env lean Effect4Test/Target/TypeScript/StructureLawsAxiomReport.lean
./scripts/check-trace-host.sh
./scripts/check-lowering-property.sh
./scripts/test-lowering-mutations.sh
./scripts/check-lowering-coverage.sh
```

## Amendment: the generic body premise is insufficient, 2026-09-03

`E4-TARGET-CE-018` refutes the quantified `BreakScopedStatement` recorded
above. This is a defect in that open statement. The existing proved
`emitWith_wellScoped` result, with `blockLabels g` as the initial block scope,
remains valid.

The witness is `Effect4Test/Counterexamples/Target/BreakScoped.lean`.
`diamond` has four nodes, with edges from 0 to 1 and 2, from 1 and 2 to 3,
and no outgoing edge from 3. It is closed and reducible. `illicitBody` asks
for `transfer 3` at every node and satisfies the original `BodyScoped`.
The pinned emitter returns a labelled block containing `break L3`, followed
by another `break L3` outside that label. `frozen_statement_false` proves
`¬ Effect4.Target.Structured.BreakScopedStatement`; the emission equation is
checked by kernel reduction.

The two graph facts listed above cannot establish this original statement:
the body may request a transfer for an edge that the graph never declared.
The proposed corrected premise is `BodyScopedOnEdges g body`, stated in the
witness module without changing the production declaration:

```lean
∀ (node : Nat) (transfer : Nat → Option (List Skeleton))
  (blocks loops : List String) (own : List Skeleton),
  (∀ target control, target ∈ g.succs node →
    transfer target = some control →
    Skel.wellScopedList blocks loops control = true) →
  body node transfer = some own →
  Skel.wellScopedList blocks loops own = true
```

`CorrectedBreakScopedStatement` retains the original graph-closedness,
reducibility, successful-emission and empty-initial-scope requirements,
replacing only `BodyScoped body` with `BodyScopedOnEdges g body`. It remains
an unproved obligation. `illicit_body_not_edge_scoped` confirms that the
corrected premise excludes the counterexample.

The actual lowerer satisfies the stronger premise. `skeletonBlockWith_edgeMove`
proves that restricting transfers to `RawTerm.successors` leaves every lowered
block unchanged. `skeletonBlockWith_scoped_on_edges` transports the existing
scoping theorem through that restriction. `actualBody_scoped_on_edges` then
proves the graph-level obligation for every operation table, block list,
entry and interrupt setting. `actualBody_exact` identifies that body with the
one used by `Flow.skeletonBody`; it is an equality by kernel reduction.
These declarations are test receipts for the proposed contract correction,
not a replacement production interface.

The intended full T4 remains open: for every admitted flow that lowers to
both forms, the structured and dispatch skeletons must denote the same
`Program` at `fuelFor`, including merges and loop headers. The current
`skeletonStructured_denote_dispatch` theorem covers flat graphs and requires
`interrupts = false`. Closing the stronger body premise does not remove
either restriction. The proof still needs the graph facts, an account of
where each labelled transfer resumes with its moved parameters, and a
sufficient-fuel argument for structured loops. A structured loop spends fuel
per iteration, while the dispatch form spends it per block, so the current
flat theorem at arbitrary fuel cannot be generalized to loops by dropping
its hypothesis. Interrupt-point denotation remains a separate obligation.

The witness and actual-body receipts were checked using only:

```text
lake env lean Effect4Test/Counterexamples/Target/BreakScoped.lean
```

Every printed theorem receipt uses at most `propext` and `Quot.sound`, with
no `sorryAx`, `Classical.choice` or native-evaluation axiom. This packet changes
no production declaration, emitter, graph algorithm or dependency pin, and
claims no host-boundary or full-T4 closure.
