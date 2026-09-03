# Contract: computed dominator facts and strict lexical scoping

Independent breaker continuation of `structure-order.contract.md` and
`E4-TARGET-CE-018`, frozen 2026-09-03. The new production module is
`Effect4/Target/TypeScript/StructureDominators.lean`, importing the existing
`StructureOrder`. Its namespace is `Effect4.Target.Structured`.

The subject is the actual `TypeScript.Structure` algorithm in
`lean4-typescript` at `cc62799055b1af7ce22b083afcfb30155c1ed4d0`.
`Structure.idoms`, `idom`, `rpo`, `index`, `dominates` and `reducible` keep their
existing definitions and exact fuel. The new module must not replace these
with an assumed table, a different algorithm, a graph carrying proof fields,
or a success-only finite fixture. The earlier packet and production
`StructureOrder` stay unchanged.

The inspected pinned source is
`.lake/packages/typescript/TypeScript/Structure.lean:74` (`idoms`), `:114`
(`idom`), `:122` (`dominates`) and `:132` (`reducible`), SHA-256
`54631186594e0f03608fe400f1e1238d2b208e528030f64c25fbbbbee345b948`.

## Public declaration and existing-type record

Exactly four public declarations are frozen. Each is native Effect4 proof
work, with duplication relationship `derived` over the existing owners below;
`StructureDominators` is their unique new declaration owner.

| Name | Meaning and related canonical owner |
| --- | --- |
| `idom_index_le` | For every raw `Structure.Graph`, computed `idom g child = some parent` implies `Structure.index g parent ≤ Structure.index g child`. No closure, reducibility, reachability, valid-entry, or convergence premise. |
| `computed_dominatorFacts` | For every target-closed, source-bounded graph that passes the existing `Structure.reducible` check, derive the existing `DominatorFacts` record owned by `StructureOrder`, including both fields, from actual computation. |
| `emitWith_wellScoped_computed` | Derive strict `Skel.wellScopedList [] []` for every successful existing `Structuring.emitWith` result from target closure, source boundedness and existing `BodyScopedOnEdges`; no supplied dominator premise. |
| `skeletonBody_wellScoped_computed` | For all operation tables, interrupt flags, raw block lists and entries, successful actual `Flow.skeletonBody` emission implies strict empty-scope binding, with no extra graph-fact, admission or flatness premise. |

The exact binder order and full types are frozen by ascriptions in
`Effect4Test/Target/TypeScript/StructureComputedContract.lean`. `Graph`,
`DominatorFacts`, `BodyScopedOnEdges`, `Skeleton`, the emitter and the scoping
judgment retain their existing native owners; this packet adds no carrier or
predicate. The two old conditional theorems remain available unchanged.
Table bounds, defined prefixes, forests, ancestry, traversal and intersection
lemmas are implementation helpers and remain private. A helper's usefulness
inside a long proof does not make it a second public surface.

The mandatory assurance route is the existing `docs/TRACE-DAG.md`
`structured-agreement` route. These four facts close the previously assumed
computed-parent obligations for the stated graph domain and support lexical
break/continue binding. They do not replace or close the separate semantic
agreement edges. No new standalone leaf or runtime coverage row is introduced.

## Assumptions, algorithm obligations and non-claims

`GraphClosed g` is exactly the existing target condition
`∀ source target, target ∈ g.succs source → target < g.size`.
Source boundedness is separately
`∀ source target, target ∈ g.succs source → source < g.size`.
The computed fact theorem may assume these and `Structure.reducible g = true`,
but neither `DominatorFacts.childIndex` nor `forwardJoinParent` may be an input.
The latter field keeps its existing forward-edge and merge-or-header premises.
The generic emitter theorem obtains reducibility from successful emission;
the actual-body theorem discharges both bounds for `Flow.graphOf`.

The proof must relate the actual bounded CHK iteration and its actual
intersection/walk fuel to the claimed facts. In particular, any private route
through parent tables must establish root/defined-parent closure, strictly
descending non-root links, preservation of earlier parent chains across later
updates, and enough fuel for each actual intersection and dominance walk.
An unproved convergence or mathematical-dominator assumption is not allowed.
There is no requirement to expose those private proof representations.

The computed `dominates` predicate is a walk of the algorithm's parent chain.
This packet establishes precisely the two graph facts used by the lexical
scoping proof; it does not assert that this chain equals the independent
all-path definition of graph domination, or that every returned parent is the
nearest such mathematical dominator. Those stronger claims would need their
own definition and theorem. In particular, “computed facts” does not mean a
complete correctness theorem for every possible dominator specification.

The generic strict-scoping theorem retains source boundedness. The proposed
`CorrectedBreakScopedStatement` in the old CE-018 witness omits that premise;
this packet does not silently identify or prove that unrestricted statement.
CE-018's original false `BreakScopedStatement` remains refuted. Supplying the
computed graph facts does not permit a body to transfer along undeclared edges.

Full T4 remains open: lexical binding does not establish transfer destinations,
parameter moves, merge/loop semantic composition, loop fuel agreement, or
equality of structured and dispatch `Program` denotations. Both interrupt flag
values are covered by lexical scoping; interrupt-point denotation and the M2
runtime-mask correction remain separate. No generated bytes or host behavior
are changed or claimed by this packet.

## Independent red battery and finite controls

The battery tests actual nonempty computed graphs: the four-node diamond,
a nested diamond whose merge parent is node 1 rather than entry 0, and a graph
whose node-number order differs from reverse-postorder. These catch replacing
all parents with `none`, choosing the entry everywhere, or ordering node IDs
instead of the actual indices. It also checks the existing swap-loop lowering
with parameter moves at both interrupt settings. These are finite controls;
the four universal ascriptions separately require the general results.

A concrete target-closed/source-bounded reducible diamond is passed to the
new computed record theorem. Its forward-join field is then used on each of
the two distinct predecessors of the real merge. Thus neither a vacuous
edge-free example nor a hidden extra premise can stand in for the new result.
The retained CE-018 illicit body must still emit its old orphan break and fail
the corrected edge-local body predicate.

Before production exists, replace only the missing module import with
`StructureOrder` in scratch copies. Removing the marked `COMPUTED-SURFACE`
section produces the isolated controls, which must pass. Keeping it must
reach the four missing public names; an import error alone is not a red
declaration check. The axiom file receives the same import-only replacement
and must reject exactly those four absent constants. A scratch mutant of the
nested-diamond expected table that assigns its merge parent to entry 0 must
fail that guard; restoration must pass.

The builder's saved green scratch checkpoint is
`/private/tmp/effect4-chk-computed-green.lean`, SHA-256
`2d0c9a33e5848ce573dbf2c6a7a76ad75eb1ac5e3dabb33c43523b00d0270e0b`.
It is evidence that the intended statements are constructible, not a substitute
for the independent red battery or the eventual production-module inspection.

## Acceptance and trust

Coordinator checks after implementation, with package work serialized there:

```text
lake build Effect4.Target.TypeScript.StructureDominators
lake env lean Effect4Test/Target/TypeScript/StructureComputedContract.lean
lake env lean Effect4Test/Target/TypeScript/StructureComputedAxiomReport.lean
```

Each of the four public receipts must use at most `propext` and `Quot.sound`.
No `sorryAx`, `Classical.choice`, `native_decide`, or new axioms are permitted.
The reviewer must inspect the actual iteration/intersection/ancestry proof
and confirm that the old algorithm and theorem statements did not change.
The breaker commits only this contract, its battery and its axiom report;
the builder owns only the new production module after that commit. Root
imports, known-red wiring, graph status, shared coordination commit and package
builds remain coordinator-owned. This proof-only packet needs no host gate.

### Breaker receipt, 2026-09-03

Verified before production exists, at repository commit
`3fbf47dc99e30475dd4ba1e61e48c87b54f25386`. Scratch files are in
`/private/tmp/structure-computed-breaker.doafeun3`.

| Command | Observed result |
| --- | --- |
| `lake env lean /private/tmp/structure-computed-breaker.doafeun3/Controls.lean` | Exit 0: all 20 guards, preserved illicit emission, and concrete diamond source bound pass. |
| `lake env lean /private/tmp/structure-computed-breaker.doafeun3/EntryParentMutant.lean` | Exit 1 only at the changed nested-diamond parent expectation. |
| `lake env lean /private/tmp/structure-computed-breaker.doafeun3/Controls.lean` (restored) | Exit 0 again. |
| `lake env lean /private/tmp/structure-computed-breaker.doafeun3/Red.lean` | Exit 1 at the four missing public declarations and uses of those same names; no control errors. |
| `lake env lean /private/tmp/structure-computed-breaker.doafeun3/AxiomsRed.lean` | Exit 1 at exactly the four absent public constants. |
| `lake env lean Effect4Test/Target/TypeScript/StructureComputedContract.lean` | Exit 1: missing `StructureDominators.olean`, recorded separately from declaration-red evidence. |
| `lake env lean Effect4Test/Target/TypeScript/StructureComputedAxiomReport.lean` | Exit 1: the same missing module. |
| `lake env lean /private/tmp/structure-computed-breaker.doafeun3/Candidate.lean` | Exit 0: full independent battery against the builder's trimmed scratch candidate, including all four exact ascriptions and the two non-vacuous forward-parent field uses; all four public axiom receipts are `[propext, Quot.sound]`. |

`Candidate.lean` combines imports once, then the builder's unmodified trimmed
scratch body and this battery without its import lines. The trimmed candidate
was `/private/tmp/effect4-structure-dominators.lean`, SHA-256
`b10c12bb0fb19c5d39a47d58acb58997b207d4f230239669ffe31fd02d751d4a`.
This candidate check did not create a production module or replace the missing-
declaration red state. No algorithm, old packet, generated file or root import
was edited. No package build or host check ran.
