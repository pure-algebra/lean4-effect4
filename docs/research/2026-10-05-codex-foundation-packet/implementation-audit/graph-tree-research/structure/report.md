# Trees, references, control, and reusable proof connections

Frozen source: `cbd2ec5793006fd1279121c5104bfdbdc065ea40`, `/Users/pooks/Dev/lean4-effect4`.
Evidence: source review and an isolated Python model of layer-reference rules. No Lean, repository runtime, compiler, build, or generator runs.
Active module-card snapshots are separate from the frozen source. Their hashes and copied bytes accompany this report.

## Main finding

The compiler does not flatten `Eff` into an instruction array. `Point.path` addresses the stored tree, and continuation names carry points.
`interpOf root` resolves those names against the original tree. Paths are source addresses; they are not complete runtime states.

The existing laws already cover much of the proposed graph work: structural editing, hoisting and reconstruction, typed source points, generator positions, and compatible world extension.

The strongest missing connection is narrower: prove that well-formed layer references disappear within the existing expansion bound. The checker currently verifies both properties separately.
A finite dependency-rank proof can connect them. It should not replace execution with expansion, because execution preserves sharing through source-path memo identities.

The second useful change is small: move general path concatenation into the structural law owner and reuse it in existing typing and generator proofs.
A generic control-flow graph, a dominator framework, and whole-program rewrite transport are not prerequisites for the module cards.

## 1. The graphs must remain distinct

| View | Actual owner | Nodes and edges | What it does not imply |
| --- | --- | --- | --- |
| Structural syntax | `Program/Eff.lean`, `Program/Node.lean`, `Machine/Term.lean` | Constructor occurrences and their stored children | A finite syntax tree can describe an unending loop |
| Addressed program family | `Program/NodeLenses.lean`, `Program/Refs.lean` | A root plus child-index paths; seven node sorts | `Term` is not a node in this path language; its own fold owns its children |
| Layer dependencies | `LayerTerm.ref`, `Eff.layerRefsWF` | A reference site points to a defining layer occurrence | Lookup and reference ordering do not make expansion preserve memo identity |
| Runtime control | `Program/Compile.lean`, `EffName`, `EffThunk`, generator counters, frame stack | Success/error continuations, loop returns, finalizers, observer delivery, fork entry | These edges are not structural child edges and need not be acyclic |
| Resource and capture relations | `Typed.World`, `PointTyped`, `CaptureTyped`, stores | Handles, declarations, saved environments, contexts and live owners | Compatible world extension is not execution, allocation freshness, or resource conservation |
| Execution history | run decisions, journal, fork ledger | Particular transitions and stamped creation events | A trace is not the source graph, and a source location is not an allocation identity |

`Point` retains a path, environment, fuel, tape, completed-fiber view, and a reserved root number.
`child` extends the path; `childWith` also appends a value. `layerBuild` instead resets the lexical environment to empty.
`redirect` changes the path and spends fuel. Its purpose differs from a structural child traversal.

The runtime's `Region` type names context/build regions. It is not a compiler dominance region.
`loopResumeAt` returns to `loopNextAt` at the same source point with a new cursor.
Generator `blockExit` can return to an enclosing while body; `loopExit` exits through nested block contexts.

Thus no source-tree topological ordering gives runtime termination. Even bounded execution can stop at a frontier rather than a completed exit.

## 2. Existing laws to reuse, not replace

### Structural folds and paths

`hom_eq_cata_eff` and its family in `Program/Fold.lean` establish the existing initial-algebra connection.
`cata_eff_congr_on` in `Laws/Program/Signature.lean` relates folds whose algebras agree on the constructors and operation/key data used.
A new graph inspection should be a view from these folds, not a second canonical representation.

`Node.yieldAt_subset_of_at` in `Laws/Program/PathFold.lean` connects an addressed node's yield to the root's path fold.
`mem_refSites_of_at` specializes this to layer references. `layerRefsWF_at` then supplies a non-reference layer target.
The current generic path-fold results are inclusions; this review found no reverse, exact enumeration theorem there.

`Laws/Program/References.lean` already provides:

- `setChild_spec`, `setChild_self`, `setChild_overwrite`, and `child_setChild_ne`;
- `replaceAt_spec`, `replaceAt_exists`, `replaceAt_self`, and `replaceAt_overwrite`;
- `at_replaceAt_disjoint`, with an explicit common prefix and distinct child branches.

`replaceAt_spec` gives read-back, same root sort, and restoration of the original node.
It does not give typing, variable remapping, preservation of references, or equal execution observations.
An ancestor edit can erase descendant addresses; disjoint structural branches can still be joined by a layer reference.

`HoistingTotal.Eff.hoistAll_exists_of_targets` needs only existing targets.
`Eff.hoistAll_exists` specializes it to well-formed references. `Eff.hoistAll_restoreAll` reconstructs the original tree.
These already provide the useful structural hoisting connection. Do not propose another generic hoisting/reconstruction campaign.

### Typed runtime addresses and environments

`PointTyped` in `Typed/Admission.lean` includes all of these:

- the original root's path selects an effect node;
- the checker accepts that node through the root's expansion, under an explicit type environment;
- point values fit that environment in the world;
- the saved completed exits fit their declared fiber types.

`CaptureTyped` specifically describes an `acquireRelease` node, the acquired value appended to its environment, and captured services.
It is not a general stored-code certificate.
`LayerPointTyped` describes checked layers with an empty lexical environment and a typed completed view.

`pointTyped_child` and `PointTyped.at_node` in `Typed/Denotation.lean` already connect paths and checks.
`layerPointTyped_redirect` in `Typed/LayerArm.lean` transports a reference's typing to its actual target.
`pointTyped_mono`, `layerPointTyped_mono`, and `captureTyped_mono` retain their compatible-world premises.
No new graph-reachability predicate should replace those environmental conditions.

### Generator control and region structure

`Typed/Commands/Clauses/Gen.lean` already models generator positions with `GenCtx`, `PosOk`, `Fall`, and `Brk`.
`PosOk` retains the block address, suffix address, checked suffix, environment split, local-binding count, and permitted exits.
`splitPc_ctx`, `blockEnv_eq`, `loopExit_typed`, and `walk_typed` prove the needed cursor and scope connections.
`genProtocol` closes the iterator protocol by coinduction. Its comment explicitly excludes progress and termination.

These are structured-control invariants that perform much of the work one might seek from dominance or region analysis.
A second generic CFG would first need a concrete transformation consumer that these laws cannot serve.

### Allocation history and worlds

`ForkLedger.spawn_forks` records an append equation. New-ID lookup needs fiber and record freshness.
`fork_source_extension` connects a stamped source child and its explicit source type to the newly allocated fiber.
Its comment excludes internal forks and a universal source-origin claim. This report does not strengthen it.

The world order has existing transport laws and separate allocation-extension laws.
`heapNotMonotone` in `Typed/World.lean` refutes preservation of heap typing from raw store growth alone.
An acyclic source graph therefore cannot replace resource-world compatibility or capture membership.

## 3. Highest-value missing connection: reference expansion by finite rank

### Current boundary and concrete consumers

`typeOfProgram` in `Program/Typing.lean` tests both `layerRefsWF` and emptiness of the expanded reference sites.
`TypedProgram.expanded_refSites` derives emptiness from successful admission, not from well-formed references alone.
`checkTypedProgram_of_hasTy` requires both reference well-formedness and expanded emptiness as premises.
`typeOfProgram_expandRefs` in `Laws/Program/ReferenceTyping.lean` also retains the separate emptiness premise.

Proposed statement, not compiled or proved:

```lean
-- Proposed shape only; final declaration placement precedes implementation.
theorem expanded_refs_nil_of_wf (root : Eff Op)
    (valid : root.layerRefsWF = true) :
    root.expandRefs.refSites [] = []
```

Keep the existing executable check initially. Derive an ergonomic admission theorem that supplies its redundant premise from the new law.
Keep the older theorem as a compatibility API if callers still use it. No runtime rewrite is needed.

### Why graph theory helps here

The relevant graph is finite and belongs to one fixed original root.
A reference depends on the references inside its target definition.
The target precedes the site and does not enclose it. Therefore references copied from that target originate earlier than the original site.
Use a rank in the finite original reference-site enumeration. Each unresolved dependency strictly decreases that rank.

Do not claim that lexicographic order on all finite `List Nat` paths is well founded.
There is an infinite descending chain `[1]`, `[0,1]`, `[0,0,1]`, and so on.
Finiteness of the original addressed occurrences is indispensable.

Expansion can increase the number of reference occurrences by copying a shared target.
The proof must decrease dependency depth or rank, not the number of occurrences in the expanding tree.
Copied nodes have new occurrence paths, but their reference targets still address the original root.
Keep that origin relation in the proof; do not add origin annotations to canonical syntax merely for this lemma.

### Minimal prerequisites

1. General path concatenation over arbitrary `Op` and arbitrary suffixes.
2. Exact correspondence between the relevant path-fold enumeration and successful lookup, extending the existing inclusion result.
3. Distinctness of occurrence paths and a finite rank for original reference sites.
4. A lemma that references inside a valid target precede its dependent site.
5. A bounded-round induction over that rank, using the existing expansion algebra.

Steps 2 and 3 should specialize to what the reference proof needs. Do not build a general graph library first.

### Placement and exclusions

Concept: `initial-algebras-folds`; compatibility of the existing expansion fold with the finite reference discipline.
Proposed registry claim: `reference-expansion-complete`. This name is a proposal, absent from the inspected registry.
Consumers: `checkTypedProgram_of_hasTy`, `typeOfProgram_expandRefs`, and shared-layer admission/read-back under R5 and R8.
It also simplifies a premise used by `denote-typed`; it does not extend that theorem's runtime scope.

This is not execution equality between a shared program and its expansion.
`resolveLayer` redirects to the defining path so memoization sees one identity. Expansion duplicates syntax for typing.
Preserving memo sharing needs its own observation and law, already separated in `LayerSharing.lean`.

Done criteria: a placed theorem at the unchanged expansion bound, the two named consumer corollaries, nested/shared positive cases, malformed-reference refusals, and normal axiom evidence.
Removing the runtime emptiness check would be a subsequent implementation choice with its own measured benefit.

## 4. A small connector worth landing with that proof

`Agreement.Node.at_append` currently handles one final child at `NativeOp`.
`Typed/Denotation.node_at_child` and generator `at_snoc1`/`at_snoc2` rebuild related facts.

Add a generic structural equation in the existing path-law owner:

```lean
-- Proposed shape only.
node.at_ (prefix ++ suffix) = (node.at_ prefix).bind (fun child => child.at_ suffix)
```

Instantiate it for the existing one- and two-child consumers. Preserve their statements or retire wrappers after migrating the callers.
Its concept is `initial-algebras-folds`, as a helper of `addressed-replacement` and proposed reference-expansion completeness.
Its observation is exact `Option (Node Op)` equality, including missing paths. It makes no typing or execution claim.

This is a small API consolidation with actual callers. It is not grounds for a separate algebra roadmap.

## 5. Attractive proposals to defer or reject

**A tree or DAG implies termination:** false for runtime control. Loop callbacks return to the same point, with changed cursors and stores.

**Adjacency gives an exact embedding:** false without labels. `succeed 0` and `succeed 1` have identical child edges but different observations.
A reconstructible graph view must retain constructor tags, nonrecursive fields, terms, and source identity. It needs all embedding laws before becoming another serialized face.

**Structural disjointness gives semantic independence:** false with reference edges, shared services, and shared stores.
`at_replaceAt_disjoint` frames lookup only. It cannot authorize simultaneous program transformations or commute their effects.

**A valid path is a typed closure:** false. The same `var 0` path can read two distinct same-typed values in different environments.
A saved completed-fiber view also changes eager await construction. Retain `PointTyped`'s full data.

**Ordinary graph reachability proves resource cleanup:** false. A finalizer can be registered but not completed at a fuel frontier.
Cleanup needs its registration identity, owner, saved context, and completion observation, not only an edge to the finalizer source.

**A generic contextual rewrite law is immediately required:** not demonstrated by this review.
`StraightEq` already has constructor congruences and `run_agrees` for exit plus complete stores, with separate sufficient budgets.
A new path-rewrite consumer could assemble those laws for a reference-free straight fragment.
The existing `Built.rebuild` re-admits the candidate; it does not require semantic transport. Defer a generic rewrite theorem until an actual optimizer needs it.

**Syntax graph structure gives new M5–M7 closure:** unsupported. The current point, generator, residual, and world invariants already supply those connections.
A graph projection can expose them for a particular consumer; it must not drop their premises.

## 6. Module-card advice from the graph boundary

The active Semaphore card is a proposal. Its current revision distinguishes live scan, snapshot, and grant-at-wake profiles.
A source-level fold is an appropriate implementation for an atomic selection profile. It does not model a live scan that resumes another fiber between visits.
The card already marks that choice open; this review proposes no new profile ruling.

For the first API, use an ordinary `withPermits count body` builder with its body supplied at the authoring site.
Reuse minted binders, the exact elaborated-body typing equation, and existing point/capture laws where their statements fit.
Do not require general stored callbacks or a flattened control graph to land Semaphore.

Move `Reads`, `Captured`, and the store connectors only when Semaphore actually calls them. Keep the caller's environment and exact body in the shared statements.
The identity/hint table is a proof-side relation. Its declared Deferred answer types remain module-specific; matching key shapes is insufficient.

Pool and Cache cards are not present in the inspected active card directory. Their planned retained behavior belongs to R7.
`LayerTerm.ref` is a closed-layer reference with memo identity. `CaptureTyped` specifically admits an acquire/release finalizer layout.
Neither is a generic Pool acquisition or Cache lookup closure certificate.
The first retained-behavior card must specify entry identity, capture layout, invocation services, lifetime, and world transport before choosing a representation.

The module factory therefore benefits more from exposing existing typed-address and environment connectors than from introducing graph infrastructure now.
Reference-expansion completeness can proceed independently as a small foundational proof slice. It is not a gate on the waiting-module APIs.

## 7. Retained finite model and evidence limits

`reference-model.py` mirrors layer-child paths, the reference predicate, and fixed-root expansion over two small layer shapes.
It examines 4,439 candidate assignments; 32 satisfy the mirrored predicate, and all eliminate references within the mirrored bound.
Separate inhabited controls cover sharing and references into a definition that itself contains a reference.

A mutant drops the non-enclosing-target condition. It admits a reference to its own non-reference ancestor and leaves a reference after the bound.
The current predicate refuses that case. This shows why the exclusion matters; it is not a counterexample to the current implementation.

The model also records a strict descending lexicographic path sequence. It cautions against the wrong well-foundedness argument.
These are bounded Python controls, not Lean proofs or runtime conformance evidence. All proposed theorems remain proposed.

## 8. Follow-up challenge: nested targets, diamonds, and the unchanged bound

This refinement uses the same frozen `Program/Refs.lean`, not later seat changes.
The proposed theorem remains uncompiled and unproved.

`layerRefsWF` checks target existence through `Node.layerAt`, the layer sort, and the non-reference target constructor.
It also checks earlier order and rejects a target that properly encloses its reference site.
It does not check lexical closure or a type environment. Those belong to separate layer typing judgments.
Do not add lexical closure as an unexplained premise of the structural reference-elimination theorem.

The source dependency relation must be explicit.
For an original reference at `s` targeting `t`, add an edge to each original reference occurrence `r` in the subtree at `t`.
Successful lookup and the path-fold correspondence must establish `r = t ++ suffix` in the original tree.
Because the target is not itself a reference, the relevant nested occurrence has a nonempty suffix.
Earlier order plus the rejected ancestor case put every such `r` before `s` at their first divergent child.
Neither this order fact nor the finiteness fact alone is the bounded-expansion theorem.

The remaining proof needs a rank on the finite original reference sites and an origin relation for copied occurrences.
One expansion round substitutes the original target without recursively expanding newly inserted syntax in that same round.
After a substitution, every remaining nested reference must inherit an earlier source site and retain its original-root target.
Bound rounds by the longest source dependency chain, then bound that chain by the number of distinct original reference sites.
Only this connection justifies the existing `refSites.length + 1` implementation bound.
No bound on expanded tree size follows. Shared targets can multiply unresolved occurrences.

The retained Python controls now include an explicit dependency diamond.
It has five original reference sites and three dependency rounds; the reference counts are `5, 4, 2, 0`.
A separate multiplicity control has counts `6, 9, 0`. It directly refutes using current occurrence count as a decreasing measure.
The nested-target control has counts `2, 1, 0`.
All controls check source-site membership and strict finite-rank decrease for their dependency edges.
They are layer-only abstract examples, so they do not verify mixed-sort path enumeration or the Lean fold connector.
Those remain required proof work. The earlier ancestor-exclusion mutant remains refusing under the current mirrored rule.

Smallest landing still consists of the placed theorem and its two admission consumers.
Do not convert this into a general runtime graph rewrite, new syntax metadata, or a gate on Semaphore implementation.
