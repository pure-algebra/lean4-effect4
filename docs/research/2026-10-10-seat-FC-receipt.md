# Seat FC receipt: checked fold caches and checked summaries

Two new claims point into tool modules, so the registry gains the root `Tools.View.FlowReach`,
and the Makefile's `gen-semantics` line builds it (`SEMANTICS_TOOL_ROOTS`).

## Base, head and scope

- Branch: `claude/fold-caches`, from the main checkout's HEAD.
- Base: `git:0c62357e5bb770750494d71724a284d063bb6397` (the merge of `codex/host-lowering-plan`).
- Code commit: `git:364b720979d28bb76daf40ef782221be3b127909` (modules, batteries, roots).
- Placement commit: `git:38f590c3c20eb569e320cce8bf72b90614045185` (claims, semantics text,
  Makefile, the regenerated report).
- Docstring commit: `git:eb9f19d3a1cd1ed83efb6ac798dba62f2b8d68cb` (how often `check` reads a
  reference). The commit that adds this receipt follows it.
- Brief: the coordinator's dispatch of seat FC, 2026-10-10. It moves four proposed tool laws of
  `docs/research/2026-10-09-openai-math-probe/OPERATIONAL-PLAN.md` into the tree.

Two more facts matter at the merge. `generated/semantics.md` is regenerated here, so a branch
that changes claims needs one more `make gen-semantics` after the merge. The core root's new
import changes the native core library, so `TestProgram` and `TestDogfood` rebuild in full.

Three of the four laws landed, proved within `[propext, Quot.sound]`. The fourth,
`view-forest-components`, stays open: the probe covers it by a Python finite probe only, and no
Lean prototype states it.

## What landed

### 1. `fold-cache-local-agreement`

- `src/Effect4/Program/TyCache.lean` is a new core module (`module`, `public import`,
  `@[expose] public section`). It holds `Entries`, `lookup`, `read`, `localValue`, `check`,
  `CheckedCache`, `admit`, `CheckedCache.query`, `Built`, `producerLayer`, `produce`, `prepare`
  and `answer`.
- Every entry reads the generated view of `Ty` (`tyCtor`, `tyArgs`, `tyKids`, `tyBuild`). The
  module keeps no constructor match of its own.
- `src/Effect4/Laws/Program/Folds/TyCache.lean` holds the laws. `check_agreement` is the claim's
  pointer: every answer of accepted entries is `cata_ty` of the same layer at its own source.
- Beyond the probe, `answer_eq` is proved: `answer layer t = some (cata_ty (TyAlgebra.ofLayer
  layer) t)` at every type and every layer. So the building fold always succeeds, which the
  probe left open.
- Its proof needs an induction on a type through its generated children (`kids_induction`). It
  comes from `cata_ofLayer_inv` at the identity layer, with one lemma whose case list is
  `tyBuild`'s own (`mem_tyKids_tyBuild`, by `fun_cases`).

### 2. `dependency-summary-exact`

- `tools/Tools/Graph/Summary.lean` is the generic law, beside `Tools.Graph.Path` and
  `Tools.Graph.Index`. A graph gives each node its seeded labels and its ordered children, and
  cycles are allowed. A distance table holds a distance for each node and label.
- `check` reads each reference at most twice for each label: once for inclusion, once for
  support. The probe's checker decided a proposition over every pair of nodes, and this one does
  not.
- `check_valid` connects `check` to the three conditions (`Valid`). `check_summary_exact` is the
  claim's pointer, with both directions.
- `distances` builds a table by breadth-first search against the references, once per label. The
  probe relaxed every reference in `n` rounds instead. `summarize` runs `check` on the table, so a
  refused table is an unanswered summary, never an empty one.
- `Graph.ofFn` reads through `List.ofFn`, because `Vector.getElem_ofFn` reaches
  `Classical.choice` on this toolchain (measured by `ProofGraph.exactAxioms`).
- The consumer is wired. `tools/ProofGraph/Summary.lean` captures the graph that the axiom walk
  reads (`captureDependencies`). It turns `reachedAxiomsMany`'s answers into a table
  (`collectorTable`) and checks it (`checkDependencies`).
- `#axiom_audit checked M …` runs these three steps over the walked declarations
  (`tools/ProofGraph/AxiomAudit.lean`). Without the word `checked`, the command is unchanged.

### 3. `view-reachability-summary-exact`

- `tools/Tools/View/FlowReach.lean` connects `Tools.View.Flow.Reach` to the summary law. The
  reach graph has a node for each position below a bound, and each node seeds its own position.
- `checkReach_exact` is the claim's pointer. `checkReach` accepts a table when every edge's ends
  lie below the bound and `check` accepts the table on the reach graph.
- `ReachTable.build?` refuses an edge with an end at or above the bound, never drops it.
  `ReachTable.reaches_iff` gives each directed query's answer as `Reach`.

### 4. `view-forest-components`: open

The Lean prototypes hold no forest and no weak-connectedness statement. `graph_controls.py` is a
Python finite probe (`graph-results.json`): 64 undirected graphs and 1024 selections, with
assertions. The route that remains:

1. Define weak reachability over selected edge occurrences of `Tools.View.Graph` (`GEdge`), or of
   `Tools.View.Flow.Edge`, with the bound premise of `FlowReach`.
2. Read the components through `Tools.Graph.Summary` on the edges in both directions, each node
   seeding its own label. `check_summary_exact` then gives component membership.
3. Define the forest producer over original occurrences (union-find, as the probe's `forest`).
   Prove that it keeps every weak component and closes no cycle.
4. Wire the consumers `Graph.layout` (`tools/Tools/View/Graph.lean`) and `Run.fiberGraph`
   (`tools/Tools/View/Run.lean`). The full edge list stays for directed queries and wait cycles.

## Changed files

Code, batteries and roots:

- `src/Effect4/Program/TyCache.lean` (new)
- `src/Effect4/Laws/Program/Folds/TyCache.lean` (new)
- `tools/Tools/Graph/Summary.lean` (new)
- `tools/ProofGraph/Summary.lean` (new)
- `tools/Tools/View/FlowReach.lean` (new)
- `tools/ProofGraph/AxiomAudit.lean` (the `checked` mode)
- `Test/Program/TyCacheControls.lean` (new battery)
- `Test/Audit/SummaryControls.lean` (new battery)
- `src/Effect4.lean`, `src/Effect4/Laws.lean`, `Test/All.lean`: one import each at the end of
  the import list (two in `Test/All.lean`)

Placement:

- `tools/ProofGraph/Registry.lean`: three claims at the end of the claims list, and the root
  `Tools.View.FlowReach` at the end of the roots list
- `docs/core/semantics.md`: three required properties at the end of §2.7's list
- `Makefile`: `SEMANTICS_TOOL_ROOTS`, built by the `gen-semantics` recipe
- `generated/semantics.md`: regenerated by the report's producer, with the three claims as its only
  change

## Commands and results

Every Lean command ran in the worktree with `LEAN_NUM_THREADS=3`, one `lake` at a time.

| Command | Result |
| --- | --- |
| `lake build Effect4.Program.TyCache Effect4.Laws.Program.Folds.TyCache` | built |
| `lake build Tools.Graph.Summary Tools.View.FlowReach ProofGraph.Summary ProofGraph.AxiomAudit` | built |
| `lake build Test.Program.TyCacheControls Test.Audit.SummaryControls` | built: every `#guard`, reader and `#guard_msgs` passes |
| `lake build Effect4 Effect4.Laws` | built: the two roots with the new imports |
| `lake build ProofGraph.Registry ProofGraph.Why Effect4.Laws.Author.Explain Tools.LoadPaths Tools.Semantics` | built: the registry's direct importers |
| `lake build Test.Audit.ProofGraph Test.Audit.ScenarioGate` | built: the pinned `#axiom_audit ProofGraph.Axioms` refusal is unchanged |
| `lake build semantics-report` with the report's roots and `Tools.View.FlowReach`, then `lake exe semantics-report <scratch>` | the three claims are proved and at the ceiling |
| the same two commands again, after the last docstring edits of the cache | `semantics.md` byte-identical to the first run (`cmp`) |
| `diff generated/semantics.md <scratch>/semantics.md` before the copy | 34 lines, the three claims only |
| `python3 scripts/check-language.py --show docs/core/semantics.md` | no finding in the added lines |
| `python3 scripts/check-language.py --strict` on this receipt | pass |

Not run, by the brief: `make check-*`, `lake build Test`, `make check-gen`, `make check-docs`,
and every behaviour gate.

## Axiom output

`#axiom_audit checked Effect4.Program.TyCache Effect4.Laws.Program.Folds.TyCache
Tools.Graph.Summary Tools.View.FlowReach Test.Program.TyCacheControls Test.Audit.SummaryControls`:

```text
#axiom_audit: 461 declarations within [propext, Quot.sound], 0 of them modulo planned goals;
0 planned goals; checked: the walk's answers at 2954 constants agree with their captured graph,
over the labels [propext, Quot.sound]
```

By module group: the cache's two modules 245, the summary and the flow connector 135, the two
batteries 81. `#closure_audit` over the same modules and `ProofGraph.Summary`: 534 declarations,
none binds a table before a returned closure.

`#axiom_audit ProofGraph.Summary ProofGraph.AxiomAudit` refuses 4 of 81 declarations:
`collectorTable`, `captureDependencies`, `checkDependencies` and `elabAxiomAudit` reach
`Classical.choice`. The paths enter it through `Lean.Environment` and `Lean.Name.instToString`,
toolchain constants. `ProofGraph.reachedAxioms` reaches it the same way, and
`Test/Audit/ProofGraph.lean` pins that refusal. The axiom gate audits `Effect4.*` and `Test.*`
only. The law these metaprograms apply rests on `propext` and `Quot.sound`.

## Placements

| Point | `fold-cache-local-agreement` | `dependency-summary-exact` | `view-reachability-summary-exact` |
| --- | --- | --- | --- |
| Concept and property | `initial-algebras-folds`; local agreement of a type-fold cache | `initial-algebras-folds`, a tool law; a checked summary of cyclic dependencies | `initial-algebras-folds`, a tool law; a checked reachability of a flow |
| Question | claim, role compatibility, pointer `Effect4.Program.TyCache.check_agreement` | claim, role decidability, pointer `Tools.Graph.Summary.check_summary_exact` | claim, role decidability, pointer `Tools.View.Flow.checkReach_exact` |
| Reach | every layer with decidable answers; entries that `check` accepts; the answer at a type an entry holds; `answer_eq` at every type | every finite graph, cycles and repeated references included; a table that `check` accepts; membership of a label at a node | every edge list and bound; a table that `checkReach` accepts; positions below the bound |
| Not established | speed; reuse after an edit; a typing judgment; an inherited input of the layer | the capture's fidelity to the Lean environment; a theorem that a node names; another stop policy; speed | a schedule; a layout; a forest; weak connectedness |
| Serves | slice D6, memoized folds, for R14 | the axiom and goal reports' evidence for R4, R10 and R14, proving none | directed queries of the application graph, for R14's evidence, proving none |

Each helper's docstring names its claim and its consumer. Each theorem of the cache's law module
carries `@[semantics "initial-algebras-folds"]`, with no requirement. So none is a node of R14:
the cache proves no part of that row.

## Open obligations

1. `view-forest-components`, by the route above.
2. Reuse after an edit: a law that carries an accepted answer to a changed type when the local
   equations still hold. D6 needs it before it keys entries by content address.
3. Speed of the cache: `lookup` is linear, and `prepare` computes the whole fold before `check`.
   No cost theorem exists, and no timing was taken.
4. The probe's `explain`, a path read off the descending distances, is not ported. `#why`
   (`tools/ProofGraph/Why.lean`) answers checked dependency paths already. No theorem connects a
   path read off a table with `Reaches`.

## Bounded and host-only evidence

- The battery lines are finite. The `#guard_msgs` control of `#axiom_audit checked Tools.Graph.Path`
  pins two counts (52 declarations, 197 constants), which a change of the toolchain moves.
- One finite probe measured the checked mode on `Effect4.Laws.Program.Typing.Annotate` and
  `Effect4.Laws.Program.Sketch`: 6832 constants, 190162 references, two labels. In one run, the
  check took about 1 s interpreted, beside a 0.9 s walk.
- No host run, no TypeScript compiler and no behaviour gate.

## Proposals for the coordinator

1. **Tool laws as registry claims** (proposed decisions row). The earlier tool laws stay outside
   the registry and cite rows 334 (3) and 336 (8) for it (`tools/Tools/View/FlowLaws.lean`,
   `tools/Tools/Graph/Path.lean`). The brief asked for claims, so two tool claims and one tool root
   landed. Options: keep them, and the report shows their status and axioms; or drop the two
   claims, the root and `SEMANTICS_TOOL_ROOTS`. Recommendation: keep.
2. **The architecture map's layering**. `ProofGraph` (height 0) imports `Tools.Graph.Summary`
   (height 2), as `ProofGraph.Why` already imports `Tools.Graph.Path`. By reading `allowed`
   (`tools/Tools/ArchitectureRoles.lean`), both imports run against the direction. The map was not
   run. Recommendation: an area `tools/Tools/Graph` at height 0 in that file.
3. **The checked mode's default**. It stays opt-in. Recommendation: run it at every landing that
   touches `tools/ProofGraph/Axioms.lean`, and at a sweep.
4. **A generated induction on children**. The generator emits `sizeOf_{low}Kids` for a plain
   family and nothing for a nested one (`tools/Effect4Gen/Fold.lean`). Emitting `kids_induction`
   for nested families would replace the two hand lemmas of the cache's law module.
5. This branch leaves `docs/STATE.md` to the coordinator's merge.
