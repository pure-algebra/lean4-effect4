# Load-path report controls

The report can label an actually consumed theorem `unconsumed` when an ordinary definition carries its proof.
Keep the owner's prohibition on deletion from this report.

Base and head: `01c83fbc0f319999faf9a9ab306137a95f6dd303`.
Reviewed implementation: `git:0f8a228e:tools/Tools/LoadPaths.lean`.
Reviewed note: `git:01c83fbc:docs/research/2026-10-08-load-paths.md`.
Worktree: `/Users/pooks/.codex/worktrees/module-folds/lean4-effect4`.
No production file changes or commits occur in this review.

Changed files:

- `docs/research/2026-10-08-load-path-probes.lean`
- `docs/research/2026-10-08-load-path-probes-receipt.md`

## Scope and placement

Evidence: checked finite metaprogram controls.
Proof role: tooling controls, with the fixture checks as their consumer.
Fragment: the loaded fixture, the report functions, and the population classifier.
The controls establish no Effect4 semantic property or host behavior.
They propose no deletion, production theorem, semantics registry entry, or frozen contract amendment.

The fixture changes the local environment's module identity to `Tools.LoadPathsProbe` for graph inclusion.
It does not change the imported environment or add a production module.
The first command checks labels against the actual graph before the restoration theorem exists.
The second command rebuilds the actual graph after that theorem exists.
Neither command changes the graph to obtain its result.

## Checked controls

| Control | Actual consumer | Report result | Consequence |
| --- | --- | --- | --- |
| Direct theorem | `directConsumer` names `directSeed` | Visible | Positive control passes |
| Ordinary proof data | `proofWrapper : PLift True` names `wrappedSeed`; `wrappedConsumer` projects the proof | Hidden; seed classified `unconsumed` | Ordinary definitions interrupt the reported dependency path |
| Restoration | `wrappedRestored` directly names `wrappedSeed` | Visible again | The finding depends on the intermediate definition |
| Statement dependency | `typeConsumer` names `typeSeed` in its statement | Hidden; seed classified `unconsumed` | Proof-body references do not cover statement dependencies |
| Ordinary instance | A `Type`-valued class instance names `instanceSeed`; `instanceConsumer` names that instance | Hidden; seed classified `unconsumed`; instance count is zero | Ordinary definition instances do not enter instance accounting |
| Library endpoint | `coreConsumer` uses `Nat.zero_lt_succ` | Header includes the library endpoint | Header reach count and tree-member reach count differ |
| Missing semantics registry roots | Semantics registry pointer/top names are absent from the minimal loaded fixture | Root filtering silently removes the names | A partial import produces a report without omitted-root diagnostics |
| Authored name | Explicit theorem `instSizeOfControl` | Population classifier excludes it | A generated-looking spelling can hide an authored theorem |
| Proof-field projection | Lean generates `HasEvidence.evidence` | Population classifier calls it authored | The population includes generated proof-field projections |

These controls bound the findings to the stated fixture.
They do not establish the magnitude of any correction to the historical whole-graph counts.
The projection result requires a population policy decision before changing the classifier.

## Commands and output

Compiler: the pinned `leanprover/lean4:v4.33.1`.

```sh
LEAN_NUM_THREADS=3 lake build Tools.LoadPaths
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-load-path-probes.lean
```

Both commands exit with status zero.
The final fixture reports:

```text
PASS first ten fixture theorem declarations have empty axiom sets
PASS authored instSizeOfControl theorem excluded by generated-name spelling
PASS generated proof-field projection counted as authored theorem
PASS header count includes nonmembers: 8 reached names, 7 graph members
PASS actual class-instance consumer hidden: (some #[LoadPathProbe.HasEvidence.evidence]); instance edges 0
PASS direct theorem visible: (some #[LoadPathProbe.directSeed])
PASS authored proof wrapper hides dependency: (some #[])
PASS statement-only dependency hidden: (some #[])
PASS wrapped/type seeds labelled unconsumed despite actual consumers
PASS missing registry names are silently omitted: 257 names, 0 retained roots
PASS direct restoration reveals dependency: (some #[LoadPathProbe.wrappedSeed])
PASS rebuilt actual graph counts restored seed as consumed and load-bearing
PASS restoration theorem has empty axiom set
```

`Lean.collectAxioms` checks every fixture theorem and reports empty sets.
This is a fixture axiom receipt, not the whole-library axiom gate.
Earlier fixture drafts expose and correct the proposition-definition linter, an implicit proposition-valued class, and a projection-query namespace error.
The retained fixture uses ordinary data definitions and an explicit `Type`-valued class.

## Source findings and smallest corrections

The source findings below have no exhaustive execution check.

| Owner | Finding | Smallest correction |
| --- | --- | --- |
| `directTheorems` in `tools/Tools/LoadPaths.lean` | Only generated auxiliaries receive further traversal | Keep direct theorem-citation edges; add a separate structural reach measure over ordinary definitions |
| `directTheorems` in `tools/Tools/LoadPaths.lean` | Declaration statements are absent from the starting references | Keep the citation metric narrow; record statement edges in the structural reach measure |
| `roots` in `tools/Tools/LoadPaths.lean` | Missing pointer/top names disappear through `filter env.contains` | Return resolved and missing names; state or enforce the loaded-environment contract |
| `loadBearing` in `tools/Tools/LoadPaths.lean` | The reached set includes endpoints outside `Graph.deps` | Intersect header totals with graph members; report external endpoints separately |
| `loadBearing` in `tools/Tools/LoadPaths.lean` | Walk-budget exhaustion returns a partial set without a flag | Return an exhaustion result and suppress categorical conclusions |
| `buildGraph` and `#load_map` in `tools/Tools/LoadPaths.lean` | Exhausted theorem walks leave the measured population; map output omits the exhaustion count | Retain unknown members and report incomplete evidence consistently |
| `measure` in `tools/Tools/LoadPaths.lean` | Instance counting starts after theorem-only dependency filtering | Count referenced definition instances separately |
| `isGeneratedCompanion` in `tools/ProofGraph/Population.lean` | The `instSizeOf` prefix receives no origin check | Check actual generated origin or constrain the population claim |
| `authoredTheorem` in `tools/Tools/LoadPaths.lean` | Generated proof-field projections count as authored | Define whether source-authored fields belong to the population; expose their category |

`Report.ratio` in `tools/Tools/LoadPaths.lean` divides tree edges by tree and local edges.
The graph counts each named dependency once per consuming theorem.
The ratio does not count distinct reused laws or distinct new helpers.
Module-prefix grouping changes which endpoints count as local.
Moving a helper between modules can change the ratio without changing any proof dependency.
Report the raw edge counts and module grouping alongside the ratio.
Do not use the ratio as a quality score or a semantic-importance measure.

The note's source-based battery/tool counts have no retained producer in the reviewed tool.
The report does not check unused `aesop` rules, attribute metadata, or source consumers outside the loaded environment.
A theorem's availability to future proof search differs from references in already elaborated Lean proof terms.
Keep those questions separate when classifying access and basis families.

The population spelling and projection findings originate in the preexisting `ProofGraph.Population` helper.
They are inherited limitations, not regressions introduced by `Tools.LoadPaths`.

Keep structural dependency reach separate from the direct theorem-citation measure.
`ProofGraph.usedConstantsOf` in `tools/ProofGraph/Axioms.lean` already collects declaration type and value references.
Its traversal can support structural reach through ordinary definitions with separate edge kinds.
A structural consumer does not imply an explicit theorem citation or a reused law.

## Open work

The report owner must choose the dependency kinds and population policy before changing historical measurements.
The coordinator may retain these finite controls as regression evidence for that change.
No whole-library report, battery, or sweep runs during this review.
