# Slice B receipt: structural program path replacement

**Coordinator first:** this is structural editing. Equal local types do not make
an edit globally valid: the fixture retains an equal-layer-type edit that removes
a referenced descendant, and complete program checking rejects its result. The
coordinator must add the Concept 7 property and registry claim proposed below.

Base: `8913519b`. Code head: `d137888b0ca3347a93b0d9909bb0e921ee0a4cdc`.
Branch: `codex/program-path-editing`.
Worktree: `/Users/pooks/.codex/worktrees/program-path-editing/lean4-effect4`.

## Changed files

- `src/Effect4/Program/Refs.lean`: `Node.replaceAt` recurses over a finite path,
  uses generated immediate-child read/write operations, and refuses absent paths
  or a replacement of a different sort. `replaceLayerAt` delegates to it.
- `src/Effect4/Laws/Program/References.lean`: general structural laws and unchanged
  layer replacement laws through the common operation.
- `Test/Codegen/ReadContract.lean`: all seven sorts, the 49 root-sort pairings,
  absent paths, nested edits, existing hoist/restore consumption, and the dangling
  reference counter-control described above.
- This directory's brief and receipt. No root, register, generator, checker or
  machine edits; existing module imports already cover every changed source.

## Checked evidence

Commands ran sequentially in the worktree with Lean warning-as-error enabled by
the project. The `.lake/packages` and `.lake/build` caches were APFS-cloned from
the coordinator worktree; no research directory was copied.

| Command | Result |
| --- | --- |
| `lake build Effect4.Program.Refs` | Passed, 28 jobs |
| `lake build Effect4.Laws.Program.References` | Passed, 198 jobs |
| `lake build Effect4.Laws.Program.Hoisting Effect4.Laws.Program.HoistingTotal Effect4.Program.Authoring Test.Codegen.ReadContract` | Passed, 304 jobs |
| `lake build Test.Program.AuthoringContract` | Passed, 299 jobs |
| `lake env lean /private/tmp/path-edit-axioms.lean` | Passed; imports References and prints both edited definitions and all twenty theorem declarations in that module |
| `git diff --check` | Passed |

The retained fixture prints the public generic and layer theorems' axioms. The
additional temporary audit covered every theorem in the touched laws module:
all use only `[propext]` or `[propext, Quot.sound]`; neither edited definition nor
any audited theorem uses `Classical.choice`. The fixture contains finite controls,
not a proof of global editing admission. No whole-tree sweep or host execution
was claimed or run.

The first laws build found proof-script elaboration issues, corrected before the
successful builds above. No statement was weakened.

## Five-part placement of the landed theorems

All rows below have Concept 7 (`initial-algebras-folds`), the proposed
`addressed-replacement` compatibility claim, and R8's exact module reconstruction
consumer. Their reach is arbitrary `Op`, all seven `Node` sorts, and finite paths.
Their exclusions are typing, global reference validity, binding relocation,
runtime behavior, liveness, and host behavior. They add no M5/M6/M7 claim.

| Declarations | Exact structural claim and consumer |
| --- | --- |
| `setChild_self`, `setChild_overwrite` | Generated immediate-child updates obey read/write and overwrite laws; helpers for the generic path laws |
| `replaceAt_spec` | Successful editing reads back the replacement, keeps the root sort, and permits restoration of the previous subtree; registry witness and layer compatibility consumer |
| `replaceAt_exists` | A present path and equal replacement sort suffice for success; layer existence consumer |
| `replaceAt_self` | Writing the subtree already at the path returns the original root; authoring transformation helper |
| `replaceAt_overwrite` | A second write at the same path has the same result as writing directly to the original root, including a refused wrong sort; structural composition helper |
| `at_replaceAt_disjoint` | An edit under one child leaves a read under a distinct child of the same ancestor unchanged; independent-branch editing helper |
| `replaceLayerAt_eq_replaceAt`, `replaceLayerAt_cons`, `layerAt_eq_some_iff` | Layer wrapper and projection connectors; unchanged `replaceLayerAt_spec`, existence, restoration, and hoist/restore consumers |
| Existing touched layer laws and `child_setChild_ne` | Existing statements retained; proofs share the generic operation and permitted proof search; `Eff.restoreAll_hoistAll` / `Eff.hoistAll_restoreAll` are the downstream consumers |

## Exact coordinator additions proposed

At `docs/core/semantics.md`, Concept 7, Required Properties, after fold congruence:

> **Addressed replacement (`addressed-replacement`)**: successful same-sort
> `Node.replaceAt` reads back the replacement, keeps the root sort, and can restore
> the original subtree. It lifts generated immediate-child operations over finite
> paths. These structural laws support module hoisting/reconstruction; they imply
> neither typing nor global layer-reference validity nor behavioral equality.

At `tools/Tools/SemanticsRegistry.lean`, after `cata-eff-congr-on`:

```lean
    { id := "addressed-replacement", concept := "initial-algebras-folds", role := .compatibility
      title := "Successful same-sort path replacement reads back, retains the root sort, and restores the original tree"
      pointer := .witness `Effect4.Program.Node.replaceAt_spec },
```

No decisions row is required: path-based layer identity and checking keep their
existing contracts (DB-12, decisions 153/170). No traversal census change is
required: the new recursion is over the path and reuses generated child access
and update, with no new runtime case walk over a policy family.

## Remaining limits

Terms are not Node-addressable. An edit does not relocate de Bruijn variables or
layer references, and changes no running session. A subsequent slice may expose
whole-program rebuilding for edited syntax; it must rerun complete admission.
