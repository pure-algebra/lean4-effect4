# Graph and tree audit plan

## Scope

Review commit `de2af69151186b775c020b9fa7f942181a7ba442`.
Keep the primary checkout and Claude's implementation unchanged.
Use branch `codex/graph-tree-audit` in the attached review worktree.
Claude owns the renderer algebra and the current view slices.
This audit investigates shared operations and their contracts before proposing implementation slices.

## Finishing criteria

- Identify the graph and tree owners, their edges, and their consumers.
- Connect proposed computations to existing named laws and their premises.
- Execute small positive and negative controls against current code.
- Distinguish measured operation counts, finite results, proved facts, and proposals.
- Check relevant graph theory against primary sources.
- Recommend small complementary slices with concrete consumers and author interfaces.
- Record commands, results, limits, and remaining obligations.

## Questions

1. Which consumers repeat navigation, adjacency construction, or dependency walks?
2. Which attributes depend on content, context, address, or execution history?
3. Which graph operations keep immediate edges, reachability, order, or multiplicity?
4. Which existing fold laws justify combined computations?
5. Which additional laws would permit incremental computation?

## Probes

Use actual program constructors and view operations where possible.
Compare construction frontiers with a parent index on finite program trees.
Compare graph composition by boundary edges with algebraic graph connect.
Check graph identity and endpoint assumptions on small layouts.
Check path relocation and environment changes separately for the checker.
Retain failed hypotheses as explicit negative controls.

## Proof placement

This audit adds no general theorem and changes no registry claim.
Existing law readers retain each theorem's full premises.
Proposed fold and address laws serve `initial-algebras-folds` and requirement R14.
Proposed cache laws name their consumer, environment, typing signature, and observation before implementation.
Tool layout laws remain outside the semantics registry under decisions rows 334 and 336.
Graph reachability does not establish execution progress or program simulation.

## Verification

Run one narrow Lake process at a time with `LEAN_NUM_THREADS=3`.
Run research probes without changing production roots or batteries.
Check new Markdown with the repository language checker.
Commit only the named research files.
Do not merge or push.
