# Seat brief: the address algebra and rebaseRefs (seat ADDRESS)

Status: brief (history, not authority). 2026-10-13. Decisions rows 336 (1), (6) and (7), 376 (1).
The ground of obligation O1 (typed edits) of `docs/research/2026-10-13-authoring-obligations/README.md`.

**The one thing to know first.** An agent's graph operations (move, paste, extract) need two
things first: proved laws of addresses, and `rebaseRefs`, which keeps a moved subtree's layer
references well formed (seat ORG's L9, `docs/research/2026-10-08-seat-ORG-theory-map.md`, its
table and rank 5). Neither exists. The program in the store (`Content (Eff NativeOp)` at kind
`program`) is rank 5's first hour. A piece's key waits on the MCP note's ruling 3: stop there.

## Read first

- Seat ORG's theory map, whole; the graph tree audit (`docs/research/2026-10-09-graph-tree-audit.md`);
  ORG's cleanup receipt (`docs/research/2026-10-09-org-cleanup-receipt.md`).
- The tree: `src/Effect4/Program/Refs.lean` (`Eff.expandRefs`, `layerRefsWF`),
  `src/Effect4/Laws/Program/References.lean`, the path and address code wherever it lives (search
  first), and the generated store instances (`src/Effect4/Store/Domain/Derived/`).

## What to build, in order

1. The address algebra: the laws of paths that the graph operations will use (prefix, append,
   relocation), gathered where they already live or in one module if none exists.
2. `Eff.rebaseRefs` with its law, the proposed claim `references-move`: a subtree whose references
   stay inside it keeps `layerRefsWF` when moved. Then `Eff.strengthen` if the map names it.
3. If no ruling is needed: `Content (Eff NativeOp)` at kind `program`, with `program-digest-exact`,
   through the existing generator. If the generator must change, stop and propose it.

## Reuse first (row 376 (3))

- Address and path lemmas likely exist in several places (layer view, slices, focus, the edit
  session). Search them all before writing one: `git grep` by the concept, `#why`, the registry,
  `#auto_census`. Gather duplicates into one home and redirect their users; list both names in the
  receipt. A new duplicate is a defect.
- Proofs use aesop and its banks (`src/Effect4/Laws/Auto/RuleSets.lean`) where they close; a path
  bank may be worth adding, with its fixture.

## Boundaries

- Worktree: `~/Dev/lean4-effect4-address`, branch `seat/address`, made by the coordinator.
- Edit `src/Effect4/Program/Refs.lean`, a new address module under `src/Effect4/Program/`,
  `src/Effect4/Laws/Program/References.lean` and new law modules beside it, the users of a lemma you
  gather, `Test/**`, and the root imports at their end. Never edit `src/Effect4/Program/Typing/**` or
  `tools/Tools/Session*` (seat APPCHECK), `src/Effect4/Program/Authoring/**` (seat CLAIMS),
  `lakefile.toml`, `docs/core/**` or the registry.
- Every `lake` through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`, narrow. Every reader of
  a changed definition builds before its commit. Commit by named paths. Never push or merge. Stop
  under 8 GiB free.
- Stop at a question of meaning, at the piece's key, or at about six hours. The receipt
  `docs/research/2026-10-13-seat-address-receipt.md` (force-added) names first the one thing to know
  before merging, then the base and head, the files, the commands and results, `#axiom_audit`, the
  placements, and the gathered and reused declarations.
