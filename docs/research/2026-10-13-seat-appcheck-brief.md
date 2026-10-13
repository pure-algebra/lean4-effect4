# Seat brief: checking at a real application (seat APPCHECK)

Status: brief (history, not authority). 2026-10-13. Decisions rows 373 (7) and (10), 376 (1).
Obligation O2 of `docs/research/2026-10-13-authoring-obligations/README.md`.

**The one thing to know first.** The edit session runs at the empty application
(`tools/Tools/Session.lean`), and its check refuses a layer reference that program admission
accepts. So no agent can edit a real program through the tool. Row 373 (7) rules the route: check
the expansion (`Eff.expandRefs`, `src/Effect4/Program/Refs.lean`), and read its table at the
source's addresses. The law is `source-annotation-agrees`. Row 373 (10) rules how a request carries
its application: the row table and the services as canonical bytes in `open`.

## Read first

- Seat BACKLOG's deep dive (`docs/research/2026-10-13-backlog-deep-dive/README.md`), §2 and its
  questions 7 and 8; Codex's live-graph theory (`docs/research/2026-10-10-live-graph-support/THEORY.md`),
  `source-annotation-agrees`.
- The tree: `src/Effect4/Program/Typing/Annotate.lean`, `tools/Tools/Session.lean` and
  `tools/Tools/Session/`, `Eff.expandRefs`, the edit session's laws (`EditSession.reached_view`,
  `Sketch.annotate_eq_table`, `Sketch.table_fill`).

## What to build, in order

1. `open` takes an application: the row table and the services as canonical bytes, decoded with
   the existing codecs.
2. The sketch's check at that application, through layer references: the expansion checked, its
   table read back at the source's addresses.
3. The law `source-annotation-agrees`: at each source address, the reported type is the
   expansion's type at the address it maps to. Place it first (`AGENTS.md`, "Trust").
4. A battery: a real scenario's program (one with layer references) edited through the tool, and a
   red control where a reference's target misfits.

## Reuse first (row 376 (3))

- Before any new definition or lemma, search: `git grep` by the concept, `#why`, the registry, and
  `#auto_census` on the module you touch. The expansion's address map may exist already in
  `Refs.lean` or the layer view. List what you reused in the receipt. A duplicate is a defect.
- Proofs use aesop and its banks (`src/Effect4/Laws/Auto/RuleSets.lean`) where they close.

## Boundaries

- Worktree: `~/Dev/lean4-effect4-appcheck`, branch `seat/appcheck`, made by the coordinator.
- Edit `src/Effect4/Program/Typing/**`, `tools/Tools/Session.lean`, `tools/Tools/Session/**`, new
  law modules under `src/Effect4/Laws/Program/`, `Test/**`, and the root imports at their end. Read
  `src/Effect4/Program/Refs.lean` and never edit it (seat ADDRESS). Never edit
  `src/Effect4/Program/Authoring/**` (seat CLAIMS), `lakefile.toml`, `docs/core/**` or the registry.
- Every `lake` through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`, narrow. Every reader of
  a changed definition builds before its commit. Commit by named paths. Never push or merge. Stop
  under 8 GiB free.
- Stop at a question of meaning or at about six hours. The receipt
  `docs/research/2026-10-13-seat-appcheck-receipt.md` (force-added) names first the one thing to
  know before merging, then the base and head, the files, the commands and results,
  `#axiom_audit`, the placement and the reused declarations.
