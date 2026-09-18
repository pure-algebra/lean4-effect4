# State of the work

One page: what is true at HEAD, where the current documents are, what is next, what the owner
must decide. Replaced at every landing; history is `git log` and `docs/research/`.

## What this is

An agent-first language of algebraic effects whose engine is reified in Lean. One machine,
three faces: Lean proves it (the reference, the machine, the certificates), OCaml runs it
natively (the same machine compiled through LCNF), TypeScript interoperates with the Effect
ecosystem (the printer and readers). Programs are data: a canonical `Eff` tree with a digest,
a computed typing certificate, folds, a journaled run with replay, and a printed image that
reads back.

## True at HEAD (2026-09-17)

- Branch `refactor/phase1-phase3`. `make check` green (build, roots, generated drift,
  catch-all arms, native, the TypeScript reader, the corpus pin); axioms `[propext, Quot.sound]`
  everywhere but the four meta modules the axiom gate names. `check-host` green after the
  corpus re-cut. CI: the workflow-file error that stopped every run since `78684a8` is repaired
  (`3a394912`, row 37), unverified until the owner pushes.
- The surface: `Api.Author` (`Author.build : Module → Except BuildRefusal Built`), `Effect4.Run`
  (`Run.open` cannot refuse; every convenience is a `List Command`; `journal_replays`,
  `drive_eq_play`), `Api.Supervision` (daemons as data), `Api.Inspection`. The alphabet is
  settled (`select`, `iterate`, `Decision`; `branch`/`whileLoop`/`callback`/`yieldError`
  retired; `gen` stays). Wire tags are stable (`tools/Effect4Gen/wire-tags.json`).
- Proved: `run_eq_meaning` on `Straight`, `loopAgreement` on `Looped`, meaning and loop type
  soundness, laws 11/12 and completeness of the printer/reader over the template table, scope
  safety by construction, the journal as a free monoid (`replay_unique`); the law of the
  projection (`explain = none ↔ effTy.isSome`) as the shape of one `Except`-valued fold
  (`Program/Typing/Agreement.lean`), its 370-line induction deleted.
- Measured (`#traversal_census`, `docs/core/traversal-census.md`): 87 hand traversals of the
  five free objects (`Eff` 34, `Ty` 17, `Term` 14, `Representation` 5, `Val` 17), down from
  93 once the hand blame walk was deleted. The converter `fold_of` (`Program/FoldOf.lean`, five
  shapes) has given 74 of them a fold and a kernel-checked connector beside the hand
  definition, at `[propext, Quot.sound]`; typing with located refusal is one `Except`-valued
  fold (`Program/Checker.lean`: a statement has a type; `effTy` its success, `explain` its
  refusal by definition, census §7.5, §7.7) and the term typer is the fold `argTy` (§7.6);
  the thirteen without are the ruled exemptions, `valCode`/`ofSchema`, and a derived instance
  (§7.4). That distance is the current work.

## The documents (read these; the rest is history)

| file | what it holds |
| --- | --- |
| `docs/core/ontology.md` | the frame: six sorts with one free object each, five arrow kinds with their obligations, coherence as a per-sort census; the probe of the "do now" rows; the Schema layer as the place to start over |
| `docs/core/coherence-principle.md` | scout F: the principle in full, the seven squares, the arrows lacking obligations |
| `docs/core/traversal-census.md` | the census numbers, every hand traversal by root, the converter design |
| `docs/core/decisions.md` | every open decision, one list (37 rows; 21 the owner's) with the order |
| `docs/core/api-surface.md` | the consolidated API and its awkward constructs |
| `docs/core/lcnf-route.md` | what the LCNF lowering handles and refuses; the LLVM-shaped architecture |
| `docs/DESIGN-ISSUES.md` | the DI register (rulings are made only when written here) |
| `docs/ARCHITECTURE.md`, `docs/GENERATED.md`, `docs/DESIGN-BASIS.md`, `docs/DESIGN-MAP.md`, `docs/RUNTIME-COVERAGE.md` | the tree, the generated groups, the DB register, the earlier five-layer map (superseded in substance by `ontology.md` §5), the runtime census |
| `AGENTS.md` | the operating rules and the vocabulary |

## Next, in order

1. **The converter's last shape** (`docs/core/traversal-census.md` §7.4): the grandchild under a
   container for `valCode`/`ofSchema` (two rows); then the callers move to
   `cata alg` (the checker's first: `explain`/`blame` and the projection law have moved and the
   hand blame is deleted; `effTy`'s consumers are the typing proof files, the next slice, after
   which `Typing.lean`'s block goes) and the hand definitions go at a good place. `compileEff`
   stays exempt.
2. **The simple rows** of the do-now set (`ontology.md` §2): 6 with exactness modulo
   annotations, 8, 23 as a delete, 24, 37, 17.
3. **The Schema layer** re-cut (`ontology.md` §3): the five files that carry the two real claims
   stay; the rest is converted where it is a fold or an embedding and deleted where it is
   neither; `Store.render` leaves `Shape.lean` first.
4. Group B of `decisions.md` (the digest, the Lean MCP driver) with the observation dogfood as
   the receipt; then group D (the TypeScript rules, the rung-3 reader, the vendoring order).

Scout G (third-party Lean tooling for this work) is out: `docs/research/2026-09-17-scout-brief-G-lean-tooling.md`.

## Owner decisions open

The 21 owner rows of `docs/core/decisions.md`, in the order its last section gives: rows 14 and
15 (the digest, the MCP server), then 2, 4, 7, 9, 10, 11; then 26–29 and 32; then 1, 30,
19–22. Rows 5 and 6 have the restatements `ontology.md` §2 gives (exactness modulo a named
normaliser).

## Process

- Speed over ceremony: build what you touch (`lake build <Module>`), `make check` once per
  step, `make check-host` per slice; nothing pushed without the owner.
- One Lean process per checkout; a parallel seat runs in its own worktree on disjoint files with
  a brief the owner has seen; scouts read `docs/research` from the main checkout by path and
  never copy it (2 GB of evidence trees).
- Build in parallel, slot in, delete at a good place: a new representation is a second file
  beside the old one with the connector (the agreement theorem), never an edit in place.
- `docs/core/` is tracked and is the current authority; `docs/research/` is gitignored, with the
  notes that matter force-added; `docs/agents/` and `COORDINATION.md` are gone.
