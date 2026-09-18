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
  safety by construction, the journal as a free monoid (`replay_unique`); the checker sound and
  complete against `HasTy` at every path, `explain = none ↔ effTy.isSome` and weakening as
  corollaries of one `Except`-valued fold (`CheckSound.lean`, `Typing/Agreement.lean`), the
  two hand inductions that proved them deleted.
- Measured (`#traversal_census`, `docs/core/traversal-census.md`): 78 hand traversals of the
  five free objects (`Eff` 28, `Ty` 17, `Term` 11, `Representation` 5, `Val` 17), down from
  93 once the hand blame walk, the hand checker and the hand term block were deleted. The
  converter `fold_of` (`Program/FoldOf.lean`, five shapes) has given 65 of them a fold and a kernel-checked
  connector beside the hand definition, at `[propext, Quot.sound]`. The checker is one
  `Except`-valued fold (`Program/Checker.lean`): `effTy` and its siblings are its success at
  the root by definition (`Program/Typing.lean`), `explain` its refusal, and the typing proof
  graph is stated for it at every path (`Laws/Program/Typing/CheckSound.lean`; census §7.5,
  §7.7, §7.8); the term typer is the fold `argTy`, `termTy` its projection at `false` (§7.6,
  §7.9). The thirteen without are the ruled exemptions, `valCode`/`ofSchema`, and a derived
  instance (§7.4).

## The documents (read these; the rest is history)

| file | what it holds |
| --- | --- |
| `docs/core/ontology.md` | the frame: six sorts with one free object each, five arrow kinds with their obligations, coherence as a per-sort census; the probe of the "do now" rows; the Schema layer as the place to start over |
| `docs/core/coherence-principle.md` | scout F: the principle in full, the seven squares, the arrows lacking obligations |
| `docs/core/traversal-census.md` | the census numbers, every hand traversal by root, the converter design |
| `docs/core/decisions.md` | every open decision, one list (40 rows; 18 the owner's; reviewed row by row against HEAD on 2026-09-18, a status column) with the order |
| `docs/core/api-surface.md` | the consolidated API and its awkward constructs |
| `docs/core/lcnf-route.md` | what the LCNF lowering handles and refuses; the LLVM-shaped architecture |
| `docs/DESIGN-ISSUES.md` | the DI register (rulings are made only when written here) |
| `docs/ARCHITECTURE.md`, `docs/GENERATED.md`, `docs/DESIGN-BASIS.md`, `docs/DESIGN-MAP.md`, `docs/RUNTIME-COVERAGE.md` | the tree, the generated groups, the DB register, the earlier five-layer map (superseded in substance by `ontology.md` §5), the runtime census |
| `AGENTS.md` | the operating rules and the vocabulary |

## Next, in order

1. **The fold work stops here** (owner, 2026-09-18): the checker, the term typer and the
   fragments landed (census §7.5–§7.10); the thirteen exemptions — the compiler's five, the
   reference evaluator's five, `valCode`, `ofSchema`, the derived instance — stay as they are and
   are tracked in census §7.4. No census gate, no fusion, no conversion for uniformity's sake.
2. **Row 39** (ruled): `EffectfulField` first, then `Check`/`Accepts`/`Image`/`schemaOf`, the
   `Annotations` trim, the `render` move. Then the simple rows still open: 8 (in the move), 23 as
   a delete, 24, 17, 16.
3. **The Schema layer** re-cut (`ontology.md` §3): the five files that carry the two real claims
   stay; the rest is converted where it is a fold or an embedding and deleted where it is
   neither; `Store.render` leaves `Shape.lean` first.
4. Group B of `decisions.md` (the digest, the Lean MCP driver) with the observation dogfood as
   the receipt; then group D (the TypeScript rules, the rung-3 reader, the vendoring order).

Scout G (third-party Lean tooling for this work) is out: `docs/research/2026-09-17-scout-brief-G-lean-tooling.md`.

## Owner decisions open

Row 39 (the Schema wipe) is ruled (2026-09-18); rows 34 and 40 are ruled out (no gate, no
further conversion). Open, in the order `decisions.md`'s last section gives: row 41 restated as
the concurrent alphabet's meaning statement (the list of API-backing obligations awaits the
owner's confirmation), then group D (26–29, 32, 30's `compileEff`), then group B (14, 15) and 2,
7, 10, 11; then 1 with 3, and 19–22. Row 5 has the restatement `ontology.md` §2 gives.

## What row 39 does (for the owner, 2026-09-18)

- *Trim `Annotations.lean` to the carrier*: of its 1,193 lines the estate uses `AnnotationKey` (a
  typed key: a name and the codec of its payload, two laws), the two keys `identifierKey` and
  `refKey`, and the lens `Representation.nodeAnnotations` — all from `Store/Shape.lean`'s
  `renderDef`. The rest is the "annotation data plane": bag operations, lenses on every node
  kind, and a 650-line `AnnotationTraversal` with four laws that nothing calls. The carrier types
  themselves (`AnnotationEntry`, `Annotations`) already live in `Payload.lean`. Kept: about 150
  lines. `Data/Optic.lean` stays (`Document.lean`'s two lawful traversals use it). Row 2(c) puts
  record and sum names in annotations, through exactly the `AnnotationKey` that is kept.
- *Move `render`*: `Store.render : Shape → Representation` is the schema arrow out of the store's
  value descriptions (the Q5 table: `nat` to `number` with `isInt`, `bytes` to a hex-pattern
  string, a `sum` to a union of tagged structs). Not a visual rendering. It lives in
  `Store/Shape.lean`, so the Store module imports the whole Schema tree; the sort order runs the
  other way. It moves to `Schema/OfShape.lean` beside `Bridge` (the arrow out of `Ty`); Store
  becomes a leaf (`Val`, `Shape`, the byte codec, `ShapeDoc.print`); row 8's key dedupe lands in
  the move.

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
