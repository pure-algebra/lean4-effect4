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
| `docs/core/decisions.md` | every open decision, one list (status by row; rows 44–45 record the approved world and rows 78–83 the state/refinement proposals) with the order |
| `docs/core/language-cut.md` | the language as cut, every alphabet against Effect: terms (first order, twenty atoms, positional binders), types, values and errors, the 25 constructors, the absent modules; which gaps are profile rulings, which are cuts nobody decided |
| `docs/core/api-surface.md` | the consolidated API and its awkward constructs |
| `docs/core/lcnf-route.md` | what the LCNF lowering handles and refuses; the LLVM-shaped architecture |
| `docs/core/machine-state.md` | The state and log owners, proposed representation changes, conditional transaction profile, and shared basis for the surveyed stateful modules. Approved world and open choices are separated; the implementation plan and supporting research are tracked under `docs/research/` |
| `docs/DESIGN-ISSUES.md` | the DI register (rulings are made only when written here) |
| `docs/ARCHITECTURE.md`, `docs/GENERATED.md`, `docs/DESIGN-BASIS.md`, `docs/DESIGN-MAP.md`, `docs/RUNTIME-COVERAGE.md` | the tree, the generated groups, the DB register, the earlier five-layer map (superseded in substance by `ontology.md` §5), the runtime census |
| `AGENTS.md` | the operating rules and the vocabulary |

## Next, in order

**Design review before implementation resumes (2026-09-19).** The completed STM and stateful-API
research is reconciled in `docs/core/machine-state.md`, with the detailed contracts, retained
finite controls and proposed D0–D7 sequence in `docs/research/2026-09-19-state-refinement-plan.md`.
Rows 44–45 record the approved typed world; rows 78–83 remain proposals. The tooling branch
`codex/typed-state-tooling` was checkpointed as three commits on 2026-09-19 (it had built green
at its last edit) and is not yet merged. Set the storage/observation contract before pinning
the concrete obligation count; fast backends and new API families do not all block the milestone.
**The deep-dive review** `docs/research/2026-09-19-plan-deep-dive-review.md` (2026-09-19) re-cut
D0–D7 into slices with files, statements, deletions and red controls (plan §14): the tooling
merge T1–T5 first; then D2 as the first machine change (a deletion: completion cells hold data),
layer 1 as one world record ordered by `Stores.le`, the residual protocol under an answer gate,
`Keeps`, S1, S2 with the ledger's ceiling pinned there, S3. Proposals: row 84 (a first
transaction profile on the straight fragment, so row 80 does not block it) and row 85 (D5 as the
`Arena` interface over which the store kernel's laws are restated; no Lean `Array` instance).
The immediate priority is shared representations and composition laws. Known future modules
can reserve contracts with explicit missing implementations using the existing wanted machinery.
Supporting reviews and the paused tooling handoff are tracked in
`docs/research/2026-09-19-state-refinement/closeout.md`; none depends on retaining the design worktree.
The critique follow-up is tracked in `docs/research/2026-09-19-critique-response.md`, with Lean
proofs and reproducible probes beside it. It corrects the composition/compilation account and
identifies the driver-continuation contract needed before ownership across fuel frontiers.
The implementation/fusion audit is retained in
`docs/research/2026-09-19-implementation-audit-and-fusion-analysis.md`; its reviewed disposition
is in the current plan §13. D1–D7 now make replay budgets, DI-97 poll, wake/progress obligations
and actual target storage explicit. Existing fold laws remain available for local reuse;
decisions 34/40 still close the fusion/conversion campaign. No open semantic choice is ruled.

0. **The tooling-first waves, 1 and 2 landed** (2026-09-19). Wave 1: `f8517fa7`, `dfd94366`,
   `9e20cf9b`, `ee88efe2`, rows 59–66 (`1f1cc8e3`), the policy re-seed (`ba5286d3`); the coherence
   review `docs/research/2026-09-19-wave1-review-and-next-slice.md` (C1–C9). Wave 2: seat D
   `f6db74cf` (one compiler: tsgo drives every typing lane; the assignability differential, 600 pairs
   594 agree 6 cut 0 defect; rows and atoms against their exports; C6 answered by the target),
   seats E and V `5a44d83b` (the engine at twenty constructors through a one-pass chain and a mirror
   that refuses a lag; `fold_of` keeps the source's matcher, so `Val.hasTy_admitsSub` closes and
   `hasTy_sub` is the fold's corollary in the Laws with the core free of theorems about the order;
   `argsBelow_trans/antisymm`, the six `sub_*_of_ne` deleted), with the two seats' last slices inside the same
   commit (template laws, `matchTemplateArgs` home, hygiene 0.5/0.8/0.9; closure manifests, fatal
   frontier and module check, `roots.json`). Rows 67–72.
   The atoms slice landed (`49543b83`, `694f02d3`, `0b6b99a1`): all 33 atoms as rows; row 69
   option atoms as subsumption rows (`isSome` mono, `getOrElse` poly); the four L4-blocking atoms
   (`ite`, `some`, `none`, `mul`) and nine L3 atoms (`nil`, `cons`, `get`, `length`, `append`,
   `sub`, `div`, `mod`, `concat`); repeated parameters infer at TypeScript's common supertype;
   generic soundness is proved once through `Fits.instantiate`; template atoms checked at explicit
   instantiation in the rows lane (26 agree, all callable atoms judged); prelude unit list bug
   repaired. Receipt: `docs/research/2026-09-19-atoms-slice-receipt.md`. Rows 73–75.
   Receipts: `docs/research/2026-09-19-seat-D-receipt.md`; E and V have none (stopped by the owner
   for speed; their commit messages are the record).
   Tier 3 item 3.1 landed (`8f56ff1b`..`eea33606`): the store step kernel `refStepOf` and
   `SyncOp.refKernel` in `Laws/Machine/RefKernel.lean` (`refStep_eq_refStepOf`), with `step_typed`
   (from 229 to 51 lines), `refStep_length`, `refStep_valid`, and `refStep_keys` walking the
   twelve heap rows in one case through `refStepOf_keeps` and per-row kernel tables (−146 net
   lines); Row 76.
   Tier 3 item 3.5 landed: split `NativeOp.kind` off `row`; `compileEff` and `Straight` use
   `op.kind`; `Ty.scope` and `NativeOp.row` exit the LCNF engine closure manifest (`NativeOp.kind`
   at 13 instructions replaces `NativeOp.row` at 279); `roots.json` and `cases-policy.json`
   updated; Row 77.
   Scanner hardening for 3.3/3.4: type instances are visited separately; exhausted scans and
   unsupported recursive carriers fail; reads include opaque whole values and matchers;
   a copied field is unchanged only relative to an explicit source. The census now has 87
   positions and 95 source rows: 13 captured-name positions were previously skipped. The
   new rows use the existing stack, pending, journal and hook sources. Focused controls:
   `Test/Audit/PositionAnalysis.lean`; receipt `docs/research/2026-09-19-typed-state-tooling-receipt.md`.
   Direct declaration generation, structural frames and the shared evidence API now accompany
   the scanner repair. `#typed_state` replaces the source-file writer; the named TypedState
   bank has a red control. `Typed/Frames.lean` generates 60 checked frame rules: 159 clauses
   are reused and 40 are explicit premises across those rules. `ProofGraph` owns theorem
   references, search and the obligation join for Laws and Conform. The declaration-backed
   `#typed_state_obligations` checker rejects missing/stale entries and exceeded ceilings;
   its executable controls pass. No new TSV or generated source file is required.
   **These are structural tools, not the completed machine-preservation ledger.** Deriving
   the transition-specific goals and pinning their open count still needs the concrete
   predicate/world instantiation. The 40 premises are not a count of those future proofs.
   Still open from the plan: 1.11a span pinning, 4.4, 4.8/4.9 and Q4–Q6 with seat I's survey;
   from Tier 3: 3.2, 3.3, 3.4, 3.7. L2–L7 resume after Tier 3.
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

Row 39 (the Schema wipe) and row 41 (the typed-state invariant on the reference machine, the
core milestone, no shortcuts; design `docs/research/2026-09-18-typed-state-plan.md`, scouted, §6) are
ruled (2026-09-18); rows 34 and 40 are ruled out. HandlesFit with Val.hasTy unchanged and
per-cell Ref/Deferred typing, including memo cells, were approved on 2026-09-19 (rows 44–45).
The release rule is implemented (DI-94/row 47), and layer 0 exists in `Laws/Effects/Protocol.lean`;
its future upstream publication remains separate. Storage, observation, transactions and future
API choices are proposals in rows 78–85, consolidated from the completed research and the
deep-dive review. Step 0 of the milestone is landed
(`docs/research/2026-09-18-position-census-design.md` §3a): the position census, the source
table under a totality gate (87/87, two refusals named), layer 0, and the generated skeleton
`Laws/Program/Typed/State.lean`, elaborated in place and parametric in the carrier predicates
(the source-file writer is retired; `make check-typed-state` owns the focused group).
Owed: the concrete transition-obligation set and its pinned count, at M6 of plan §14 after M1
and M2. Open, in the order `decisions.md`'s last section
gives: group D (26–29, 32, 30's `compileEff`), then group B (14, 15) and 2, 7, 10, 11; then 1
with 3, and 19–22. Row 5 has the restatement `ontology.md` §2 gives.

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
