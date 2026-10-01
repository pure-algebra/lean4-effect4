# Seat T: the completeness census, so the type language is finished once

Read `README.md` here first. Your folder: `docs/research/2026-10-01-type-language-probe/T/`.
Worktree `/Users/pooks/Dev/lean4-effect4-probe-T`, branch `probe/T`. Read in full: the effect seat's
`note.md` §3 and §5 ("What the model cannot say today, by how often it is hit": thirteen items
ranked by the v4 application counts), its scripts and logs (`census_heads.py`, `member_histogram.py`,
`count_schema.py`, `sample_decode_sites.py`, `top_files.py`, `v4-app-files.txt`,
`research-ts-files.txt`, the 34-project corpus they read; rerun them, cite the logs); the synthesis
§3.2's stages 1–5 and "Not staged", §8 Q1, Q4, Q7, Q9; decisions rows 2 (closed into 119), 4, 46,
108, 109, 119–126, 130, 131 (`docs/core/decisions.md`); `DESIGN-BASIS.md` DB-15 (the value profile)
and DB-03; `docs/core/system-map.md` §1.1 (what a full program is, the three senses of signature),
§5 (the sorts), §8 (R1–R13 and their status); `docs/RUNTIME-COVERAGE.md` and the block printed by
`scripts/report-effect-runtime-coverage.sh` after `scripts/check-effect-runtime-census.sh` (run
both at your base; cite the block verbatim; the row families still absent or partial at `:119-140`);
`docs/core/machine-state.md` §6–§7 (how the rest of Effect's stateful modules land: Queue, PubSub,
the storage interfaces); `docs/core/host-boundary.md`; `src/Effect4/Program/Ty.lean` (the 20
constructors), `src/Effect4/Machine/Value.lean` and `src/Effect4/Store/Carrier/Val.lean` (the value
carrier), `src/Effect4/Program/Packages.lean` (the hand package tables, DI-89), `generated/
row-citations.tsv` (the rows and atoms cited against rc.112), the ingest recognizer's corpus
(`docs/research/` notes on foldlab's 34 projects; `ts/eff/ingest/`).

**The one thing.** The owner's instruction: when records land, land every other type form the
target profile needs, so `Ty`, `Val`, the faces and the mirrors are extended one time and the type
language does not reopen. Your census decides what "every other form" is, by measured frequency
and by what full reification of rc.112's program surface needs, and what else outside the type
language still blocks "full Effect semantics" (the runtime census's absent families, the stateful
modules, the host lane). Every row of your census names its evidence; nothing is "obviously
needed".

## Questions

1. **The form census.** For every type form rc.112 application code uses (start from the thirteen
   items of effect note §5 and the Schema member histogram; add the TypeScript-level forms the
   ingest corpus shows: `undefined`/`null`/`void`, `bigint`, `Date`, `symbol`, template literals,
   `readonly` arrays, tuples with rest, intersections, index signatures, generics in signatures,
   function-typed fields (refused by the carrier rule), branded types, `Option`/`Result`/`Exit`/
   `Cause`/`Fiber`/`Ref`/`Deferred`/`Scope`/`Queue`/`PubSub`/`Stream`/`Duration` as types):
   frequency (occurrences, files, projects, from the rerun scripts, with the five probe programs
   and the dogfood programs counted separately), what `Ty` has today, which synthesis stage covers
   it (1–5, "not staged", or none), what its landing needs in each layer (`Ty`, `Val`, `Fits`,
   codec, Schema, printer/reader, LCNF/OCaml, the checker, the generators), and a verdict:
   **critical** (p1–p5 or more than half the corpus projects need it and no spelling exists),
   **wanted** (a spelling exists but loses something: say what), **deferred** (rare, or refused by
   design with the reason), with the reason as a sentence a reader can check.
2. **The data wave's set.** From the census, the set to land together with records so the type
   language closes: at least records, optional keys, tagged unions of records, error payloads
   (row 120), keyed maps (row 125), numbers (`number`/`int` with row 108/109/121), and say for
   each whether it can share the record machinery (variable-arity generated folds, the canonical
   order, the type-directed faces) or needs its own. Recursive types (row 124), refinements
   (row 4), classes (row 2's `Σ_app` half), generic code over schemas (DI-89), in-program decode
   (row 123): in or out, with the measured reason. Produce the ordered commit series for the wave
   as a draft (the synthesis §7 series extended), with the dependencies between seats P, Q, R, S.
3. **What else blocks full reification.** Outside the type language: the runtime census's absent
   and partial families (run the report; which rows stay absent after M5–M7, and what model
   closes each); the stateful modules of `machine-state.md` §7 not yet in the tree (Queue, PubSub,
   the storage interfaces: what rows of the ingest corpus use them, how often); the host lane
   (row 96, TY-11); the `Effects`/`Layer` surface the corpus uses that the language refuses
   (`Layer.*` forms, `Config`, `Schedule`, `Stream`, `Sink`, `Metric`, `Logger`: count them; which
   are first-order rows by DI-89's route, which are host boundaries, which are out of profile by
   design). Rank by frequency; mark what is already ruled.
4. **Ergonomic codegen.** From the corpus's idiomatic signatures (the p1–p5 programs' TypeScript,
   the ingest README's forms): the printed spellings the faces must produce for each form in the
   data wave's set (interfaces or type aliases, `readonly`, `?:`, discriminated unions,
   `Data.TaggedError` classes for payloads, `Schema.Class`), checked with `tsgo` on files in your
   folder; the reader's inverse; what the current printer cannot say (cite `Codegen/Types.lean`,
   `Print.lean`). One table: form, spelling, printer today, reader today, gap.

## Deliverable

`T/note.md`: the census table (question 1) with its logs under `T/logs/`; the data wave's set and
draft commit series (question 2); the blocker list ranked (question 3) with the coverage block
verbatim; the codegen table (question 4); the proposed decisions rows (one row per form admitted
into the wave that has none; amendments to 120, 121, 124, 125, 131) and the one-paragraph "what
full reification still lacks after the data wave" for `docs/STATE.md`. Nothing lands from this
seat; the coordinator synthesizes.
