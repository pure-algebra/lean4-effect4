# Scout C brief — the MCP surface over the new application API (2026-09-17)

Owner's ask (verbatim intent): "get another Opus seat to do a deep dive into the MCP surface,
and what that's now actually going to look like here." This is a scout: a research note, not
code. The coordinator commits; you write `docs/research/2026-09-17-mcp-surface-scout-C.md`.

## What landed today, which the MCP face sits on

All on branch `refactor/phase1-phase3` at `d798feb2` or later. Read these first, whole:

- `src/Effect4/Api/Built.lean` — `Built`: table, program, admission certificate, row names.
- `src/Effect4/Api/Author.lean` — `Author.build : Module NativeOp → Except BuildRefusal Built`,
  `Built.typed`, the `Built` face (`ty`, `requires`, `closed`, `positionOf`, `run`, `runSync`,
  `print`, `bytes`); `BuildRefusal` (scope / typing / admission / serviceCarrier).
- `src/Effect4/Program/Authoring.lean`, `Program/Authoring/Services.lean` — `Module`, `RowDef`,
  `Row.host`, `Row.call`, `ServiceDef`, `Package`, the layer and fiber words, `daemon` syntax.
- `src/Effect4/Run.lean` — `Run` (built, budget, session, journal, phases), `Run.open` (cannot
  refuse), `Rows.*` as functions into `List Command`, `Run.play`/`step`, `Observation`
  (first-order, now with `fibers`), `Reactor σ`, `Run.drive`, `runPure`/`runClock`/`runWith`.
- `src/Effect4/Api/Supervision.lean` — `supervision : Eff Op → List ForkSite` (static tree),
  `FiberStatus`, `fiberStatuses`, `daemonsQuiet`, `Inspection.fibers`.
- `src/Effect4/Api.lean` — the older face: `check`, `Typed`, `Inspection` (renamed from `Run`
  today), `replay`, `run`, `explain`, `author`, `TypedLayer`, `checkLayer`, `schemaOf`.
- `src/Effect4/Api/HostSession.lean`, `Api/Runner.lean`, `Api/RunnerBytes.lean` — the checked
  session, the command alphabet (`bind | submit | apply | control`), the bytes boundary and the
  `schemas` list (which generated schema each boundary value already has).
- The laws you may cite as guarantees: `src/Effect4/Laws/Run.lean` (`open_total`,
  `journal_replays`, `drive_eq_play`, `drive_envelope`, `runPure_eq_run`),
  `Laws/Api/Runner.lean` (`replay_unique`: journals are the free monoid on commands),
  `Laws/Api/Supervision.lean` (`supervision_static`, `daemonsQuiet_iff`),
  `Laws/Program/Author.lean` (`build_table_lawful`, `build_rows_resolve`).
- The three seat receipts: `docs/research/2026-09-17-seat-{run,author,daemons}-receipt.md`
  (§ "owed" lists what is missing — the `Observation` codec O-8, `openBytes`, a concrete
  reactor, `Repr` on `Observation`).

## The prior plan you are refining, not repeating

- `docs/STATE.md` item 4 (R12): "the inspection protocol over MCP" — one `InspectOp` signature
  (`resolve`, `at`, `children`, `render`, `window`, `spans`, `locate`, `explain`, `blame`),
  served over MCP with object-typed success schemas, DevTools-Protocol shape; `evaluate`
  second; the `ToolSpec` table of the nineteen drivers. And the line under "The generated
  session as the engine's host API": a thin MCP driver over the session (start, step, reply,
  inspect, trace, blame), every response first-order data.
- `docs/research/2026-09-16-system-layout-and-abstractions.md` §4.14b (the owner's steer:
  everything inspectable through one small protocol).
- `docs/research/2026-09-16-generation-medium-workshop.md` (the `InspectOp` emitter as
  generated Effect TypeScript on bun).
- `src/Effect4/Codegen/Target.lean` (the JSON-document target: "JSON Schema, OpenAPI, the MCP
  list payloads, wrangler").
- `harness/truth/session/Keyed.lean` (`planRun`: the driver loop every host lane writes by
  hand — `Run.drive` is its Lean form now).
- `ts/eff/eff.gen.ts` (the generated `Schema.Struct` exports; what a response can already be
  typed as on the TypeScript side).

## Questions to answer, in this order

1. **The tool table.** For an agent holding an MCP client, list every tool the surface should
   expose, each as one row: name; input (which Lean type, which generated schema or which
   missing one); output (same); the Lean function it is (`Author.build`, `Run.open`,
   `Run.play`, `Rows.answer`, `Run.observe`, `Run.drive`, `supervision`, `Built.print`,
   `Api.explain`, …); its refusal shape (`BuildRefusal`, `Phase.refused`, …); and which law
   makes it safe to call. Prefer few deep tools over many shallow ones. Say which of R12's
   `InspectOp` commands survive as tools and which are projections of `Observation`.
2. **The run lifecycle over MCP.** A run is a value (`Run`), and a journal replays without a
   host (`journal_replays`). What does the MCP server hold between calls — the `Run`, the
   journal, the bytes of both? What is the identity of a run on the wire (`Run.id`, the bytes
   of `Built`)? Where does the reactor live when the *agent* is the host (the agent answers
   `Await`s through `Rows.answer`)? Write the exact call sequence for: author → build → open →
   start → observe → answer a call → flush → observe → replay from the journal.
3. **Every response is first-order data with an Effect Schema.** Check that claim against
   `Observation`, `Inspection`, `ForkSite`, `FiberStatus`, `BuildRefusal`, `Phase`, `Await`,
   `Command`: which already have a generated schema (`RunnerBytes.schemas`, `eff.gen.ts`), which
   need only "the structure's own group" in the generator (the run receipt's O-8 note), which
   hold a `Machine` and must not cross. Name the generator group each missing one goes in
   (`tools/Effect4Gen/*`, the Value+Runner groups of `docs/research/2026-09-17-runner-schema-
   codegen-plan.md`).
4. **What is generated, what is hand-written.** The server itself: generated Effect
   TypeScript on bun (the medium's plan) or a Lean `--run` driver in `Tools` (memory: native
   IO tooling is Lean `--run` drivers)? Give the recommendation with the reason, and what the
   generator must emit for it (tool specs from the table in (1), schemas, the client).
5. **The dogfood scenario.** One agent session, end to end, as the concrete MCP transcript
   (requests and responses as JSON, abbreviated), using the author battery's kv package
   (`Test/Program/AuthorContract.lean`, E2) as the program. Mark every response field that
   today has no schema or no codec.
6. **Decisions for the owner.** Numbered, each with your recommendation and the reason.

## Rules

- Work in your own worktree: `/Users/pooks/Dev/lean4-effect4-scout-c` (at `d798feb2`, with a warm
  build cache). Narrow builds are yours to run there — `lake build <One.Module>` for a probe
  module you write under your scratchpad or the worktree's `Test/`, `lake env lean` on a
  scratch file — never `lake build` with no target, never `make check`, and never a build in
  the main checkout `/Users/pooks/Dev/lean4-effect4` (one compiler per checkout). Probes that
  build are better evidence than reading; use them.
- Cite `file:line` for every claim about the tree. No name-hunting: if a thing does not exist,
  say "does not exist" and where it would go.
- The owner's vocabulary: **Run** (not Session); deep modules `Author` / `Run` / `Face`;
  programs as data; every boundary value carries an Effect Schema (D12); one program
  representation (`Eff`); no semantics duplicated outside the machine.
- The note is the deliverable, ≤ 450 lines, sections numbered as the questions above, a
  one-paragraph summary at the top. No artifacts, no commits, no edits outside
  `docs/research/2026-09-17-mcp-surface-scout-C.md`.
