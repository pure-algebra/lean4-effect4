# State of the work

One page: what is true at HEAD, where the documents are, what is next, and what the owner must
decide. It is rewritten at every landing. History is `git log`, the rows of
`docs/core/decisions.md` and `docs/research/`. Counts, statuses and freshness come from
`make status`, never from this page.

## What this is

An agent-first language of algebraic effects whose engine is reified in Lean. One machine has
three faces. Lean proves it: the reference, the machine and the certificates. OCaml runs it
natively, compiled through LCNF. TypeScript joins the Effect ecosystem through the printer and
the readers. Programs are data: a canonical `Eff` tree with a digest and a typing certificate.
A program has folds, a journaled run with replay, and a printed image that reads back.

## Where the tree stands (2026-10-08, branch `refactor/phase1-phase3`)

- **Programs and their types.** The checker types a program with located refusal. The address
  table, the focus function and one annotating traversal give each address its environment and
  type (rows 296, 302 and 324). A template binds its parameters by the match by bounds (rows 303,
  306 and 315). It binds a row's request and a binder term alike: UNGUARD removed the guards.
  The approved eliminators read every union member of their input (P2b, row 325).
- **Data.** Records, required and optional reads, tags, string maps and fixed tuples are in the
  language. Integers carry, encode and compute inside the profile's bound (rows 316 to 322).
  Streams have their first profile (row 311). A Lean structure ties to its `Ty` by
  `deriving Modeled` (row 330, slice L1). Each of its values inhabits the derived type and
  survives JSON under codec admission, with no proof of its own.
- **Steps as data** (row 330). A module's step is data over typed inputs
  (`src/Effect4/Step.lean`). Named inputs, source arguments and binders share their declarations.
  The language supports captured folds, required records, typed empty values and deferred identity comparison.
  Shared list operations carry their value equations once.
  Reading, typing, frame and scope laws connect translated steps to their carrier interpretation under explicit premises.
  Semaphore, Pool and Queue retain independent model statements.
  Latch also has initial, registration and first-match cleanup connectors.
  The [foundation receipt](research/2026-10-08-seat-module-gaps-receipt.md) names the checks and remaining boundaries.
- **The machine and the session.** The frame machine agrees with the reference on a session
  (`session_eq_ref`, row 314), and the host meaning has its fast path (row 313). A session admits
  a host reply at its call's checked instance (row 323). The session's face is `Live.open`,
  `Live.start`, `Live.feed` and `Live.view` (row 326, DI-85).
- **The library's layout** (row 332, cutover slices C1 to C4). A user imports five entry
  modules: `Effect4.Author`, `Effect4.Run`, `Effect4.Emit`, `Effect4.Library` and
  `Effect4.Laws.Author`. Each re-exports and declares nothing. The acceptance programs import
  only these, and `#exposure_gate` refuses any other import. The step language is
  `src/Effect4/Step.lean`, and its shared laws are in `src/Effect4/Laws/Step/`.
- **Composed modules.** Queue, Semaphore, Pool, Latch, Stream and Ref have their models, cells,
  steps and operations in `src/Effect4/Library/`, and their laws in `src/Effect4/Laws/Library/`. Each
  keeps the module name and building blocks of latest (Effect 4.0.1) (row 335). Cache's profile is ruled
  (rows 270 to 272) and not built. The procedure is the
  [module factory plan](research/2026-10-05-claude-lead/module-factory-plan.md).
  A [native-module comparison](research/2026-10-08-module-compatibility-design.md) records finite target evidence and the selected profiles' differences.
- **Procedures** (row 328). A program may hold a definition block at its root, and an operation
  call invokes a definition by its declared row. The checker, program admission, the frame
  machine, the OCaml engine and M5 take a block (slices PROC-1 and PROC-2, the
  [receipt](research/2026-10-08-procedures-receipt.md)). The module printer prints a block's
  definitions as constants, and the reader reads them back (slice PROC-3, the
  [receipt](research/2026-10-08-procedures-proc3-receipt.md)). An author declares a definition
  once, and `Def.of` turns a library operation into a definition and its invocation. The Queue's
  operations are definitions too (slice PROC-4, the
  [receipt](research/2026-10-08-procedures-proc4-receipt.md)). `eff_module` now derives the
  authoring record, invocations and installation from one declaration list. Queue and Semaphore
  use it. The [authoring receipt](research/2026-10-08-module-authoring-receipt.md) records the checks.
- **Code generation.** The printer and the readers are driven by one table. The typed print has
  its slices P1, P2a, P2b and P3 (rows 324 and 325, the
  [receipt](research/2026-10-08-codex-unguard-receipt.md)). A call at a join carries its type
  arguments, and so does an approved eliminator site. The reader reconstructs the typed print
  after its named erasure. The application's print is not yet the typed print.
- **Partial programs** (R14, row 282). A sketch is a program with its hole table (row 291). The
  replacement law holds over the six typing judgments (row 294). A sketch reads a whole program,
  definition block included: its check, focus, fill, table and refusals (cutover slice S1). An
  edit that keeps its focus's type splices the address table, inside any part of a whole
  program (`edit-splices-table`, `module-table-splices`). A filled sketch is checked as its
  module (`module-holes-conservative`). A sketch has canonical bytes, so the query tool takes a
  hole table and gives back an omission's (`sketch-wire`).
- **The edit session** (row 334). `EditSession` (`src/Effect4/Program/Edit.lean`) keeps a sketch
  and its table, with the face `open`, `feed` and `view`. Its edits fill an address and omit
  one into a hole. A fill that keeps its focus's type checks only the new subtree, and an
  omission at the focus's type adds one entry (`omit-splices-table`). The session tool
  (`tools/Tools/Session.lean`, driver `tools/Drivers/Session.lean`) holds a session and its
  journal over JSON lines: open, fill, omit, view, undo, journal, sketch. Each answer names its
  laws. A program travels as canonical bytes or as its JSON print, the schema form an agent writes
  (`json-read-exact`). After any run of edits the view is the checker's answer on the
  sketch (`edit-session-coherent`). An edit can be undone exactly (`edit-session-undo`), and a
  spliced edit repaints only its subtree (`edit-repaint-set`).
- **Addresses** (seat ORG's [theory map](research/2026-10-08-seat-ORG-theory-map.md)). The laws
  that compose addresses stand in `src/Effect4/Laws/Program/Address.lean`
  (`address-composes`), with the path folds' naturality in their base (`path-fold-natural`).
  The checker is natural in its base too, so a subtree's table computed once stands at any
  address (`checker-base-natural`, `src/Effect4/Laws/Program/Typing/Rebase.lean`). A moved
  subtree's bytes, levels and layer-reference targets still depend on where it stands.
- **The proof graph.** A planned goal is a `proof_goal`, placed at a concept and a requirement
  (rows 203 and 207). `generated/semantics.md` derives every claim's status from its proof.
  `#load_report` and `#load_map` (`tools/Tools/LoadPaths.lean`) measure which theorems carry a
  registered claim, and a landing's reuse ratio (the [load paths note](research/2026-10-08-load-paths.md)).
  An unconsumed theorem is triaged before any removal.
- **The build.** The program and dogfood batteries run the machine as native code (row 327). A
  build prints only findings and the axiom gate's summary: reports print when a script asks for
  them. A battery restates no theorem (row 301); the cleanup pause of 2026-10-07 is closed, with
  Codex's review repairs merged (`docs/research/2026-10-08-codex-review-repairs-receipt.md`).

## The documents (read these; the rest is history)

| file | what it holds |
| --- | --- |
| `AGENTS.md` | the operating rules, and one line per core word into the dictionary |
| `docs/core/system-map.md` | the frame: the goal, the layers and their owners, the sorts, the arrow kinds, the requirements R1 to R14 |
| `docs/core/semantics.md` | the judgments by concept; the statuses are generated into `generated/semantics.md` (`make gen-semantics`) |
| `docs/core/controlled-english.md` | the writing rules and the dictionary (`make check-language`) |
| `docs/core/host-boundary.md` | the external-reply lane: host answers, handle declarations, the session lifecycle |
| `docs/core/decisions.md` | every decision, one list, with its status |
| `docs/core/api-surface.md` | the live surface and its open decisions |
| `docs/core/machine-state.md` | the machine's state and logs, transactions, the stateful modules |
| `docs/core/lcnf-route.md` | what the LCNF lowering handles and refuses |
| `docs/core/traversal-census.md` | every hand traversal by root, and the converter |
| `docs/DESIGN-ISSUES.md`, `docs/DESIGN-BASIS.md` | the open design questions, and the settled representation decisions |
| `docs/ARCHITECTURE.md`, `docs/GENERATED.md`, `docs/RUNTIME-COVERAGE.md` | the source tree, the generated groups, the runtime census |

## Next, in order

1. **Codex's module catalogue** on the new layout (the
   [catalogue brief](research/2026-10-08-module-catalogue-brief.md)), in latest's order of
   building blocks.
2. **The authoring line** (the [tangible authoring design](research/2026-10-08-tangible-authoring-design.md)).
   First the session tool as an MCP server. Then marking, after the design note's decision 3.
   Then each table entry's rule as data, and one session for editing and running.
3. **The module toolkit's gaps** (row 330): wrapper reply records and laws (G1), `derive_step`
   in the tree (G3), then the module form at the Latch (G2).
4. **The stream stack** (row 331): the pull protocol, then the channel as a pull transformer.
5. **The first composition law**, SynchronizedRef from Ref and Semaphore (G10), then the
   transaction attempt (G4).

Also open: procedures PROC-5 (row 328), the simulation's slices S1 to S4 (row 329), the session
API's slices (row 326), and H8.

## What the owner must decide

- **The simulation's first question** (row 329): what every schedule covers. Its questions 2
  and 3 take row 330's answer as their recommendation.
- **The frozen contracts' statement pins** (row 301, point 8; the
  [test census](research/2026-10-06-test-cleanup-census.md), proposal 4).
- **The claims record** (the [application packet](research/2026-10-07-packet-application-claims.md),
  section 5.3): five questions.
- **The host-lowering plan**: whether the plan of the branch `codex/host-lowering-plan` was
  ratified on 2026-10-04 (row 310).
- **Where the language stops computing**, beyond the line of row 309 (row 307).
- **The marks of an open part** in the proof graph view (row 308).
- **Seat ORG's three questions** (the [theory map](research/2026-10-08-seat-ORG-theory-map.md),
  section 7.1). Do a moved layer's references keep absolute targets? The recommendation is yes,
  with a rebase law. What keys a stored subtree? The recommendation is one node per program,
  until a table cache needs subtrees. Does a tool's named law count as load? The recommendation
  is yes, by theorems.

## Process

- Build what you touch (`lake build <Module>`). Run one `lake` at a time. The whole battery and
  `make check-full` run at a sweep, when the owner asks.
- Commit by explicit paths, each after a narrow build. Nothing is pushed without the owner.
- A new representation is a second file beside the old one, with its connector. The callers
  move, then the old one goes.
- `docs/core/` is the current authority. `docs/research/` is history, and the notes that
  matter are force-added.
