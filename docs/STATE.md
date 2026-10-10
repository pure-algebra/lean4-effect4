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
- **The host meaning on a run** (slices H8 and H9, row 310). `denoteRows_eq_session` and
  `denoteRows_eq_session_host` are theorems (`src/Effect4/Laws/Api/SessionMeaning.lean`). Their
  fragment is `StraightRows`, at every compile budget. A recorded run that is funded, at rest and
  host-driven observes the program's meaning under its reply tape (H8). A finished run observes
  the meaning under any host whose answers are the run's (H9). A host is a comodel of the row
  signature (`Effects.Comodel`), and the reply tape is one host. The driver `Run.runWith` meets
  H9's premises when its reactor stays inside the envelope and answers with exits
  (`runWith_denotes`, `src/Effect4/Laws/Api/HostDrive.lean`). A reactor behind its rows' types
  (`Reactor.guardRows`) always does. The row table's types are also a protocol of its hosts
  (`src/Effect4/Laws/Program/RowProtocol.lean`). Between decisions the machine is in one of four
  forms: loaded, parked on a yield, parked on a host call, exited
  (`src/Effect4/Laws/Program/Agreement/Hosted.lean`). Each host decision moves it to another,
  and the local run with calls moves the same way. One drive law serves H8 and the packet's
  theorem: `drive_seg` (`src/Effect4/Laws/Program/Agreement/Segment.lean`). It relates a segment
  of commands to the local run with calls and counts its steps. `run_eq_meaning` follows from it.
- **The coalgebra layer** (the [coalgebra note](research/2026-10-09-host-coalgebra.md)). The
  `Effects` package, version 0.10.0, holds systems, bisimulations, protocols and runs. It holds
  hosts as comodels, which compose by routing, renaming, admission, recording, and implementation
  by programs over other operations. Typed handlers compose (0.9.1), and indexed signatures give
  protocols of a higher order, where an answer opens operations (0.10.0). It is committed on
  branch `coalgebra` of `~/Dev/lean4-effects` and pinned here, unpushed: push `lean4-effects`
  before this branch. Any host of the row signature drives a run (`Reactor.ofHost`). A typed
  layer over a host that meets its lower protocol needs no guard (`runWith_layer_denotes`).
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
- **The view** (rows 336 and 337; the [visual pipeline note](research/2026-10-09-visual-pipeline.md)).
  A picture is data in Lean: a page, its drawing calls and their device calls, each with the key
  of its object (`tools/Tools/View/`). A move by whole pixels commutes with the lowering
  (`lowerCall_move`), so the motion between two frames is exact. The frames of a program built
  by edits replay any session request file through the session tool. `tools/view/v NAME` plays
  them in a window; SVG and the console are two more outputs of the same calls. Each page shows
  the program's TypeScript beside its tree. A graph of any shape lays out by ranks
  (`ranks_forward`), with cycles as back edges and every edge a curve. A run draws its fibers as
  one (`v -r NAME`). A step ends at exactly the next frame (`sample_end`). Every choice of style
  is a look: a W3C design-token file, written as CSS for the web (`v -l LOOK`, `v -L`).
- **The view's folds** (the [algebra audit](research/2026-10-09-view-algebra-audit.md)). A map
  that commutes with each layer commutes with the fold (`cata_fusion`). Several readings of a
  program are one fold (`cata_prod`). A program's lines anywhere are its lines at the root, moved
  (`lines_at`).
- **The program's own graph** (the [design note](research/2026-10-09-program-graph-design.md)):
  a fold of the program, drawn in UML's notation, with every wait (`v -F`). Its layout's laws are
  proved for every flow: each part is well formed (`lay_good`), every edge descends
  (`place_descends`), boxes stand apart (`place_apart`). What a flow orders first stands above
  (`place_keeps_order`), through the algebraic graph and Mokhov's axioms. Lines are organic
  strokes by growth rules, their width bounded by proof (the
  [organic strokes note](research/2026-10-09-organic-strokes.md)). MCP and code mode are designed
  (the [MCP note](research/2026-10-09-mcp-code-mode-design.md)).
- **The generated code** (`tools/Drivers/Emit.lean`): one module per program, with exact
  imports, a header and Effect's width; all eight corpus modules pass tsgo 7. TypeScript's syntax
  has a generated fold (`TsFold`). The pinned printer is one of its algebras (`render_eq_expr`)
  and the readable layout another; laid flat, the layout is the house print (`flat_fold_expr`).
  The printer's known hazards are latent, and their repairs are placed as laws (the
  [JavaScript audit](research/2026-10-09-js-semantics-audit.md); ECMA-262 vendored at
  `vendor/ecma262-es2026/`).
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

0. **The host session as a coalgebra** (the
   [coalgebra note](research/2026-10-09-host-coalgebra.md), slices CO-1 to CO-7). CO-1 to CO-5
   landed, and CO-6's typed protocol and its law at the driver. Left in CO-6: a reactor that
   names its row (a core change, batched), so `Effects`' constructions drive runs. Then CO-6b
   prints a verified handler as an Effect service, and CO-7 adds promises. Codex reviews the `Effects` packet. HC-2, HC-6 and HC-7 of the
   [host-call note](research/2026-10-09-host-calls-and-cleanup.md) stand.
1. **The view and the printer**, one plan across four notes. The order:
   - the program's own graph (row 337, point 9). First its design, with an agent's place in it.
     Then the graph, its ranks and its places as folds of the program (the algebra audit's D);
   - the printer's conformance (the JavaScript audit): J1, precedence from the vendored grammar;
     then J2 to J7 in lean4-typescript; then J9's reader; and slice F2;
   - the marks of row 337: arrowheads, depth as a fold (slice E), the secondary tone, the code's
     token classes;
   - the algebra audit's slices B, C and G: the build as layers, the splice law, the run's forks;
   - flags by one table (row 337, point 8); a look's density; transpose in the order;
   - a module's cell drawn by its type; the span map as a source map (J8); interaction; termbox2.
   MCP and code mode: the note's slices M0 to M12, after the owner's six rulings.
2. **The requirement statuses**: the prose of `docs/core/system-map.md` section 8 lags the
   measured table of `generated/semantics.md` (R10, R14); refresh it from the table.
3. **The graph operations of an agent** (row 336, points 1 and 7). Pieces are stored by content
   address. An agent searches by type and by explanation, and wraps, extracts and inlines, each
   shown as frames.
   Seat ORG's L9 (`rebaseRefs`, point 6) and its rank 5 (a program in the store) come first.
4. **Codex's module catalogue** on the new layout (the
   [catalogue brief](research/2026-10-08-module-catalogue-brief.md)), in latest's order of
   building blocks.
5. **The authoring line** (the [tangible authoring design](research/2026-10-08-tangible-authoring-design.md)).
   Its parts: the session tool as an MCP server; marking at a gap (row 336, point 3); each table
   entry's rule as data. One session edits and runs.
6. **The module toolkit's gaps** (row 330): wrapper reply records and laws (G1), `derive_step`
   in the tree (G3), then the module form at the Latch (G2).
7. **The stream stack** (row 331): the Pull protocol's handlers are landed (Codex, merged at
   `b8630762`); next the channel as a pull transformer.
8. **The first composition law**, SynchronizedRef from Ref and Semaphore (G10), then the
   transaction attempt (G4).

Also open: procedures PROC-5 (row 328), the simulation's slices S1 to S4 (row 329) and the
session API's slices (row 326). The host session is to be drawn by H8's machine forms. The
owner's note of 2026-10-09: write a program, then watch its session answer calls and schedule.

## What the owner must decide

- **The vendoring list** (row 336, point 5): the C libraries of the
  [visual pipeline note](research/2026-10-09-visual-pipeline.md), section 6. Each is confirmed at
  its own repository before a download.
- **The marks of an operation** (the forms note's proposal A, 1): drawn in the view by each
  operation's row, and removed by `v -P`.
- **The program's graph** (the design note, section 7): its marks, built as recommended, to
  confirm. What a line's width means: the organic strokes note, section 4.
- **MCP and code mode** (the MCP note, section 10): six rulings.
- **The coalgebra note's three questions** (its section 8). Is `Effects` the home of the generic
  layer? Is Codex the breaker of its packet? Should the comodel and runner papers be filed?

## Process

- Read a declaration's axioms with the gate's walk (`exactAxioms`, `tools/ProofGraph/Axioms.lean`).
  Lean 4.33's `collectAxioms` can omit an axiom behind a cycle of the dependency graph.
- Build what you touch (`lake build <Module>`). Run one `lake` at a time. The whole battery and
  `make check-full` run at a sweep, when the owner asks.
- Commit by explicit paths, each after a narrow build. Nothing is pushed without the owner.
- A new representation is a second file beside the old one, with its connector. The callers
  move, then the old one goes.
- `docs/core/` is the current authority. `docs/research/` is history, and the notes that
  matter are force-added.
