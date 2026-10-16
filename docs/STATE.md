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

## Where the tree stands (2026-10-13, branch `refactor/phase1-phase3`)

- **Programs and their types.** The checker types a program with located refusal. The address
  table, the focus function and one annotating traversal give each address its environment and
  type (rows 296, 302 and 324). A template binds its parameters by the match by bounds (rows 303,
  306 and 315). It binds a row's request and a binder term alike: UNGUARD removed the guards.
  The approved eliminators read every union member of their input (P2b, row 325).
  Variances are one semiring with a bivariant point (`Var4`, `src/Effect4/Program/Polarity.lean`),
  and a parameter's polarity in a template is one fold (`Ty.polarity`); the match's composition
  and the reference's reading are its images (VAR-1, the
  [polarity note](research/2026-10-10-openai-math-type-systems/README.md)). Every built-in row and
  atom scheme reads its parameters at co or bi in the answer, except `Ref.make` and `Ref.set`
  (VAR-3, `E4-POL-CE-001`, row 342). Instantiation respects polarity (VAR-2, `Ty.sub_instantiate_polarity`), proved.
- **Definitions whose parameter is a program** (row 340, slices HO-1 and HO-2, the
  [note](research/2026-10-09-program-parameters.md)). A definition declares its parameters, and
  `Eff.invoke` passes one program per parameter. The checker types each program at its
  parameter. Against `HasTy` it is sound and complete for the arm (`check_sound`,
  `check_complete`). The machine keeps the passed programs'
  sites on the point's stack; a parameter's run resumes at its site. The compile agrees with the
  reference denotation on both hops. The focus, the address table and typed replacement enter
  the passed programs. A typed point reads the parameters of its lexical scope, and its stack of
  sites is typed there (slices CX1 and CX2, the [note](research/2026-10-10-cx-lexical-scope.md)).
  The typed run of an invocation and of a parameter's run is proved (`invoke_arm`, `param_arm`).
  A layer reference stands in its target's scope: the same body, or both outside every body
  (decisions row 341, the note's §11). A block holds the module's layers as its third child, and
  every scope names a whole module layer by reference (step 2,
  [the note](research/2026-10-10-layer-scopes.md) §4.5 and §4.6). They print as module-level
  constants, read back, and an authored module with definitions declares its layers there. So M5
  and M7 rest on no goal. An ill-formed reference is refused at its site with the condition it
  breaks (`Eff.refFault`, `Api.explain`), and the tools' summary carries the whole refusal. A
  definition's parameters print as functions named by their declarations, and an invocation
  with programs as the definition's name on its request and its programs as arrows; both read
  back (HO-3a, HO-3b: one law of named rows for a block's and a body's spelling,
  `LawfulSpelling.extend`, and the laws of invocations, `LawfulInvokes`). A service method that
  takes programs takes them after its arguments and passes them on, and reads back (HO-5). An
  initial program that takes one is refused. A callback that needs a service is refused at
  its invocation until the header carries a requirement variable. A body's own layer is
  built once per call (step 3a, the owner's option B). A build is keyed by its path and the
  running call (`Point.layerKey`), which names the chain of invocation sites. A body's own layers
  print as constants at the top of its suspension and read back (step 3b). Three counted
  programs agree with rc.112.
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
  a host reply at its call's checked instance (row 323). It makes the call table once, at open
  (slice DM5, `5c01db4a3`). The face a caller holds is `Run` (`src/Effect4/Run/Basic.lean`).
  Row 326 rules the session's face, the module `Live` with `open`, `start`, `feed` and `view`
  (DI-85, the [session note](research/2026-10-07-session-api-design.md)). It landed in
  `src/Effect4/Run/Live.lean` with `view_funded` (DM6 and DM7 remain).
  No host answer is preloaded: every host call parks, and its answer is a decision (slice HC-2,
  row 343). The raw statement
  `run_eq_ref_table` is proved. A list of answers is a host that answers from a list
  (`Test/Api/HostList.lean`).
- **The host meaning on a run** (slices H8 and H9, row 310). `denoteRows_eq_session` and
  `denoteRows_eq_session_host` are theorems (`src/Effect4/Laws/Api/SessionMeaning.lean`). Their
  fragment is `StraightRows`, at every compile budget. A recorded run that is funded, at rest and
  host-driven observes the program's meaning under its reply tape (H8). A finished run observes
  the meaning under any host whose answers are the run's (H9). On loops both hold past a budget
  bound: `h8_loopedRows` and `denoteRowsB_eq_session_host`
  (`src/Effect4/Laws/Api/SessionMeaningLoop.lean`). Their meaning is `denoteRowsB`, the row
  meaning with loops cut at a budget, on the fragment `LoopedDataRows`
  ([the widening packet](research/2026-10-10-host-meaning-widening/README.md), slice L1). A
  waiting run names its wait too (`rows_loop_frontier`, slice L4,
  [the plan](research/2026-10-10-l4-frontiers.md)). Past a budget bound, the meaning waits at the
  machine's call, with the machine's stores. A host is a comodel of the row
  signature (`Effects.Comodel`), and the reply tape is one host. The driver `Run.runWith` meets
  H9's premises when its reactor stays inside the envelope and answers with exits
  (`runWith_denotes`, `src/Effect4/Laws/Api/HostDrive.lean`). A reactor behind its rows' types
  (`Reactor.guardRows`) meets the reply premises. It refuses a success that allocates, and accepts
  a failure that fits the error column. Funding, rest and a root exit stay premises. The row table's types are also a protocol of its hosts
  (`src/Effect4/Laws/Program/RowProtocol.lean`). Between decisions the machine is in one of four
  forms: loaded, parked on a yield, parked on a host call, exited
  (`src/Effect4/Laws/Program/Agreement/Hosted.lean`). Each host decision moves it to another,
  and the local run with calls moves the same way. One drive law serves H8 and the packet's
  theorem: `drive_seg` (`src/Effect4/Laws/Program/Agreement/Segment.lean`). It relates a segment
  of commands to the local run with calls and counts its steps. `run_eq_meaning` follows from it.
  The forward agreement with calls is proved once, on loops; the straight one is its instance
  (row 344). The six meanings of the call tree are instances of one algebra of control
  (`denoteCtl`, `src/Effect4/Laws/Program/DenoteCtl.lean`, row 344).
- **The coalgebra layer** (the [coalgebra note](research/2026-10-09-host-coalgebra.md), slices
  CO-1 to CO-6 and CO-7's generic half, row 338). The
  `Effects` package, version 0.10.0, holds systems, bisimulations, protocols and runs. It holds
  hosts as comodels, which compose by routing, renaming, admission, recording, and implementation
  by programs over other operations. Typed handlers compose (0.9.1), and indexed signatures give
  protocols of a higher order, where an answer opens operations (0.10.0). Branch `coalgebra`
  of `lean4-effects` is pushed (`bf5ab8f`, 2026-10-10) and pinned here. Any host of the row
  signature drives a run (`Reactor.ofHost`). A typed layer over a host that meets its lower
  protocol is its own guard in the denotation (`hostGuard_through`). The driver theorem still runs
  the guarded reactor (`runWith_layer_denotes`). A block's roles print as an Effect service's key
  and layer, and they read back (CO-6b's S1 and S2, rows 338 and 339, the
  [plan](research/2026-10-09-co6b-service-plan.md)). S3 checks a client that uses the Queue's
  service through its key, on tsgo 7 and rc.112. The Semaphore's service landed too, with Codex's
  service findings repaired.
- **The library's layout** (row 332, cutover slices C1 to C4). A user imports five entry
  modules: `Effect4.Author`, `Effect4.Run`, `Effect4.Emit`, `Effect4.Library` and
  `Effect4.Laws.Author`. Each re-exports and declares nothing. The acceptance programs import
  only these; `#exposure_report` lists any other import (the gate is retired, row 375). The step language is
  `src/Effect4/Step.lean`, and its shared laws are in `src/Effect4/Laws/Step/`.
- **Composed modules.** Queue, Semaphore, Pool, Latch, Stream, Ref, Pull, Channel, PubSub,
  PartitionedSemaphore and SynchronizedRef are built. Each has its model, cells, steps and
  operations in `src/Effect4/Library/`, and its laws in `src/Effect4/Laws/Library/`. Each
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
  after its named erasure. The application's module is the typed print, and every lane's module
  comes from one Lean writer (decisions row 392, P1).
- **The type interface** (the [type interface note](research/2026-10-11-type-interface/README.md)).
  `Ty` is the hub, and the JSON codec is its one exact image. A model of tsgo's assignability
  (`src/Effect4/Laws/Codegen/TargetOrder.lean`) agrees with tsgo on every recorded pair of
  `generated/assignability.tsv`. The TypeScript face refuses a natural literal above the profile,
  on emission and on reading (row 357). TypeScript and OCaml refuse a product outside the profile
  (`E4-RUN-CE-047`, repaired 2026-10-11). The printed type is not monotone (`E4-PRINT-CE-001`; row 346's repair A, with tsgo's bound).
- **Sketches** (R14, row 282). A sketch is a program with its hole table (row 291). The
  replacement law holds over the six typing judgments (row 294). A sketch reads a program with a
  definition block: its check, focus, fill, table and refusals (cutover slice S1). It refuses a
  layer reference, which program admission accepts. `Sketch.check`
  (`src/Effect4/Program/Sketch.lean`) checks the program as written, and the checker refuses `.ref`
  with `layerReference` (`Checker.checkLayer`, `src/Effect4/Program/Checker.lean`). The edit
  session's table refuses it too (`Annotate.checkLayer`, `src/Effect4/Program/Typing/Annotate.lean`).
  Row 373 (7) rules the repair: the sketch checks the expansion, as admission does, and reads the
  result back at the source's addresses (`source-annotation-agrees`). An
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
  is a look: a W3C design-token file, written as CSS for the web (`v -l LOOK`, `v -L`). Every
  run is kept with its page, which steps its SVG pictures as the window does (`v -H NAME`), and
  `v -G` lists every kept run.
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
  An unconsumed theorem is triaged before any removal. A cache of a fold is checked against the
  fold (`Effect4.Program.TyCache.check_agreement`, row 345). So are the axiom walk's distance
  summary (`#axiom_audit checked`) and the view's reachability table.
- **The machine's base laws** (row 350, the
  [machine-from-the-base note](research/2026-10-11-machine-from-the-base/README.md)). One native
  evaluation edits the evaluated fiber's frame by a word of eight moves (`iteration_moves`,
  `src/Effect4/Laws/Program/Moves.lean`), and its footprint on the run fiber keeps six fields
  (`iteration_footprint`). Every other fiber after an evaluation is an old one under three listed
  edits, or a new one (`iteration_interferes`). An iteration that does not finish is the same over
  more frames, with the same machine (`iteration_under`, `src/Effect4/Laws/Program/StackLocal.lean`):
  the evaluation's half of `compiled_region_bracket`'s premise. After any command, every fiber's
  frame followed from an old one by listed edits, or the fiber is new (`driveStep_framesFollow`).
  Five guard chains and the evaluation
  half of `MaskRuns` follow as instances (row 350). A raw context write let a checked program at
  a closed row die with `missingService` (`E4-CTX-CE-001`, now repaired). Row 349 ruled option A: a typed `context` reader and a `provideContext` region, landed on 2026-10-12.
  One ambient judgment types the machine's code (`AmbientProg`,
  `src/Effect4/Laws/Program/Typed/Residual.lean`). Every program's failure row is within its
  entry row, interruptible or not. Every clause of the typed state keeps it. A capture's release
  runs under its captured context merged over the current one (`releaseContext`, Effect's
  `provideContext`). It proves the four scope-close goals (the
  [release merge receipt](research/2026-10-12-release-merge-receipt.md)). A countdown observer acts
  only when its record waits on the firing fiber (`Pending.waitingOn`, row 376 (2)), as in rc.112
  and 4.0.1. So `Evaluating.countdown_parks_positional` is proved, and M6 and M7 rest on no goal.
  The printer spells a pair of a union as a union of pairs (`E4-PRINT-CE-001`, row 346, ruled).
- **Shared accounting** (row 355). A stack ledger states once what the goals lane re-proved per
  scenario: consumed plus held is at most produced, along every reachable machine
  (`src/Effect4/Laws/Machine/Ledger.lean`, `src/Effect4/Laws/Program/LedgerRun.lean`). The
  finalizer custody law is its first instance. Place funding states the command step once for
  any budget (`PlaceFunding.command_funded`, `src/Effect4/Laws/Program/PlaceFunding/`); the
  source-opportunity budget is its instance. The other ledgers move to it, and each merge is
  audited for consolidation (`docs/research/2026-10-11-machine-models/AUDIT.md`). The driver's
  helpers are words of one edit alphabet (`src/Effect4/Laws/Machine/Edits.lean`). Edits of
  another fiber's record apply after the running fiber's write-back, so a fiber that interrupts
  itself exits interrupted, as rc.112 does (`E4-RUN-CE-046`, repaired).
- **The first-exit race** (row 352). `raceAllFirst` selects the first observed entrant exit and
  awaits the losers' cleanup before the parent sees it, as rc.112 does. It repairs the timeout form.
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
| `docs/core/controlled-english.md` | the writing rules and the dictionary (`make check-sweep`) |
| `docs/core/host-boundary.md` | the external-reply lane: host answers, handle declarations, the session lifecycle |
| `docs/core/decisions.md` | every decision, one list, with its status |
| `docs/core/api-surface.md` | the live surface and its open decisions |
| `docs/core/machine-state.md` | the machine's state and logs, transactions, the stateful modules |
| `docs/core/lcnf-route.md` | what the LCNF lowering handles and refuses |
| `docs/core/traversal-census.md` | every hand traversal by root, and the converter |
| `docs/DESIGN-ISSUES.md`, `docs/DESIGN-BASIS.md` | the open design questions, and the settled representation decisions |
| `docs/ARCHITECTURE.md`, `docs/GENERATED.md`, `docs/RUNTIME-COVERAGE.md` | the source tree, the generated groups, the runtime census |

## Next, in order

**PROC-6 landed** (row 379; merged `36ddb0b56`): `h9_blocks` is proved, with the context family at every scheduler budget. **Build first** (owner, row 387): the general theory of module composition (rows 382 to 386) pauses. Its findings are kept in [the modelling check](research/2026-10-14-proc-close/modelling-check.md) §8. **Next, in order** ([the work streams note](research/2026-10-15-workstreams/README.md), 2026-10-15). Done: the gate consolidation (`370300fba`), cleanup S3 (merged `5729f839b`; `make check-ocaml` passes) and A1, rc.112's persisted Schema documents (`54d5552e5`). The types landing is done too (row 399; [its receipt](research/2026-10-15-type-roundtrip-audit/receipt.md)). It adds the Schema arms of `number`, `null`, `undefined` and `bytes`, and the aliases `Int` and `Num`. The effect types read back, `eq` holds at `bool`, `Modeled` takes sum types, and a row takes named parameters. The lowered to-do host now types under ocamlopt. (1) V3's prelude package, the diagnostics over shipped modules, the checked bank entry and the host-handle rule. (2) P1/LC-6's native to-do: the lowered host run now runs under dune and matches Lean byte for byte (`ocaml/engine/test/todo/`). The engine takes the row table, admits a reply as Lean's checked replay does, and runs under `E4_host`, which reproduces Lean's host run, with a repository written in OCaml too ([the report](research/2026-10-15-lowering-state/README.md), §6.11). (3) CR-5's names and CR-10's type repairs. [The types audit](research/2026-10-15-type-roundtrip-audit/README.md) §8 recommends four type slices, a table of type declarations first. Row 400 unparks recursive types, and [their probe](research/2026-10-15-recursive-types/README.md) sizes that slice. (4) The local CR-6 folds and CR-7's fusion. (5) A2 to A5 and P2, then P3, P4, A6 and A7. (6) The concrete proofs on their path: custody, M1, M2, the outline driver, Atomic, Timeout and the queue crew; then SCOPE-1 and CONC-1. A service is a record of closures held as data (row 381 (3)), and a module's instance is one (row 382 (2)).

0000. **The vertical slice: the to-do application end to end** (decisions row 378; the
   [lowering note](research/2026-10-13-lowering-vertical-slice/README.md) and the
   [ergonomics probe](research/2026-10-13-agent-ergonomics-probe/README.md)). The to-do is
   proved and run in Lean only. `agrees` and `conforms` (`src/Effect4/Laws/Program/Validated.lean`)
   decide its claims' premises on one recorded run, so a real run is checked run by run. In order:
   - the agent's small fixes in the tools. Answers carry no hex unless asked, and the session's
     JSON is named. A fill at a missing address is refused, and the catalogue's gaps are filled.
     A refusal names its definition and parameter, and the session tool adds `"run"`;
   - done: V1, the to-do on the keyed lane and lane S (`4017fac26`, `2daa3ac55`). On each script
     rc.112 and the generated OCaml engine agree with Lean;
   - done: V2, the application as one Effect service with its layer. Its host rows are services
     of their own (row 378 (19), (20), (22); the
     [design note](research/2026-10-13-emitted-services/README.md)). The to-do's file reads back
     whole (`ab8aeefa7`). `make check-ts` runs its 13 scripts on rc.112 through a
     consumer, and Lean decides each run's checks (`210424144`). A key that a service row names
     prints by the service's name and reads back by it (`"TodoRepo"`, row 378 (22));
   - V3, the generated declarations: the rows' bindings interface, the inputs' and answers'
     Schemas, the prelude package. They are also the agent's typed surface;
   - done: V4, `apps/todo/` on SQLite with the per-run checker, in `make check-ts`. A
     run from an empty database passes Lean's checks on each request, and four red controls fail
     the checks they target;
   - beside them, binder names in the TypeScript reader (row 378 (17)). `request_leads` is
     proved, so the recorded call tree rests on no goal. The
     claim record's two labels landed (`13551903c`), and `ClaimRecord` and `Bank.Entry` live in
     the core and join the semantics report (row 378 (23)). The banked Ref cache and its
     transfer law `cache_agrees` rest on no goal (`23f95aac2`, `f463ee53b`). The cache block
     prints as `ListCache` (HO-5) and reads back (`Ref.Ref<A>` in definition headers). The cached
     to-do imposes it (`bindWith`), proves `cached_list_after_add` on the built module, reads
     back whole, and runs in `apps/todo/` (row 378 (8));
   - then V5, the OCaml face, its repository lowered through LCNF.

   Planned goals off the slice's path pause (row 378 (12)).
000. **The runtime differences the probes found** (research notes named `2026-10-12-probe-`). The
   probes of 2026-10-12 rank each difference from Effect by its outcome in real code. Fix those
   that change an outcome; record the rest. Items 2 and 1 of the
   [alignment plan](research/2026-10-12-probe-alignment-plans.md) landed (row 359, the
   [receipt](research/2026-10-12-close-mask-receipt.md)). As in Effect 4.0.1, an explicit
   `Scope.close` masks its closer. The failure walk adds a recorded interrupt past a skipped
   mask. Items 3 and 4 keep rc.112's behaviour. Item 5, the operation counts, waits: 5a first.
   The restore slot is retired (the
   [slot scout](research/2026-10-12-restore-slot-scout.md); owner, 2026-10-12). The positional
   countdown goal is proved (seat COUNTDOWN's
   [receipt](research/2026-10-13-seat-countdown-receipt.md)).
00. **The last planned goals** (the [goals packet](research/2026-10-10-goals-packet/README.md)).
   Codex reached its quota on 2026-10-12, and Claude carries its lane
   (`docs/research/2026-10-11-machine-models/CODEX-PROMPT.md`). `#plan_status` gives each
   application goal's standing (`Test/Dogfood/Scenario/`). Seat GOALS-2 proved `WriterHistory.evaluation` on 2026-10-13
   ([receipt](research/2026-10-13-seat-goals2-receipt.md)), so `Atomic.cleans_once` is proved.
   `Atomic.atomic` now rests only on `Atomic.Store.shop_stages` (the receipt's §7).
   `Workers.Assertions.logs_step` and `QueueWorkers.Assertions.logs_history` stay open. In both
   scenarios a release note writes the acquired value that its environment binds, so their count
   needs a fact about values. Seat FLOW carried the frame-level answer flow through whole
   histories (`PlaceFunding.NativeFlow.history`, its
   [receipt](research/2026-10-13-seat-flow-receipt.md)). The four goals that need it stay open:
   these two, `Timeout.cleanup_keeps` and `Timeout.retries_declared`. Next: those four through
   it, then the rest of the GOALS-2 receipt's §8 (`request_leads` is proved). The packet also sorts the open parts that no goal states yet. Beside it: the legacy host
   fixtures of the truth lane move to the keyed lane (row 343 (8), signed until then). Seat FC's
   rulings land too (row 345 (2): `tools/Tools/Graph` at height 0; the generator's children
   induction).
0. **The authoring line** (row 373 (1); the
   [obligations note](research/2026-10-13-authoring-obligations/README.md) orders the rest). The
   `Live` face landed: `Live.open`, `Live.start`, `Live.feed` and `Live.view`, with
   `view_funded` (seat LIVE's [receipt](research/2026-10-13-seat-live-receipt.md); DM6 and DM7
   remain). In order:
   - landed: a definition block in the meaning, PROC-5 (row 328; `src/Effect4/Laws/Program/Block.lean`),
     and `denoteRows_invoke`, `denoteRows_call` and `denoteRows_provideContext` on the row meaning.
     Next on that line: `run_eq_meaning` extended to blocks, and the general inlining law (PROC-6);
   - landed: one checked replay route. `Typed.replay` feeds a journal through the checked
     session (`Live.replay_at_call_instance`, `Live.replay_recorded`; rows 98 and 373 (8); seat
     REPLAY's [receipt](research/2026-10-13-seat-replay-receipt.md));
   - landed: the application and claim records (row 336 (9); seat CLAIMS's
     [receipt](research/2026-10-13-seat-claims-receipt.md)). Four of the to-do claims are proved,
     and `Todo.serves` is proved now that `request_leads` is;
   - generics and Pool's service, HO-4
     ([the plan](research/2026-10-09-program-parameters.md), row 340).

   Row 376's four more seats landed on 2026-10-13. FLOW is above, and COUNTDOWN closed M7.
   APPCHECK checks a sketch through its layer references (`SourceSession`), and the session tool
   opens at an application. ADDRESS proved `references_move` and stores a program's content at
   kind `program`. Their receipts list the duplicates they found, for one consolidation pass.

   CX3 and CX4 wait for a consumer: the typed run goes through sites, not through an inlined body
   ([the note](research/2026-10-10-cx-lexical-scope.md) §8). Codex's scout of a keyed layer after
   Effect's `LayerMap` (row 341) is parked, and so is its further review of the `Effects` packet.
   Codex reached its quota on 2026-10-12. After them stand CO-7's Effect4 half (handle rows and
   call sites as worlds) and HC-6, the immediate-answer lowering of the
   [host-call note](research/2026-10-09-host-calls-and-cleanup.md). DM7 and HC-7, the checked
   session on OCaml, come after the first share (row 373 (2)). The deep dive's ranked list (§6)
   orders the rest of the host session, holes, authoring and lowering.
0. **The studio** (row 362; the [designer workflow note](research/2026-10-12-designer-workflow/README.md)).
   One served page in the app's browser pane shows each new view entry, the looks, the PC's probes
   and the documents, and reloads by itself. DS-1 the studio and its reload, DS-2 the scrubber and
   strips, DS-3 inline pictures with a look switch, DS-4 the keyed diff, DS-5 the document specimen.
   The documentation site (rows 363 and 364) is live at `https://effect4-docs.pages.dev`, deployed
   by `make deploy-site`. It is one value whose pages the semantics report is split into, each page
   in a typed shell with the site's navigation. Its first semantics page is the open work: each
   planned goal with its docstring, and each modulo theorem's chain to it. Next: the design and
   semantics grill. The C player stays first-class (row
   363, point 5). The tube language (rows 369 to 374) and its pegs port left the view on
   2026-10-14, at the owner's word; the code stands at the tag `archive/tube-language`. Of the
   [motion plan](research/2026-10-13-motion-everywhere/README.md), M1 stays: each figure's cost and
   a documentation page's limits (`tools/Tools/View/Measure.lean`). The PC's graph work is merged:
   connectors as one closed perimeter (`tools/Tools/View/Connector.lean`), and the graph's checks,
   regions, packing and inspectors. The kit's tube went too (its ruling R-S59, tag `archive/tube`).
   The kit is pinned at its `html/svg` (`3e5e79335`), which GitHub does not hold yet.
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
   - the design language of documents (row 354), in five slices (the
     [design language note](research/2026-10-11-docs-design-language/README.md), section 7). D1
     writes its authority in `docs/core/`. D2 gives one token source, status by shape and no
     organic noise by default. D3 adds the figure and the motion value, D4 automata, and D5
     Mermaid. Then the [view model](research/2026-10-11-view-model/README.md)'s R-V1 to R-V5.
   MCP and code mode: slice M1 (typed requests) lands now, with the note's rulings 1 and 2 made
   (row 373 (9)). Rulings 3 to 6 wait for the owner's walk-through.
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
   Editing and running stay two sessions, an edit session and a host session, with the same verbs
   (row 373 (5)). One operation joins them: it builds a sketch with its hole table and opens a host
   session on it. When an author asks whether a result depends on the schedule, the checked
   fragment of row 361 (D1 to D3) answers. Random descent is in the law graph (`random-descent`).
   The line's parts:
   - the session tool at an application: `open` takes the row table and the services as canonical
     bytes (row 373 (10));
   - a sketch typed through its layer references (row 373 (7));
   - the session tool as an MCP server;
   - marking at a gap (row 336, point 3);
   - each table entry's rule as data.
6. **The module toolkit's gaps** (row 330): wrapper reply records and laws (G1), `derive_step`
   in the tree (G3), then the module form at the Latch (G2).
7. **The stream stack** (row 331): the Pull protocol's handlers (Codex, merged at `b8630762`) and the
   channel's transforms (`34e516559`) are landed. Next: stateful filtering and early stopping,
   which need repeated-pull, empty-batch, index and lifetime contracts.
8. **The first composition law**, SynchronizedRef from Ref and Semaphore (G10), then the
   transaction attempt (G4).

Also open: the simulation's slices S1 to S4 (row 329), and the session note's DM6 after DM3. The
host session is to be drawn by H8's machine forms. Effect4 pins the SVG kit (lean4-whatwg
`html/svg` at `a8a8e7b`, slice S24, rows 358 and 370; `ec25409f4`), a branch local until the owner
pushes it. The view's pictures are typed trees on it (`tools/Tools/View/SvgOut.lean`). Row 360
orders the rest after its pin move: the motion port and the geometry port. They delete the view's
own join, easing reader, samplers and stroke geometry. The owner's note of 2026-10-09: write a
program, then watch its session answer calls and schedule.

## What the owner must decide

Row 380 decided the parked rulings of the view, MCP and the type interface, and the vendoring
list, under the owner's delegation of 2026-10-14. HarfBuzz 14.6.0, FreeType 2.15.0 and ThorVG
1.1.2 are vendored by pin beside termbox2 and SDL3 (`vendor/`). Each has a `fetch.sh` that refuses
a tarball whose SHA-256 differs, and FreeType's checks its signature too.

- **Pushing the kit** (`pure-algebra/lean4-whatwg`, branch `html/svg` at `3e5e79335`). A checkout
  other than this Mac's seeds `.lake/packages/whatwg` from the local kit until then.

## Process

- Audit a landing's modules with `#axiom_audit M …` (`tools/ProofGraph/AxiomAudit.lean`), the
  gate's walk. Lean 4.33's `collectAxioms` can omit an axiom behind a cycle of the dependency graph.
- Build what you touch (`lake build <Module>`). Run one `lake` at a time. The whole battery and
  `make check-full` run at a sweep, when the owner asks.
- Commit by explicit paths, each after a narrow build. Nothing is pushed without the owner.
- A new representation is a second file beside the old one, with its connector. The callers
  move, then the old one goes.
- `docs/core/` is the current authority. `docs/research/` is history, and the notes that
  matter are force-added.
