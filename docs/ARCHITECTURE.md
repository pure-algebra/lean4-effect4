# Effect4 architecture

The measured map is `make gen-architecture`'s report, `.lake/gen/architecture-map.html`: every
area of the tree at its declared height, the imports between them as the parser reads them, the
typed-state proof stack as it lands, the file map by role, and every import against the direction
this document states. It is regenerated from the tree when wanted and never committed
(`docs/GENERATED.md`, group `architecture`); the roles and the layering it checks against are
declared in `tools/Tools/ArchitectureRoles.lean`. This document is the prose; the map is the
measurement.

## Dependency direction

```text
effects (external: signatures, programs, laws)      typescript (external: syntax, rendering)
        |                                                    |
Data (Row, Json, Optic, Ascii)      Machine (Cause, Exit, FiberId, supervision vocabulary, ServiceKey)
        |                        |                          |                              |
Machine: the frame alphabet (Prim, PrimInterp, FrameFiber) and the Scope state machine
        |
Machine: the fiber machine over the frames; its stores (the memo world included); the service map and the fiber context
        |
Program: Eff (the program IR), typing, printer, native alphabet, compile to frames
        |
Api: the application face (type, print, compile, run; Schema syntax)
Program (the authoring surface) -> Modules: the words of a step term and the shared waiting wrapper, then the composed modules (the cell and the steps of the Queue, of Semaphore and of Pool, and the first operations of the Queue and of Semaphore)

Effect4: Api and the functional utilities, including Config / ConfigValue / Provision
Machine and Program -> Effect4.Laws: the separate proof graph; no reverse import

Schema (carrier, annotations, checker, authoring) -> Codegen (profile, Schema generation)
Store (Val, one byte codec, Canonical, Kind, Ref, node, store, word, traits)
Arch (JSON numbers, structural acceptance of Schema documents)

OCaml5 (lake library, src/OCaml5): the OCaml 5 / js_of_ocaml runtime model, the OCaml
language model, library carriers, the LCNF backend, the Machine descriptions; imports
Effect4.Machine and Effect4.Api; Tools and Conform.Effect4 consume it -> ocaml/ (the dune workspace)

Tools (lake library, tools/Tools): Effect4-side --run drivers over Program,
Codegen, OCaml5.Eff.World and Test.Program.Gen; runtime and Laws do not import them
Conform (tools/Conform): generic reflection/checking below its Effect4-specific adapters;
OCaml5.Lcnf consumes the generic Source/Lcnf utilities, never Conform.Effect4
```

Arrows point from what is imported to what imports it. `Api` imports the
Program and Schema faces; callers and selected batteries import `Api`. From `Program`,
`Machine` imports only the type data a record term stores, `Program.TyCore` and `Program.TyEq`
([record contract](research/2026-10-03-data-language/record-contract.md)). It never imports
`Eff`, typing or the checker. The persisted Schema data plane stays below Machine. The type-directed
boundary in `Schema/Codec` sits above Program's value admission and uses Machine's
existing value images; `Api` imports that boundary, and its proofs live under
`Laws/Schema/Codec`. Machine does not import the boundary. The external packages are pinned
by exact commit in `lakefile.toml` (`effects`, `typescript`, and `hash` for the
store's SHA-256). Effect4 depends on them, never conversely, and re-declares
none of their carriers. `Codegen.Types` projects normalized core types into the
dependency's structural `TypeRef` and parses the supported legacy type strings at
that boundary. It does not import the renderer; stored `Ty` and `Row` data remain
unchanged. The target carrier retains source annotations and binding distinctions
for validation above the canonical expression reader.

Lean's module system (decisions row 200) covers 116 core modules outside `Laws`: those that reach
no package or only `hash`. Such a module opens with `module`, imports with `public import`, and declares in
`@[expose] public section`. A proof edit inside one leaves its importers fresh. Seven
specialization sites and their importers stay non-module (decisions row 202, ruled (a)). `Laws`,
the core modules that reach `effects` or `typescript`, `Test`, `tools` and `OCaml5` stay non-module. The audit roots stay non-module too, so the
axiom gate reads every proof body, and the gate refuses a module root.

## Source tree

The retained Schema boundary contains the raw carriers and authoring constructors,
`Bridge` for the program type arrow, `Codec` for type-directed JSON, and `OfShape`
for the Store shape arrow. Row 39 retires the separate field-admission judgment,
program image, annotated-field generator and recursive annotation traversal.
Pure `Store/Domain/Shape` imports no Schema module; `Store/Domain/Canonical` owns
`Canonical.document` through `Schema/OfShape`, and Domain/Node/Genesis retain
schema-node and address construction. (`Schema/Transform` and `Schema/Endpoint`,
the second authoring plane, were deleted on 2026-09-18 under the ontology note §3.)

| Area | Responsibility |
| --- | --- |
| `src/Effect4/Data` | requirement rows, JSON, lawful optics |
| `src/Effect4/Machine` (`Cause.lean`, `Exit.lean`) | `Cause` and `Exit`, the error channel everywhere |
| `src/Effect4/Machine` (`Fiber.lean`, `Supervision.lean`) | `FiberId`; the fork, observer, scope and race vocabulary the machine speaks |
| `src/Effect4/Machine` (`Completion.lean`) | the external answer data and Ref key, below both the scheduler and stores |
| `src/Effect4/Machine` (`Key.lean`) | `ServiceKey`, its universe and transport |
| `src/Effect4/Machine` (`Frames.lean`, `Scope.lean`) | the rc.112 frame alphabet and single-fiber step, and the `Scope` state machine |
| `src/Effect4/Machine` (`Fibers.lean`, `Wake.lean`, `Timer.lean`, `Stores.lean`, `ContextMap.lean`, `Context.lean`) | the reference fiber machine (`RunMachine`, `drive`, `replayEval`, `runSyncExit`), the shared wake protocol (`WakeList`, `Owed`, `WakeMode`; DB-13), the logical clock (`TimerStore`, the `advance` decision; DB-14), the stores including the memo world, the service map and the fiber context |
| `src/Effect4/Laws/Machine` | the frame and store invariants, value images, scope restoration, clause theorems and witnesses; resumable fuel, observation and scheduling laws; composition and execution receipts |
| `src/Effect4/Program` | `Eff`, `typeOf`, the native operation alphabet, `compile` and `interpOf`; `Ty.lean` owns raw type data, constructive ordering, normalization and checked canonical representatives, with semantic membership laws in the separate Laws graph; `Provision` — the requirement algebra (`Row.diff`), the layer signature `LayerTy` and its laws, the build specification and its totality theorem, and the docs deployment as compile-route runs (`docs/research/2026-09-04-provision-algebra.md` (untracked working note)); the layer term `LayerTerm` is a member of the `Eff` family since the join of 2026-09-07 (`Eff.lean`), typed in `Typing.lean` and compiled by path (`Compile.lean`'s `compileLayer`: a layer is a subterm, its identity its path, its build `EffName` continuations at Points); `Config` — rc.112's `ConfigProvider` as a fallback monoid under a path-transformation action, the `Config` reader with its tri-state resolution, dotenv substitution with fuel, and the configuration requirement row (`docs/research/2026-09-04-production-standards-spike.md` (untracked working note)) |
| `src/Effect4/Api` | the one application-facing module |
| `src/Effect4/Laws/Program` | value typing and progress, denotations, agreement and simulation; the term scheduler, evaluator, replay and observations; `RuntimeR.replay_rel` relates loaded frame/reference machines for every tape and compile/command budget, while `beh_eq_ref` compares their observations under sufficiency receipts. `Laws/Program/Signature.lean` holds the application signature as data (`SigApp`, `SigExtends`, `LawfulSig`; rows 111–116). `Laws/Program/Typed/` is the typed-state proof graph in import order: `Membership` (values, the one module that cases on `Ty`), `Residual` (the protocol-typed program judgment and the posts), `Adequacy` (the handler-adequacy rules, between `Residual` and `Stack`), `Contracts` and `Stack` (frames closed under world growth, the walk), `Scheduler`, `Assembly` (the assembled state and the ledgers), `ExitConnector` (the bridge to the meaning layer's `ExitHasTy`), `Seq` (the `seqR` sequencing lemma); `M3bWorld`'s ledger report and audit run at the foot of `Assembly.lean`, where its last goal (`preds_savedOk_mono`) is declared |
| `src/Effect4/Modules` | the composed modules: programs over the authoring surface, in a layer of the runtime root above `Program` (decisions row 255). `Queue/` holds the Queue's cell (`Cell.lean`: its type at a message type, and its initial value) and its six step terms (`Steps.lean`). Each step is one pure term over the cell's value. It holds the first operations too (`Ops.lean`): `bounded`, `offer`, `take`, `poll` and `size`, each a library program over the steps. The module exports no row, and it adds no handle type: a queue's handle is its cell's `Ref`. The pieces of a step term that name no module are in `Words.lean`, and the shared pieces of a module that waits are in `Waiting.lean` (their rows below) |
| `src/Effect4/Modules/Waiting.lean` | the shared pieces of a module that waits, in the namespace `Effect4.Modules` (decisions rows 221, 238 and 240). It holds the posted helper's options (`posted`) and the builder that posts one helper for each request of a list (`postAll`). It holds the cleanup on interruption (`onInterrupt`), the wait at a mask's restore site (`waitAt`), and the wrapper in its two forms (`waitRetry`, `waitAnswer`) over a module's `Waiter`. It holds the wrapper at a caller's restore (`waitRetryAt`), and the protected body (`protectedBy`): one mask over the acquisition, the hook and the body (decisions row 276). Every binder is minted. The Queue's operations are its first user, and Semaphore's are the second |
| `src/Effect4/Modules/Words.lean` | the pieces of a step term that name no module, in the namespace `Effect4.Modules`. It holds `idTy`, the type of a request's identity and of a hint that carries nothing. It holds the words, one application of a native atom each, and the removal pass `removeById`. It holds a list that a term writes out (`single`, `front`, `listOf`). The Queue, Semaphore and Pool read them here |
| `src/Effect4/Laws/Modules` | the laws of composed modules (decisions row 255). Five files name no module, and each has its row below: `Table.lean`, `Reading.lean`, `Checking.lean`, `Store.lean` and `Waiting.lean`. `Queue/` holds the Queue's abstract transition model (`Model.lean`), its capacity statement (`Capacity.lean`), and its first profile with the profile's closure (`Profile.lean`). It holds the typing statements of the cell and of the steps (`Typing.lean`), and the relation between the cell and the model (`Relation.lean`). It holds what the cell's records and the Queue's passes read (`Reading.lean`), and the six step statements (`Steps.lean`). It holds the laws of the first operations (`Ops.lean`): scope, the attempt laws at each operation's own step term, and the typing of each operation at every scope |
| `src/Effect4/Laws/Modules/Table.lean` | the encoding table of a module's relation (`Table`): each model identity's handle and its current hint. It holds `Table.Injective`, and the one change of a step (`Table.renew`). A module's own function of the table stays in the module's folder |
| `src/Effect4/Laws/Modules/Reading.lean` | the judgment `Reads`, and the capture of a caller's term under a fold (`Captured`). It holds what each authoring builder, each native atom and each word of a step term reads. It holds the reading rule of `removeById` |
| `src/Effect4/Laws/Modules/Checking.lean` | the judgment `Types`, with `TypesEach` and the typed capture `CapturedTy` (decisions row 257). It holds what each authoring builder and each word types at, and the typing rule of `removeById`. It holds the checker's answer at a scope of names (`typeAt`). The checker's rules that it applies are in `TermIntro.lean` (its row below) |
| `src/Effect4/Laws/Modules/Store.lean` | the connectors of a step term to the store: one atomic update (`step_updates`), the typed half (`step_keeps_cell`) and the read law of a cell (`cell_read`) |
| `src/Effect4/Laws/Modules/Waiting.lean` | the laws of the shared pieces of a module that waits. Each piece keeps the scope judgment. A name that `bindWith` mints is a caller's term of a row's step, for values and for types. The typing at every scope is here too: a typed scope (`TypedScope`), a term that keeps its type under the surface's binders (`Kept`), and a program that answers a type (`Answers`). It holds what each builder and each row of a cell answers, and the typing of the posted helpers, of the cleanup and of the wait. A program at any effect type has its own judgment (`Has`), for a protected body. The wrapper is typed once over a module's part (`Waiter.Typed`, `waitRetryAt_answers`, `waitRetry_answers`), and the protected form has its rule (`protectedBy_has`) |
| `src/Effect4/Laws/Program/Typing/TermIntro.lean` | the term checker's rules in their introduction form: from the parts' types to the whole's type (decisions row 257). It holds one rule for each node of `argTy`, the native calls at a symbolic type, and a record and a tuple in normal form. It names no module |
| `src/Effect4/Modules/Semaphore` | Semaphore's cell (`Cell.lean`: its type, and its initial value at a total) and its five step terms (`Steps.lean`): take or enrol, take if available, release, one visit of the wake's walk, and withdraw (decisions rows 259 to 261 and 265). Each step is one pure term over the cell's value. The words and the removal by identity are shared (`src/Effect4/Modules/Words.lean`). It holds the first operations too (`Ops.lean`, decisions rows 260 and 276): `make`, `take`, `release`, `takeIfAvailable`, `withPermits` and `withPermitsIfAvailable`. Each is a library program over the steps and the shared wrapper, and the walk of a release is one too. The module exports no row, and it adds no handle type: a semaphore's handle is its cell's `Ref` |
| `src/Effect4/Laws/Modules/Semaphore` | the laws of Semaphore's cell and steps (decisions row 265). It holds the abstract transition model (`Model.lean`), and the first profile with its closure and two facts of a visit (`Profile.lean`). It holds the typing statements of the cell and of the steps (`Typing.lean`), and the relation between the cell and the model (`Relation.lean`). It holds what Semaphore's records and passes read (`Reading.lean`), and the five step statements (`Steps.lean`). It holds the laws of the first operations (`Ops.lean`): scope, the typing at every scope, and the attempt laws, one for each step of an operation. The judgment `Types`, the reading rules, the table and the connectors to the store are the shared files of `src/Effect4/Laws/Modules` |
| `src/Effect4/Modules/Pool` | Pool's cell and its five step terms (decisions rows 267 to 269). `Cell.lean` holds an item's type and the cell's type at a resource type, and the initial value at a list of resources. `Steps.lean` holds the steps: lease or enrol, return, one selection of a wake, withdraw, and the close's first step. Each step is one pure term over the cell's value. The words, a written list and the removal by identity are shared (`src/Effect4/Modules/Words.lean`). The module performs no effect and exports no row. The public operations come with the wrapper's slice |
| `src/Effect4/Laws/Modules/Pool` | the laws of Pool's cell and steps (decisions rows 267 to 269). It holds the abstract transition model (`Model.lean`), and the first profile with its closure (`Profile.lean`). That file holds the model's facts too: of an enrolment, a selection, a return and the close's first step. It holds the typing statements of the cell and of the steps (`Typing.lean`), and the relation between the cell and the model (`Relation.lean`). It holds what Pool's records and passes read (`Reading.lean`), and the five step statements (`Steps.lean`). The judgment `Types`, the reading rules, the table and the connectors to the store are the shared files of `src/Effect4/Laws/Modules` |
| `src/Effect4/Program/Authoring/Mask.lean` | the mask that restores, as a derived form over `bind` (decisions rows 244 to 246): the builders `uninterruptibleMask` and `uninterruptibleMaskWith`. The form adds no constructor and no wire tag |
| `src/Effect4/Laws/Program/Authoring/Mask.lean` | the mask's two builders keep the authoring scope judgment (`uninterruptibleMask_scoped`, `uninterruptibleMaskWith_scoped`) |
| `src/Effect4/Laws/Program/Typed/Mask.lean` | the mask's three claims at the typed state: the saved image's membership (`saved_mask_image_membership`), the body of a restore site (`scoped_body_substitution_boundary`), and the flag at the boundaries of regions (`saved_mask_restoration`). The file states no run-level bracket |
| `src/Effect4/Laws/Codegen/Mask.lean` | the mask's two rows keep the template table's premises (`mask_rows_table_premises`), and the profile of the mask's printed form (`mask_printed_form_profile`) |
| `src/Effect4/Laws/Machine/MaskDiscipline.lean` | the saved mask's chain on a fiber's stack (`MaskChain`): at one fixed base bit, the restoring frames alternate from the negation of the flag. One placed theorem holds the statements (`saved_mask_pop_discipline`). The frame machine's pop from an empty scratch stack, `getCont`, the finished frame's path `Machine.frameExitState` and the entry of each region keep the chain. Two fibers with one base and one stack have one flag. The file states no law of a run. It imports no module of `src/Effect4/Laws/Program` |
| `src/Effect4/Laws/Machine/MaskRuns.lean` | the saved mask's chain at every live fiber of a run (`MaskRuns`), over a table of start flags that is proof data. A step of the frame machine keeps the chain, and a pop that answers nothing ends at an empty stack and at the base. Each command keeps the invariant under the condition on `Cmd.exitDone` (`ClearReady`), and the command loop discharges it through `Machine.Lift`. One placed theorem holds the statements at the frame evaluator (`saved_mask_chain_runs`). The file states no bracket of a region |
| `src/Effect4/Laws/Program/MaskRuns.lean` | the same invariant at the compiled program's interpreter, under the native evaluator (`compiled_mask_chain_runs`, the pointer of the registry claim `saved-mask-chain-runs`), and at the entries of `src/Effect4/Api.lean` and `src/Effect4/Program/Admit.lean` that return a machine |
| `src/Effect4/Laws/Api/MaskRuns.lean` | the same invariant at the host session, the runner with its rows of bytes, and the run API: each entry that returns a machine keeps it, with no premise for the condition |
| `src/Effect4/Laws/Machine/MaskBracket.lean` | the bracket of a region in its general form (`saved_mask_region_bracket`): the chain of the own frames over the entry's stack (`MaskChain.append_iff`), the pop of two lists of frames, a frame step over more frames (`step_under`), and the region's end (`regionEnd`, `RegionEnds`). Two machines that hold `MaskRuns` at tables in the prefix order give the bracket for a fiber that is live at both cuts (`MaskRuns.bracket`) |
| `src/Effect4/Laws/Program/MaskBracket.lean` | the bracket at the cuts of a compiled command loop (`LoopCut`): a fiber that a pending command steps has not exited (`stepped_live`, the pointer of the registry claim `stepped-fiber-live`), each command gives a cut again, and a region ends at its entry's stack and at its entry flag (`compiled_region_bracket`, the pointer of `saved-mask-region-bracket`) |
| `src/Effect4/Laws/Program/ReferenceExpansion.lean` | the reference expansion leaves no reference: a program whose layer references are well formed (`Eff.layerRefsWF`) expands to a program with no reference site, at the bound of `Eff.expandRefs` (`expanded_refs_nil_of_wf`). It holds one law of the generated folds at the seven sorts, with its two instances: one round (`Eff.refSites_expandRound`), and a layer's sites under a longer path (`LayerTerm.refSites_append`). It holds the budget of the rounds (`RefsWithin`). The rank of a path and the facts of the path fold that it uses are in `PathOrder.lean` and `PathFold.lean`. The file states nothing about a run: the compile redirects a reference, and it does not expand |
| `src/Effect4/Schema` | the persisted Schema data plane; `Codec` is the type-directed JSON boundary above Program, with exact value admission and a conservative shared-layout test for subtype agreement |
| `src/Effect4/Codegen`, `src/Effect4/Ingest` | the pinned Effect v4 profile, `print`, the Schema and annotated-field generators, target/artefact definitions, and the Ingest taxonomy |
| `src/Effect4/Store` | the content-addressed store as one trait (`docs/research/2026-09-04-cas-trait-plan.md` (untracked working note)): `Val` the value tree and its one exact byte codec, `Canonical α` (shape, `toVal`, `ofVal`, three laws), including `RowCanonical` built from the existing subtype/equivalence images (sorted list bytes, proof-free and exact), with `encode`, `decode`, `digest`, the JSON printer and the spec `Document` all derived, `Kind` and the typed `Ref α`, the node `version ∷ kind ∷ spec ∷ payload` with the meta-schema as the zero-spec genesis, the heterogeneous store with admission and roots, words with closure, the layered read, the outbox and `verify`, and traits as `annotation` nodes that never enter identity; instances are generated by `tools/Effect4Gen` into `Store/Derived/*`, `Store/Domain/Derived/Program.lean`, `Store/Domain/PinDerived.lean` |
| `git:f7d22703:src/Effect4/Arch` | JSON-number facts and structural acceptance of Schema documents; the views are archived on `archive/char-stdlib` |
| `src/OCaml5` | the Lean half of the OCaml estate: the OCaml 5 handler machine (`Runtime/Effect`, the model the Eio and Picos carriers build on) and backend-relative values (`Runtime/Value`), the OCaml language model (`Ml`), library carriers (`Lib`), the `Eff` closed world and emitters (`Eff`), the LCNF → OCaml backend (`Lcnf`), the `--run` drivers (`Tools`) |
| `tools/ProofGraph` | shared tooling evidence: exact theorem references, speculative tactic search, checked proof publication; planned goals (`Goal`: `proof_goal`, a theorem whose body is `sorry`, and each theorem's standing, decisions row 203), sketches (`Sketch`, `proof_sketch`) and the plan (`Plan`: edges read from proof terms, derived statuses, `#plan_status`); the one population filter (`Population`); the proof-style ratchet (`ProofStyle`); no Effect4 or Aesop dependency; both Laws and Conform consume it |
| `tools/Conform` | generic source descriptions, exact conformance reports, proof bindings through `ProofGraph`, layouts, model builders, specification generation and compiler inspection; `Conform.Effect4` owns project profiles and target fixtures; `git:c67ff096:scripts/check-conform.sh` owns fresh execution receipts |
| `tools/Tools` | the Effect4-side `--run` drivers (lake library `Tools`): `TsGen`, the TypeScript estate's generated files (schemas, JSON writers, the profile) from the source description in `Tools.ProgramStructure` through the target projection `OCaml5.Eff.World`; `ProgramStructure` owns the selected ground family/parameter/mutual inventory; `Conform.Source.Description` reads and validates the generic shape, and is shared by Program deriving validation and the wire/engine structural views; `Corpus`, the printed corpus with `Api.roundTrip` beside each program; a sibling root of `Effect4`, outside the gate; its thin drivers are not library dependencies, and its small helper modules are imported only by tooling |
| `ocaml/` | the OCaml estate as one dune workspace: the LCNF route's generated machine (`gen/`), the host engine under it (`engine/`), and the `Eff` IR as an OCaml library (`eff/`) (`ocaml/README.md`) |
| `ts/eff` | the `Eff` IR as a TypeScript library (bun): `read.ts`, the one hand-written function (oxc's tree into the printer's fragment, then `Codegen/Read.lean` ported clause for clause, one reader per head); `eff.gen.ts`, `json.gen.ts`, `profile.gen.ts`, the Schema nodes, their JSON and the profile (heads, and each native operation with its `Row`, as nodes) generated by `Tools.TsGen` from the same closed world as `ocaml/eff`; checks `make check-gen` (drift) and `make check-ts-reader` (against `Api.roundTrip` over the corpus `Tools.Corpus` writes) in `make check` |
| `harness/schema-host` | locked rc.112 / TypeScript / effect-tsgo test installation for the Schema gates |
| `harness/truth` | the Lean-vs-rc.112 exit differential over the program corpus (bun) |

`src/Effect4/Laws.lean` imports the proof graph. Its files keep the namespaces of
the definitions they extend. `src/Effect4.lean` imports the application face and
functional utilities without reaching Laws. The audit checks both closures against
every library source; `make check-roots` elaborates `Test/All.lean` freshly so a new
unimported source cannot hide behind a cached build.

**Runtime content holds no proof tooling; imports are not the gate (DI-18, re-ruled 2026-10-01).**
General deriving and reflection live in tool roots (`tools/Tools`, `tools/Effect4Gen`,
`tools/Conform`, `tools/ProofGraph`). Command elaborators and tactic instruments of the law graph
live in `Laws/Auto` and beside the proofs they serve; their implementation modules have explicit
trust-gate admissions, every generated theorem is checked in its consuming module at the ordinary
axiom ceiling, and a module that imports Lean's elaboration APIs is audited like any other. What
the rule protects is the representation: no `Expr`, `Syntax`, metavariable or elaborator closure
is stored program content or a runtime value (`AGENTS.md`'s representation rules,
`docs/DESIGN-BASIS.md` DB-08, the separation gates at the foot of the machine modules). The
runtime root's one metaprogram, `Program/FoldOf.lean`, and a measured check in place of the former
import ban are open under the Codex metaprogramming audit
(`docs/research/2026-10-01-metaprogramming-audit/brief-codex-metaprogramming.md`, A7). The
typed-state skeleton and frame rules are declarations generated during elaboration, so no printed
source or TSV is read back. `docs/GENERATED.md` owns their build/check entry points.

`Effect4.Laws.Program.Typing` owns declarative typing judgments, generated specifications,
checker-agreement proofs and the input-indexed checking API. Its legacy
`Conform.Effect4.Typing` declaration names remain; module ownership keeps them in the
library audit. Aesop and `Std.Tactic.Do` stay in Laws. `ProofGraph` is below both Laws and
Conform: extracting the shared evidence checker does not introduce a Laws-to-Conform
import or alter the runtime/LCNF root. The six owed encoders (DI-41) remain with
`tools/Effect4Gen`; `deriving Canonical` is still a pilot for later families.

`Program/CheckedTyping.lean` owns the computed `TypedProgram` evidence for the
existing whole-program checker. Execution admission extends it; code generation
reuses it without runner registration limits. `Codegen/Checked.lean` owns module
production receipts indexed by program, row table and export name. The application
module exposes those receipts through `emitModule`, while `printModule` projects
syntax. Checker/declarative connections and production/reconstruction theorems live
in `Laws/Program/CheckedTyping.lean` and `Laws/Codegen/Checked.lean`. These are proof
views of the same program and printer, not a second language or source validator.

`Codegen/Bindings.lean` owns import origins, aliases, value/type availability and
nearest-name resolution. `Codegen/SourceBindings.lean` traverses the original target
syntax and records each use with its lexical scope. `Api.checkSourceBindings` returns
evidence indexed by that unchanged module and the caller's permitted import origins.
The corresponding Laws modules connect the computed check to the independent
`Bindings.Resolves` relation. This conservative profile masks local declarations at
block entry, exposes their capabilities after the initializer, and refuses forward
references, opaque declarations and unsafe verbatim name spellings. It is a component
of source admission; binder-annotation agreement and expected package-head origins still
need validation before raw reconstruction can become typed source admission.

`Codegen/Names.lean` owns what a legal target binding name is, for both the lexical
source check and the printer's export-name check. `Codegen/Admit.lean` is the reading
half of the module boundary: `admitModule` composes the lexical check, the raw
reconstruction, the shared `TypedProgram` certificate and a declaration-envelope
comparison against `Program.declarationType` — the printer's own annotation rule — and
keeps all four as `ModuleReading`, indexed by the exact module read. `Laws/Codegen/Admit.lean`
holds the envelope reflection theorem, uniqueness, and the composition with the producer.

`Program/Fragment.lean` owns executable membership in the existing straight
fragment. Both ordinary application admission and `Laws/Program/Denote.lean`
use that same definition. `admitStraightProgram` adds its membership proof to
the existing admission certificate; it does not certify a user specification
or provide whole-program type safety. Execution theorems stay in Laws.

Tests mirror these areas under `Test/`; durable attacks live under
`Test/Counterexamples/` with their stable IDs in
`Test/Counterexamples/REGISTER.md` and their contracts under `Test/contracts/`.

## The OCaml estate

One runtime: the *visible machine*, the Lean `RunMachine` running in OCaml as Lean's
compiler IR translated to typed OCaml (`ocaml/gen`, and `ocaml/engine` under it), so every
fiber, frame and park token is a field of one value that can be inspected, serialised and
messaged through the model's own decision alphabet. `ocaml/eff` is `Eff` as an OCaml
language whose bytes the Lean decoder accepts exactly. The other routes that once stood
beside it, the avatar (the same machine as OCaml 5 effect handlers) with the daemon
`effect4d` that served it, and route 1 (compiled Lean held as an opaque value behind
`Bridge.lean` and `git:5b3eb56b:ocaml/link`), are archived (see "What is not here"). Everything under
`ocaml/` is held to `ocaml/STANDARDS.md`.

## The seam

`Effect4.Api` exposes the operations of
the program pipeline. Callers cross this seam; batteries also test modules
at their own boundaries. Program printers answer syntax (`TypeScript.Expr`, `ConstDecl`). The explicit
`render` operation crosses to bytes through `Codegen.Artefact.render`; it and
text-producing functions such as `Codegen.Schema.documentSource` are admitted by
exact name in the axiom gate.

Inside the seam the library keeps its faces distinct and relates them by
theorem: structural syntax (`Eff`) for construction and printing; the frame
alphabet for what rc.112 evaluates; the machine's relational meaning over
explicit decision tapes, with `replayEval` as its fuel-bounded simulator; and
the executable witnesses and host receipts as bounded evidence. No bounded
runner is promoted into the meaning merely because it executes.

The scheduler records accept code, saved-state and frame-event parameters.
`FiberCore` and `FiberEvaluator` are interpretation parameters, with the original
frame machine as the default instance. This shares the command loop without
changing `Eff` as canonical program content. The reference term evaluator and the
Book/BMeans replay connection now live in `Laws/Program/InterpR.lean` and `RuntimeR.lean`.
Their proof-side continuations may contain functions; compiled frames remain data.
The decision tape carries Completion data at every instance. Replay agreement is not
a public resumption guarantee: the command-level `driveState` retains residue, but the
current session projection does not retain the whole suspended driver. The alternatives
are specified by the semantic owner, `docs/core/machine-state.md` §5.

## The faces, and the two ingest contracts

`Program.Ty` provides Effect-facing aliases over its existing constructors: `result`,
`exit`, `fiber`, `cause`, `array` and `readonlyArray`. Nullability helpers compose unions
with opaque `null` and `undefined` handles; duration, date-time and chunk helpers also
use the existing external-handle admission. `take` composes a list with an exit; the
stream binding checks the nonempty-batch requirement. `Api.Val.resultFailure` and
`resultSuccess` expose the existing sum encoding as match patterns. These helpers add
no stored constructors, key ordinals or codec cases. Signed integer values and flat
tuples of arity greater than two remain outside this addition.
`Machine.Value` owns the shared `exitOk`, `exitNil` and Result patterns; the machine
and context value namespaces export them. Wrappers that adapt typed keys or causes
remain beside their owning alphabet.
Shared pattern payloads use the foundational value type, so nested typed handles
are qualified, for example `.exitOk (Val.cell ⟨k⟩)`.

`Effect4.Api.HostSession` extends the program API with checked incremental replay over the
existing machine. Its program/table admission certificate, recorded-call association,
keyed pending replies and application ledger have separate roles. `Api.HostProtocol` owns
the finite transition and record-shape datum projected into the TypeScript prelude and the
v2 tape schema. Receiving a reply only stores it; `applyReply` selects its fiber/token key.
`reply_commute` proves that valid receipts for different keys commute as whole sessions;
it does not commute the effects of resumed programs. `Program.Stream` builds the generic
scoped open/pull/close kernel using existing Eff constructors and external rows. JSON decoding and
actual host resource ownership remain in the selected binding; `Program.HostBoundary` names
the relation being modeled. The session API does not add another stored program language.

`Eff` has several faces — the Lean printer and reader, the TypeScript reader over the printed
image, the two foreign ingest engines, the truth harness, the OCaml conformance face — and each
pair is held by a different kind of evidence; the packet that states them one by one is
`Test/contracts/faces.contract.md` (DI-50), in the format of `Test/contracts/README.md`.

The **two ingest contracts are different contracts, not one implementation with options**
(DI-37, ruled 2026-09-08, written here 2026-09-09), and they differ on three axes:

1. *The admitted language.* The printed image is the sub-language the Lean printer emits; the
   strict-foreign contract admits wild rc.112 source, including spellings the printer never
   produces.
2. *The refusal discipline.* The printed-image reader may treat what it meets as well formed and
   refuse by name where rc.112's surface genuinely loses information; the foreign engines must
   classify every input into a closed, injectively coded taxonomy — a `true` passed into a
   number-shaped service key is refused there, and the printed image never contains one.
3. *The service-key numbering.* The printed image carries each key's own recorded numbers (the
   printer mints `k<name>_<service>` from the key's data and invents nothing), while the foreign
   contract *assigns* ordinals per unit in first-use order from 4, with 0–3 reserved. One source
   unit can therefore have two different key tables, one per contract.

The implemented cross-contract test establishes **conditional fidelity** on the shared admitted
fragment: two foreign-reader lifts match the printed oracle up to key renumbering. It does not
establish that every printed program is foreign-admitted. The readers must first return one
valid verdict each and agree; agreed refusals remain visible, while asymmetric, missing,
malformed or conflicting verdicts fail. An independent positive control prevents two readers
that refuse everything from passing (`ts/eff/ingest/check-corpus.ts`, DI-37, Wave 2 amendment).

## The codegen route and the `Api` export

The experimental Surface emitter route was retired and the `Api` codegen export was **cut**
(DI-27, ruled 2026-09-09, executed 2026-09-10). The `Api` module exports `Target`, `Artefact`,
and the single crossing `render`.

## What is not here

The Surface library (`git:70b1571e:src/Effect4/Surface`, coupled codegen/ingest modules under
`src/Effect4/Codegen` and `src/Effect4/Ingest`, the frozen breaker batteries and
counterexamples under `git:70b1571e:Test/Surface` and `git:70b1571e:Test/Counterexamples/Surface`) is preserved
at `70b1571` on the local branch `archive/surface`.

The Char and StdLib modules, architecture and surface views, observability surface,
layer printer, export-census projections and foldlab vendor evidence are preserved at
`62c04d9` on the local branch `archive/char-stdlib`. Their live consumers were checked
before removal; the Store remains.

The Flow route — the Effects-flow language and runner, the region and frame
simulations, the TypeScript flow lowering, the store families and their trace
harness — is at `606918e` in main's history and on the pushed branch
`archive/flow-route`.

The avatar (`git:14e68353:ocaml/avatar`, the Machine as hand-written OCaml 5 effect handlers with its
descriptions, derived twins and projection guard under `git:ae9b4932:src/OCaml5/Avatar`), the daemon
`effect4d` (`git:14e68353:ocaml/server`) that served it, its wasm host (`git:14e68353:ocaml/wasm`), the fuzz corpus
and tapes rendered against it, and the two gates that held it (`avatar-witnesses`,
`armmap-citations`) are preserved at `14e6835` on the local branch `archive/ocaml5-avatar`.
The ruling that retired it is the engine brief's: one OCaml engine, `ocaml/gen`. The host
over the engine that replaces the daemon is owed by the host-rows slice.

The OCaml 5 reification the avatar was built against, the handler machine's invariants and
witnesses, the js_of_ocaml machine and the native ≈ jsoo relation, jsoo's block IR, the
Term → Code compiler, the CPS pass and its proofs, the Promise host, the `Term` renderer and
the term fuzz (`src/OCaml5/{Runtime,Jsoo,Compile,Ir,Fuzz}`, less `Runtime/Effect` and
`Runtime/Value`, which stay as the model the `Lib` carriers and the `Ml` profile cite), route
1's OCaml half (`git:5b3eb56b:ocaml/link`) and the spike probes (`git:5b3eb56b:ocaml/probes`) are at the same `14e6835`
on `archive/ocaml5-avatar`. Their findings are in the research notes they cite. Route 1's
Lean bridge was removed during the Conform integration and remains available at that
archived revision; truth fixtures cite the immutable historical source.
`Codegen/Print.lean` and `Codegen/Read.lean` retain the `Effect4.Program`
namespace: they operate on `Eff`, while rendered syntax lives with its target.
Shared demo carriers stay beside the library guards that use them; module-local
examples are private. The axiom gate keeps its ownership lookup independent
of the battery support module it audits.

Placement ownership: `Store/Carrier` holds values below Machine; `Store/Domain` holds canonical store operations above Schema, including the program instances and wire face. Fold connectors and their six typing projection agreements belong to Laws. `Codegen/Authoring/Forms` holds the target-profile authoring adapters while retaining their declaration names. `tools/Drivers` sits above OCaml5; `tools/TestSupport` shares the existing CAS and host-row fixtures between tools and tests, and has no runtime importer.
