# Effect4 architecture

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
Program and Schema faces; callers and selected batteries import `Api`; `Machine` never imports
`Program`; `Schema` never imports `Machine`. The external packages are pinned
by exact commit in `lakefile.toml` (`effects`, `typescript`, and `hash` for the
store's SHA-256). Effect4 depends on them, never conversely, and re-declares
none of their carriers.

## Source tree

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
| `src/Effect4/Laws/Program` | value typing and progress, denotations, agreement and simulation; the term scheduler and its evaluator, replay and observations, with general frame/term simulation still owed |
| `src/Effect4/Schema` | the persisted Schema data plane |
| `src/Effect4/Codegen`, `src/Effect4/Ingest` | the pinned Effect v4 profile, `print`, the Schema and annotated-field generators, target/artefact definitions, and the Ingest taxonomy |
| `src/Effect4/Store` | the content-addressed store as one trait (`docs/research/2026-09-04-cas-trait-plan.md` (untracked working note)): `Val` the value tree and its one exact byte codec, `Canonical α` (shape, `toVal`, `ofVal`, three laws), including `RowCanonical` built from the existing subtype/equivalence images (sorted list bytes, proof-free and exact), with `encode`, `decode`, `digest`, the JSON printer and the spec `Document` all derived, `Kind` and the typed `Ref α`, the node `version ∷ kind ∷ spec ∷ payload` with the meta-schema as the zero-spec genesis, the heterogeneous store with admission and roots, words with closure, the layered read, the outbox and `verify`, and traits as `annotation` nodes that never enter identity; instances are generated by `tools/Effect4Gen` into `Store/Derived/*`, `Program/Derived.lean`, `Store/PinDerived.lean` |
| `src/Effect4/Arch` | JSON-number facts and structural acceptance of Schema documents; the views are archived on `archive/char-stdlib` |
| `src/OCaml5` | the Lean half of the OCaml estate: the OCaml 5 handler machine (`Runtime/Effect`, the model the Eio and Picos carriers build on) and backend-relative values (`Runtime/Value`), the OCaml language model (`Ml`), library carriers (`Lib`), the `Eff` closed world and emitters (`Eff`), the LCNF → OCaml backend (`Lcnf`), the `--run` drivers (`Tools`) |
| `tools/Conform` | generic source descriptions, exact conformance reports, checked proof bindings, layouts, model builders, specification generation and compiler inspection; `Conform.Effect4` owns project profiles and target fixtures; `scripts/check-conform.sh` owns fresh execution receipts |
| `tools/Tools` | the Effect4-side `--run` drivers (lake library `Tools`): `TsGen`, the TypeScript estate's generated files (schemas, JSON writers, the profile) from the source description in `Tools.ProgramStructure` through the target projection `OCaml5.Eff.World`; `ProgramStructure` owns the selected ground family/parameter/mutual inventory; `Conform.Source.Description` reads and validates the generic shape, and is shared by Program deriving validation and the wire/engine structural views; `Corpus`, the printed corpus with `Api.roundTrip` beside each program; a sibling root of `Effect4`, outside the gate; its thin drivers are not library dependencies, and its small helper modules are imported only by tooling |
| `ocaml/` | the OCaml estate as one dune workspace: the LCNF route's generated machine (`gen/`), the host engine under it (`engine/`), and the `Eff` IR as an OCaml library (`eff/`) (`ocaml/README.md`) |
| `ts/eff` | the `Eff` IR as a TypeScript library (bun): `read.ts`, the one hand-written function (oxc's tree into the printer's fragment, then `Codegen/Read.lean` ported clause for clause, one reader per head); `eff.gen.ts`, `json.gen.ts`, `profile.gen.ts`, the Schema nodes, their JSON and the profile (heads, and each native operation with its `Row`, as nodes) generated by `Tools.TsGen` from the same closed world as `ocaml/eff`; gates `check-ts-eff.sh` (drift) and `check-ts-eff-corpus.sh` (against `Api.roundTrip` over the corpus `Tools.Corpus` writes) in the sweep |
| `harness/schema-host` | locked rc.112 / TypeScript / effect-tsgo test installation for the Schema gates |
| `harness/truth` | the Lean-vs-rc.112 exit differential over the program corpus (bun) |
| `harness/streams` | mined rc.112 stream dependency examples and explicit Pull/foundation boundary tests; exact host observations, with type-only and unasserted examples distinguished; the Lean stream connection remains open |

`src/Effect4/Laws.lean` imports the proof graph. Its files keep the namespaces of
the definitions they extend. `src/Effect4.lean` imports the application face and
functional utilities without reaching Laws. The audit checks both closures against
every library source; `scripts/check-library-roots.sh` runs it freshly so a new
unimported source cannot hide behind a cached build.

**Project reflection and generators stay outside the audited roots** (DI-18, ruled
2026-09-09). Runtime code imports no Lean tooling. The bounded `Std.Tactic.Do` proof
workflow lives in Laws, whose resulting declarations receive the ordinary axiom audit. Deriving and
reflection live in a **tool root** — `tools/Tools`, `tools/Effect4Gen` and `tools/Conform`, sibling roots outside
the gate — and emit ordinary `.lean` declarations that the kernel then checks like any other
source. The output is what the audit reads. `Effect4.Laws.Program.Typing` owns the
declarative typing judgments, ordinary generated specifications, checker-agreement proofs
and input-indexed checking API. Its legacy `Conform.Effect4.Typing` declaration names are
retained; source-module ownership keeps them in the library axiom audit. `Std.Tactic.Do`
is used in Laws only; runtime code does not import the proof tools. The six owed encoders (DI-41) go through
`tools/Effect4Gen`, and the `deriving Canonical` handler stays a pilot for later families.

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
`Bridge.lean` and `ocaml/link`), are archived (see "What is not here"). Everything under
`ocaml/` is held to `ocaml/STANDARDS.md`.

## The seam

`Effect4.Api` exposes the operations of
the program pipeline. Callers cross this seam; batteries also test modules
at their own boundaries. Program printers answer syntax (`TypeScript.Expr`, `ConstDecl`). The explicit
`render` operation crosses to bytes through `Codegen.Artefact.render`; it and
text-producing generators such as `Codegen.Schema.generate?` are admitted by
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
changing `Eff` as canonical program content. An algebra-carrier integration
fixture exercises the same loop; the later term evaluator and simulation remain
outside this slice. The decision tape carries Completion data at every instance.

## The faces, and the two ingest contracts

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

The Surface library (`src/Effect4/Surface`, coupled codegen/ingest modules under
`src/Effect4/Codegen` and `src/Effect4/Ingest`, the frozen breaker batteries and
counterexamples under `Test/Surface` and `Test/Counterexamples/Surface`) is preserved
at `70b1571` on the local branch `archive/surface`.

The Char and StdLib modules, architecture and surface views, observability surface,
layer printer, export-census projections and foldlab vendor evidence are preserved at
`62c04d9` on the local branch `archive/char-stdlib`. Their live consumers were checked
before removal; the Store remains.

The Flow route — the Effects-flow language and runner, the region and frame
simulations, the TypeScript flow lowering, the store families and their trace
harness — is at `606918e` in main's history and on the pushed branch
`archive/flow-route`.

The avatar (`ocaml/avatar`, the Machine as hand-written OCaml 5 effect handlers with its
descriptions, derived twins and projection guard under `src/OCaml5/Avatar`), the daemon
`effect4d` (`ocaml/server`) that served it, its wasm host (`ocaml/wasm`), the fuzz corpus
and tapes rendered against it, and the two gates that held it (`avatar-witnesses`,
`armmap-citations`) are preserved at `14e6835` on the local branch `archive/ocaml5-avatar`.
The ruling that retired it is the engine brief's: one OCaml engine, `ocaml/gen`. The host
over the engine that replaces the daemon is owed by the host-rows slice.

The OCaml 5 reification the avatar was built against, the handler machine's invariants and
witnesses, the js_of_ocaml machine and the native ≈ jsoo relation, jsoo's block IR, the
Term → Code compiler, the CPS pass and its proofs, the Promise host, the `Term` renderer and
the term fuzz (`src/OCaml5/{Runtime,Jsoo,Compile,Ir,Fuzz}`, less `Runtime/Effect` and
`Runtime/Value`, which stay as the model the `Lib` carriers and the `Ml` profile cite), route
1's OCaml half (`ocaml/link`) and the spike probes (`ocaml/probes`) are at the same `14e6835`
on `archive/ocaml5-avatar`. Their findings are in the research notes they cite. Route 1's
Lean bridge was removed during the Conform integration and remains available at that
archived revision; truth fixtures cite the immutable historical source.
`Codegen/Print.lean` and `Codegen/Read.lean` retain the `Effect4.Program`
namespace: they operate on `Eff`, while rendered syntax lives with its target.
Shared demo carriers stay beside the library guards that use them; module-local
examples are private. The axiom gate keeps its ownership lookup independent
of the battery support module it audits.
