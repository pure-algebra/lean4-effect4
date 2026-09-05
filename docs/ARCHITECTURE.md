# Effect4 architecture

## Dependency direction

```text
effects (external: signatures, programs, laws)      typescript (external: syntax, rendering)
        |                                                    |
Data (Row, Json, Optic)   Semantics (Cause, Exit)   Concurrency (FiberId, vocabulary)   Context (ServiceKey)
        |                        |                          |                              |
Runtime: the frame alphabet (Prim, PrimInterp, FrameFiber) and the Scope state machine
        |
Deep: the fiber machine over the frames; its stores; Context and Layer models; clauses; witnesses
        |
Syntax: Eff (the program IR), typing, printer, native alphabet, compile to frames
        |
Api: the application face (type, print, compile, run; Schema syntax)

Schema (carrier, annotations, checker, authoring) -> Target/TypeScript (profile, Schema generation)
Store (canonical bytes, digest, trie) -> Arch (views as Schema documents), StdLib (rc.112 export census)
                                      -> Surface (entities, HTTP API, MCP agent, deployment, site), Char

OCaml5 (lake library, src/OCaml5): the OCaml 5 / js_of_ocaml runtime model, the OCaml
language model, library carriers, the LCNF backend, the Machine descriptions; imports
Effect4.Machine and Effect4.Api, nothing imports it   ->   ocaml/ (the dune workspace)

Tools (lake library, src/Tools): the Effect4-side --run drivers; imports Effect4.Api,
Test.Program.Gen and TypeScript.Render, nothing imports it
```

Arrows point from what is imported to what imports it. `Api` imports the
Syntax and Schema faces and nothing imports `Api`; `Deep` never imports
`Syntax`; `Schema` never imports `Deep`. The two external packages are pinned
by exact commit in `lakefile.toml` (`effects`, `typescript`, and `hash` for the
store's SHA-256). Effect4 depends on them, never conversely, and re-declares
none of their carriers.

## Source tree

| Area | Responsibility |
| --- | --- |
| `src/Effect4/Data` | requirement rows, JSON, lawful optics |
| `src/Effect4/Machine` (`Cause.lean`, `Exit.lean`) | `Cause` and `Exit`, the error channel everywhere |
| `src/Effect4/Machine` (`Fiber.lean`, `Supervision.lean`) | `FiberId`; the fork, observer, scope and race vocabulary the machine speaks |
| `src/Effect4/Machine` (`Key.lean`) | `ServiceKey`, its universe and transport |
| `src/Effect4/Machine` (`Frames.lean`, `Scope*.lean`, `LiveStack.lean`) | the rc.112 frame alphabet and single-fiber step, the `Scope` state machine, and the frame-level facts that pin them (`LiveStack`, `ScopeRestoration`) |
| `src/Effect4/Machine` (`Fibers.lean`, `Stores.lean`, `Context.lean`, `Layer.lean`, `Clauses.lean`, `Witnesses.lean`) | the reference fiber machine (`RunMachine`, `drive`, `replayEval`, `runSyncExit`), the stores, the Context and Layer models, the clause theorems and the witnesses |
| `src/Effect4/Program` | `Eff`, `typeOf`, the native operation alphabet, `compile` and `interpOf`; `Provision` — the requirement algebra (`Row.diff`), the layer signature `LayerTy` and its laws, the layer term `LayerTerm` with `Eff` bodies, `App` (`Effect.provide`), the build specification and its totality theorem, and the lowering into the Layer machine (`docs/research/2026-09-04-provision-algebra.md`); `Config` — rc.112's `ConfigProvider` as a fallback monoid under a path-transformation action, the `Config` reader with its tri-state resolution, dotenv substitution with fuel, and the configuration requirement row (`docs/research/2026-09-04-production-standards-spike.md`) |
| `src/Effect4/Api` | the one application-facing module |
| `src/Effect4/Schema` | the persisted Schema data plane |
| `src/Effect4/Codegen`, `src/Effect4/Ingest` | the pinned Effect v4 profile, `print`, the Schema and annotated-field generators and the surface emitters; the readers that go the other way |
| `src/Effect4/Store`, `src/Effect4/Evidence` | content store; architecture and surface views; the rc.112 export census (`Evidence/StdLib`) and its links to the model |
| `src/Effect4/Surface`, `src/Effect4/Evidence/Char` | surface carriers; characterized components; `Surface/Middleware` and `Surface/Provision` are the joins of the surface carriers to the provision algebra (an HTTP middleware as a requirement transformer, a deployment as a closed layer) and are the one place `Surface` imports `Program` |
| `src/OCaml5` | the Lean half of the OCaml estate: the OCaml 5 handler machine and its theorems, the jsoo machine, the OCaml language model (`Ml`), library carriers (`Lib`), the LCNF → OCaml backend (`Lcnf`), the Machine carriers described and rendered (`Render`, `Derived`), the route-1 bridge (`Bridge`), the `--run` drivers (`Tools`) |
| `src/Tools` | the Effect4-side `--run` drivers (lake library `Tools`): `TsGen`, the TypeScript estate's generated files (schemas, JSON writers, the profile) from the closed world `OCaml5.Eff.World` reads off the environment; `Corpus`, the printed corpus with `Api.roundTrip` beside each program; a sibling root of `Effect4`, outside the gate, imported by nothing |
| `ocaml/` | the OCaml estate as one dune workspace: the avatar (the Machine as OCaml 5 handlers), the daemon `effect4d`, the route-1 link and host core, the LCNF route's generated machine, and the `Eff` IR as an OCaml library (`ocaml/README.md`) |
| `ts/eff` | the `Eff` IR as a TypeScript library (bun): `read.ts`, the one hand-written function (oxc's tree into the printer's fragment, then `Codegen/Read.lean` ported clause for clause, one reader per head); `eff.gen.ts`, `json.gen.ts`, `profile.gen.ts`, the Schema nodes, their JSON and the profile (heads, and each native operation with its `Row`, as nodes) generated by `Tools.TsGen` from the same closed world as `ocaml/eff`; gates `check-ts-eff.sh` (drift) and `check-ts-eff-corpus.sh` (against `Api.roundTrip` over the corpus `Tools.Corpus` writes) in the sweep |
| `harness/truth` | the Lean-vs-rc.112 exit differential over the program corpus (bun) |

Tests mirror these areas under `Test/`; durable attacks live under
`Test/Counterexamples/` with their stable IDs in
`Test/Counterexamples/REGISTER.md` and their contracts under `Test/contracts/`.

## The OCaml estate

Two runtimes exist on purpose. The *visible machine* is the Lean `RunMachine` running in
OCaml — compiled Lean held as an opaque value (`ocaml/link`), or Lean's compiler IR
translated to typed OCaml (`ocaml/gen`) — so every fiber, frame and park token is a field
of one value that can be inspected, serialised and messaged through the model's own
decision alphabet. The *avatar* (`ocaml/avatar`) is the same machine as OCaml 5 effect
handlers with the frame stack on the OCaml stack: fast, effects-native, never one-for-one,
and held to the Lean model by the witness report, the corpus differential against rc.112,
and the projection guard between its hand descriptions and the descriptions derived from
the environment. The daemon (`ocaml/server`) serves the avatar on three hosts from one
module list; `ocaml/eff` is `Eff` as an OCaml language whose bytes the Lean decoder accepts
exactly. Everything under `ocaml/` is held to `ocaml/STANDARDS.md`.

## The seam

`Effect4.Api` is a deep module: a small interface (a dozen definitions) over
the whole pipeline. Callers and batteries cross it the same way. It answers
syntax (`TypeScript.Expr`, `ConstDecl`) and never text, so it stays at the
library's axiom ceiling; rendering to bytes is the pinned package's one call,
outside the seam, and the few text-producing generators (`Target.TypeScript.
Schema.generate?` and its kin) are admitted by exact name in the gate.

Inside the seam the library keeps its faces distinct and relates them by
theorem: structural syntax (`Eff`) for construction and printing; the frame
alphabet for what rc.112 evaluates; the machine's relational meaning over
explicit decision tapes, with `replayEval` as its fuel-bounded simulator; and
the executable witnesses and host receipts as bounded evidence. No bounded
runner is promoted into the meaning merely because it executes.

## What is not here

The Flow route — the Effects-flow language and runner, the region and frame
simulations, the TypeScript flow lowering, the store families and their trace
harness — lives on branch `archive/flow-route`
(`docs/research/2026-09-04-prod-cleanup-inventory.md`, D1). The single-fiber
loop inside `Runtime/Runtime.lean` and its batteries are the next candidates
for the same move (D4).
