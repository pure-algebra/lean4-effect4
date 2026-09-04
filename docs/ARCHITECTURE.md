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
| `src/Effect4/Program` | `Eff`, `typeOf`, the native operation alphabet, `compile` and `interpOf` |
| `src/Effect4/Api` | the one application-facing module |
| `src/Effect4/Schema` | the persisted Schema data plane |
| `src/Effect4/Codegen`, `src/Effect4/Ingest` | the pinned Effect v4 profile, `print`, the Schema and annotated-field generators and the surface emitters; the readers that go the other way |
| `src/Effect4/Store`, `src/Effect4/Evidence` | content store; architecture and surface views; the rc.112 export census (`Evidence/StdLib`) and its links to the model |
| `src/Effect4/Surface`, `src/Effect4/Evidence/Char` | surface carriers; characterized components |

Tests mirror these areas under `Test/`; durable attacks live under
`Test/Counterexamples/` with their stable IDs in
`Test/Counterexamples/REGISTER.md` and their contracts under `Test/contracts/`.

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
