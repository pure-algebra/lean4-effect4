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
| `Effect4/Data` | requirement rows, JSON, lawful optics |
| `Effect4/Semantics` | `Cause` and `Exit`, the error channel everywhere |
| `Effect4/Concurrency` | `FiberId`; the fork, observer, scope and race vocabulary the machine speaks |
| `Effect4/Context` | `ServiceKey`, its universe and transport |
| `Effect4/Runtime` | the rc.112 frame alphabet and single-fiber step, the `Scope` state machine, and the frame-level facts that pin them (`LiveStack`, `ScopeRestoration`) |
| `Effect4/Deep` | the reference fiber machine (`RunMachine`, `drive`, `replayEval`, `runSyncExit`), the stores, the Context and Layer models, the clause theorems and the witnesses |
| `Effect4/Syntax` | `Eff`, `typeOf`, `print`, the native operation alphabet, `compile` and `interpOf` |
| `Effect4/Api` | the one application-facing module |
| `Effect4/Schema` | the persisted Schema data plane |
| `Effect4/Target/TypeScript` | the pinned Effect v4 profile; the Schema and annotated-field generators |
| `Effect4/Store`, `Effect4/Arch`, `Effect4/StdLib` | content store; architecture views; the rc.112 export census and its links to the model |
| `Effect4/Surface`, `Effect4/Char` | surface carriers and their emitters; characterized components |

Tests mirror these areas under `Effect4Test/`; durable attacks live under
`Effect4Test/Counterexamples/` with their stable IDs in
`test/counterexamples/REGISTER.md` and their contracts under `test/contracts/`.

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
