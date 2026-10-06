# PUB faces and engine integration review

No new actionable mismatch appears in the reviewed merge. The faces and engine additions match the assigned scope and retain their evidence boundaries.

## Frozen scope

The seat commits are `0338b004` and `f9f24092`. The reviewed merge is `41be5ef3`; main `601ed7c5` retains identical bytes in all six changed files.

The monitor reads source, retained output, and fixture data only. It runs no Lean, compiler, engine, build, generator, or repository gate.

The prior truth-repair review remains separate. This packet covers the later faces and engine additions.

## Printing and reading

`Test.Program.QueueFaces` serves `read_print` and `read_exact`, under R8. Its new controls cover construction and the four Queue operations.

Five whole programs print and read back to their admitted program. Ten individual nodes also round-trip: five operations each at natural-number and string message types.

These node checks use the caller’s stated binder level. A take printed without its required handle level fails the control.

`readsAs` rejects take-as-offer and poll-as-size. Existing scenario controls still distinguish separate programs.

The rendered operation text is pinned. Long step rows are replaced only by text computed from the actual printed step at its exact binder level.

The remaining pin therefore checks the surrounding mask, Deferred allocation, loop, posting, withdrawal, and reply structure. Counts retain the unabridged take and offer components.

The round-trip checks read TypeScript syntax values. Rendered text pins are separate; these guards alone do not test an external parser or target typing.

The separate truth lane supplies tsgo and rc.112 results for five whole Queue programs. The faces module names that boundary.

This is finite evidence. It adds no universal operation-typing theorem, arbitrary-scope proof, or whole-run agreement theorem.

## Engine observations

The brief asks the existing R1/R4 lane to add a waiting taker, an interrupted taker, and the masked caller. All three additions are present.

`Test.Program.QueueEngine.runs` and `ocaml/engine/test/queue/write.lean` list `r1`, `r4`, `r2`, `r5`, and `masked` in that order.

The Lean battery binds each fixture’s program bytes, fuel, and final answer to the program admitted by `Api.Author.build`.

The writer refuses an unbuilt, unfinished, or unprintable result. The reader consumes canonical program bytes on both OCaml carriers.

| Comparison | Actual observation | Scope |
| --- | --- | --- |
| Lean against Fast and Ref | Each root’s final answer, with successful completion at fuel 20,000 | Five programs; the engine’s own drive loop |
| Fast against Ref | Outcome, exits, fiber rows, trace rows, and store row | The same five runs |

Full Fast-versus-Ref report equality does not establish full Lean-versus-engine trace or store equality. The module and test explicitly state that distinction.

Placement remains a finite control for `queue-expansion-agrees`, concept `translation-simulation`, R10. The tests establish no general scheduler, delivery, or liveness claim.

Each program has byte-truncation refusal and insufficient-fuel controls. Different expected answers reject substitution of the neighbouring run’s answer.

The first two fixtures are byte-for-byte unchanged as complete records. The three new answers are `7`, `[5,0]`, and `[1,9,true,0,0]`.

## Retained acceptance

The seat’s narrow logs report 350 jobs for QueueFaces and 170 jobs for QueueEngine, both successful.

The seat and coordinator engine logs each contain 1,754 PASS lines and no FAIL lines. Each reports `test_queue: 47 checks, 0 failures`.

The monitor recounts those saved lines and matches every run’s byte count and fuel to the committed fixture. This is data inspection, not engine execution.

The coordinator’s gate summary records zero exits for build, fixture generation, corpus preparation, dune build, dune test, documentation checks, and Test.All.

Its build records 990 jobs, 740 modules, and 87,690 declarations. The semantic/test axiom ceiling remains `[propext, Quot.sound]`.

It retains 24 planned goals and 11 declarations depending on goals. No additional proof completion follows from these finite controls.

## Remaining work

No final `docs/research/2026-10-06-seat-PUB-receipt.md` exists at the frozen merge. The seat’s further typing, documents, and final accounting remain unfinished.

The fixture binding holds when its Lean battery is elaborated. Its existing generator and freshness boundaries remain explicit; this review introduces no new gate.

No advisory is needed from this review. The final PUB receipt still needs to preserve these observation limits and report the remaining obligations.
