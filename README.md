# Effect4

An Effect program, as data you can hold.

If you write Effect TS, you already know the shape of a program: `Effect.gen`, a few
`flatMap`s, a `scoped` block with an `acquireRelease` inside it, a `catchCause` around the
whole thing. What you do not have is that program as a value. It is a closure tree the
runtime walks once. You cannot diff it, hash it, type it outside `tsc`, or ask what the
fiber runtime will do with it before you run it.

Effect4 is that value. It is a first-order syntax for Effect programs, written in Lean 4,
with a type checker, a printer that emits real Effect TS, a reader that takes real Effect
TS back, a compiler down to the runtime's own frame primitives, and a fiber machine that
runs those frames the way `effect@4.0.0-rc.112`'s run loop does. Every piece is data. Every
piece has canonical bytes and a content address.

## The same program, four ways

Here is one program. First as you would write it:

```ts
Effect.flatMap(Ref.make(0), (a0) =>
  Effect.flatMap(
    Effect.scoped(Effect.acquireRelease(Effect.succeed(7), (a1, a2) => Ref.set(a0, a1))),
    (a1) => Ref.get(a0)))
```

Make a ref, acquire the number seven inside a scope, and when the scope closes write the
acquired value into the ref. Then read the ref. The answer is seven.

Second, as the Lean value the printer produced that text from:

```lean
def pAcquire : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (.scoped (.acquireRelease (.succeed (.lit (.nat 7)))
        (.perform .refSet (.app "pair" (.cons (.var 0) (.cons (.var 1) .nil))))))
      (.perform .refGet (.var 0)))
```

Variables are positions. `.var 0` is the ref, `.var 1` is the acquired seven, because a
release in Effect is typed over the acquired value and the exit. There are no closures in
this tree and no Lean functions. It is an inductive with derived equality, so two programs
are the same program when Lean says they are.

Third, what the compiler turns it into. Effect's run loop does not interpret `flatMap`. It
interprets a small alphabet of primitives: `Success`, `Failure`, `Sync`, `Suspend`,
`WithFiber`, `OnSuccess`, `OnFailure`, `OnSuccessAndFailure`, `OnExit`, `Iterator`,
`WhileLoop`, `Async`, and a few more. Effect4 has that alphabet as an inductive called
`Prim`, transcribed from `internal/effect.ts` with the line numbers kept beside each arm.
`compile` takes the program above to an `OnSuccess` frame whose body is a `Sync` on the
ref store and whose continuation names the rest of the program by its address in the tree.
Nothing is inlined. The frame the runtime would push is the frame the compiler emits.

Fourth, what running it means. The machine holds fibers, a scope store, refs, deferreds,
a timer, a layer memo map, and a per-fiber dispatcher. It does not decide anything on its
own. Every point where rc.112 would consult the world is a decision on a tape: evaluate
this fiber, flush the event loop, advance the clock, here is the host's answer to that
async call. Replaying a tape against a program is a pure function. Same program, same tape,
same machine, every time.

## Why this exists

Because the fiber runtime is the part of Effect nobody can see. Interruption, masks,
finalizer order when a scope closes with a failure and a parallel strategy, which losers a
race interrupts and when, what a deferred interrupt does under `uninterruptible`. These are
the behaviours that make Effect worth using and the ones you cannot check by reading your
own code. Effect4 writes them down as a machine you can step, in a language where the
machine is also a theorem prover.

That gets you three things.

**A program is a document.** It types outside TypeScript. `Effect<A, E, R>` is computed
structurally: the answer, the error union, and the requirement row of service keys. It
prints to Effect TS and reads back from Effect TS, and the round trip is exact on the
fragment the printer emits. It has canonical bytes, so it has an address, so it can be
pinned, cited, stored, and served.

**The runtime is a specification you can run.** The machine is written from the pinned
source, arm by arm, with the citation on each arm. When rc.112 changes, the citations
tell you what moved. When you want to know what a `raceAll` does to its losers, you read
one function instead of the run loop, the fiber, the scheduler and the scope.

**The two are checked against each other.** A truth harness prints a corpus of programs,
runs each on the real rc.112 under bun, and compares the exit and the schedule with what
the Lean machine produced from the same tape. Programs that talk to a host, a sqlite
client or a key-value store, run against the real package with the host's answers recorded
on the tape, so the Lean replay reproduces the run without the host.

## The pieces

**`Eff`** is the program syntax. Twenty-seven constructors, one per Effect export or
runtime primitive the tree handles. Each carries the name it prints as and the frame it
compiles to:

| constructor | prints as | compiles to |
| --- | --- | --- |
| `bind` | `Effect.flatMap` | `Prim.onSuccess` |
| `gen` | `Effect.gen(function* () { … })` | `Prim.iterator` |
| `catchCause` | `Effect.catchCause` | `Prim.onFailure` |
| `onExit` | `Effect.onExit` | `Prim.onExit` |
| `scoped` | `Effect.scoped` | the region frames |
| `acquireRelease` | `Effect.acquireRelease` | `uninterruptible` plus `onExit` over the scope |
| `withFiber` | `Effect.withFiber` and the `Fiber.*` calls | `Prim.withFiber` |
| `provideLayer` | `Effect.provide` | a scoped layer build and a context region |
| `perform` | the row's export: `Ref.get`, `Deferred.await`, `Effect.sleep`, `sql.unsafe(…)` | sync, async, or a nested body, by the row |

Two sequencing forms on purpose: `bind` is a `flatMap` frame, `gen` is one `Iterator`
primitive. They print differently and run differently, and that difference is what the
harness compares.

**Rows** are the operations a program may perform. The standard library rows are `Ref`,
`Deferred`, `Scope`, `Clock`. A package is a row table: the sqlite client and the in-memory
key-value store are tables of rows answered by the host, each with its request type, answer
type, error type and the rc.112 lines it transcribes. Adding a package is writing its table.

**Typing** computes `Effect<A, E, R>` for a program. The error column is a canonical union.
The requirement column is a set of service keys that `provide` and `provideService`
discharge. A program that does not type does not compile.

**The machine** is the rc.112 fiber runtime as a state transition system: fibers with
their frame stacks and masks, the scope store with sequential and parallel close, the
deferred store with its waiters, the ref heap, a logical clock, the layer memo map, the
context. `RunDecision` is the tape alphabet. A run is a fold over decisions.

**The faces.** The printer emits Effect TS. The reader admits Effect TS, including the
sugar people actually write (`andThen`, `tap`, `ensuring`, `matchCause`, `forkScoped`), and
lifts it to `Eff`. A second reader in TypeScript, generated from the same Lean data, runs
in the ingest tooling.

**The store.** Every value the machine holds is one carrier, `Val`, with a fixed tag
alphabet and a fixed framing. Programs, types, rows, tapes and results all encode to it
through derived `Canonical` instances, so a program's bytes are a function of the program
and decode back to exactly it. Addresses are digests of those bytes.

**The OCaml engine.** The Lean compiler's own intermediate representation of the machine,
translated to OCaml and built with dune, so the same run loop exists as native code.

## Where things are

| path | what |
| --- | --- |
| `src/Effect4/Api.lean` | the application face: `typeOf`, `print`, `read`, `compile`, `run`, `replay` |
| `src/Effect4/Program/` | `Eff`, `Ty`, typing, the compiler, the rows, the packages |
| `src/Effect4/Machine/` | the fiber machine, stores, causes, scheduler, timer |
| `src/Effect4/Codegen/` | the printer, the reader, the sugar forms |
| `src/Effect4/Store/` | `Val`, the framing, `Canonical`, the content store |
| `src/Effect4/Laws/` | the proof graph, its own build root |
| `harness/truth/` | the corpus, the tapes, the differential against rc.112 |
| `ts/eff/` | the TypeScript reader and the generated reflections |
| `ocaml/` | the OCaml engine and the wire goldens |
| `vendor/effect-4.0.0-rc.112/src` | the pinned source every citation points into |

`docs/ARCHITECTURE.md` owns the dependency direction. `docs/DESIGN-MAP.md` says what is
claimed and how strongly, layer by layer, and is the right second page.

## Building

The toolchain is pinned in `lean-toolchain`; dependencies are pinned by commit in
`lakefile.toml`.

```bash
lake build Effect4
```

builds the library. `lake build Effect4Laws` builds the proof graph, and a bare
`lake build` builds both plus the test battery, whose root audits every declaration's
axioms. The truth harness needs bun and the pinned Effect packages:

```bash
bun install --frozen-lockfile --cwd ts/eff
scripts/check-truth.sh
```

`scripts/sweep.sh --hermetic` runs every gate that needs nothing but Lean. The OCaml
lane needs the `effect4` opam switch; see `ocaml/README.md`.

## What it is not

It is not a runtime you deploy. Your program runs on Effect. Effect4 is the model you check
it against, the form you store and address it in, and the specification of what the
runtime does with it. rc.112 is the reference and the pin, never the owner of the
semantics; when the pin moves, the citations show what to re-read.

Two earlier subsystems live on branches: `archive/flow-route`, a control-flow-graph front
end, and `archive/surface`, an HTTP and MCP surface library. Both are one checkout away.
