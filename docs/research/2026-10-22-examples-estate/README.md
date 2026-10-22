# The examples estate

The owner, 2026-10-22, by voice: the examples leave the tests, and the run code goes. This note
holds the census, then the receipt. The base is `007c7cd17`.

## 1. The files under `Test/Dogfood`

A program is what an author writes: data, rows, services, definitions and entries. A battery
pins a build, a printed TypeScript module or a run. A scenario drives the machine through a script.

| File | Lines | Kind | Where it goes |
| --- | ---: | --- | --- |
| `Scenario/Todo/Data.lean` | 183 | program, with the reference model | the data, rows, programs, protocols and application go to `Examples.Todo`; the cache wrappers go to `Examples.CachedTodo`; the model `repository` stays |
| `Scenario/Todo/CachedProgram.lean` | 43 | program and consumer | `cached` goes to `Examples.CachedTodo`; the consumer builder stays |
| `Scenario/Todo.lean` | 232 | battery | stays, reads `Examples.Todo` |
| `Scenario/Todo/{Entries,Cached,Runs,Scenario,Typed}.lean` | 615 | battery | stay |
| `Scenario/Todo/{Host,HostRun,HostLane}.lean` | 286 | battery: the OCaml lane's host run | stay; the LCNF recipe names their roots |
| `P1HttpCache`, `P2HandlerLayers`, `P3WorkerQueue`, `P4RateLimiter`, `P5LedgerService`, with their `Data` | 1934 | battery: rc.112 acceptance tests (decisions row 206) | stay: each holds program fragments and pins their refusals, not one program |
| `Stage.lean`, `StageData.lean` | 220 | battery support | stay |
| `Scenario.lean`, `Scenario/Data.lean`, `Scenario/TapeData.lean` | 711 | scenario driver | stay |
| `Scenario/{Atomic,QueueWorkers,Routing,Timeout,Workers}/**` | 2950 | scenario | stay |
| `Bank.lean` | 180 | battery: the bank's digests | stays |
| `ApplicationDefs.lean` | 95 | battery | stays |
| `EditSession.lean` | 75 | battery | stays |

The five P programs stay batteries. Each subject they name gets an authored example in its place.
The worker queue becomes the bounded buffer, and the rate limiter runs over the Semaphore. The
ledger becomes the bank account, and the HTTP cache becomes the key-value store with a cache.

## 2. The run code and what reaches it

| Declaration or file | Lines | Reached by | Fate |
| --- | ---: | --- | --- |
| `tools/Compiler/Run.lean` | 258 | `Compiler.Main` | deleted |
| `Compiler.Main`: `runHosted`, `runCommand`, `Source.hosted?`, the `run` usage, the docstring's `run` lines | about 70 | `Compiler.Groups`, the batteries | deleted |
| `Compiler.Source.application`'s `hosted` and `script` arguments, `Compiler.main`'s | 4 | `Compiler.Groups` | deleted |
| `Compiler.Groups.todoHosted`, `todoScript` | 14 | `Test/Codegen/CompilerEmit.lean` | deleted |
| `Test/Codegen/CompilerEmit.lean`, the run section | 120 | the battery | deleted |
| `Test/Codegen/CompilerReport.lean`, the hollow run step | 6 | the battery | rewritten over `check` |
| `tools/Tools/RunChecks.lean` | 293 | `Test/Dogfood/Scenario/Todo/Host.lean`, by import only | deleted; `Host.lean` imports `Tools.RunRecord` |
| `tools/Tools/RunRecord.lean` | 34 | `HostRun.lean`, `HostLane.lean`, `Compiler.Groups` | stays: the OCaml lane's host run reads it |
| `tools/Tools/WireText.lean` | 43 | `tools/Drivers/Live.lean`, `tools/Drivers/View.lean`, two batteries | stays: the run does not reach it |

The Lean machine (`Run.runWith`, the reactors under `src/Effect4/Run`) stays.

## 3. The batteries that read the groups

- `Test/Codegen/CompilerEmit.lean` reads `Compiler.Groups.all`, the `todo` group's host and
  script, and `Groups.todoLowered`.
- `Test/Audit/ClosureAudit.lean` imports `Compiler.Groups`.
- `Test/Codegen/CompilerReport.lean` and `Test/Codegen/CompilerGraphs.lean` read the to-do through
  `Compiler.check`.
- `scripts/generate.py`'s `graphs` family runs `inspect --group todo`.

No battery pins `generated/graphs`. The `graphs` group stays as it is, because the Makefile's
`GEN_GROUPS` and `HERMETIC_GROUPS` name it and this seat only appends to the Makefile.

## 4. What else the move reaches

- The LCNF recipe `ocaml/gen/roots.json` names roots in `Test.Dogfood.Scenario.Todo`. They stay
  there, so the recipe does not change. `make gen-lcnf` after the move changes no lowered file:
  the lowered closure holds no declaration that moved.
- `scripts/check-program-object.py` names `Test.Dogfood.Scenario.Todo.application`. It is the
  build-hygiene seat's file; the receipt names the one-line repair.
- The certificate's text names a key's Lean declaration. The battery's pinned line moves from
  `Test.Dogfood.Scenario.Todo.todoRepoKey` to `Examples.Todo.todoRepoKey`.

## 5. Receipt

**The one thing to know.** The library's glob `Examples.+` leaves the root module `Examples`
unbuilt, so nothing can import it. The list therefore stands in `Examples.All`, beside the root.
The proposal is `globs = ["Examples", "Examples.+"]` in `lakefile.toml`, the coordinator's file.

Base `007c7cd17`. Head: the commit that adds this section.

### The commits

| Commit | What |
| --- | --- |
| `604eb96bc` | the census, sections 1 to 4 |
| `6fbb50b87` | the run code goes: 39 lines added, 798 removed |
| `9a4f0641d` | the to-do leaves the tests: `Examples.Todo`, `Examples.CachedTodo`, the groups from `Examples.all` |
| `b6857a5a5` | `Examples.BoundedBuffer` |
| `e502b7359` | `Examples.BankAccount` |
| `01b30955f` | `Examples.KeyValueStore` |
| `6a7efa418` | `Examples.RateLimiter` |
| `064fed931` | `Examples.VendingMachine` |
| `dc3777e9f` | `generated/examples`, the `examples` family, `make gen-examples` |

Outside `generated/` and this note, 37 files change: 764 lines added, 969 removed. Under
`generated/`, 59 files change: the seven example folders and the index are new, and
`generated/graphs/todo.gen.{md,json}` change two lines each.

### The examples

| Example | Module | Lines | Form | Library blocks |
| --- | --- | ---: | --- | --- |
| `todo` | `Examples.Todo` | 108 | four host rows, two protocols, four entries | none |
| `cachedTodo` | `Examples.CachedTodo` | 42 | the to-do with the Ref cache imposed | `Ref.Cache` |
| `boundedBuffer` | `Examples.BoundedBuffer` | 54 | one entry; two producers and two consumers forked | `Queue` |
| `bankAccount` | `Examples.BankAccount` | 84 | two host rows, one protocol, four entries | none |
| `keyValueStore` | `Examples.KeyValueStore` | 87 | four host rows, four entries, the cache imposed | `Ref.Cache` |
| `rateLimiter` | `Examples.RateLimiter` | 62 | one host row; three requests forked through two permits | `Semaphore` |
| `vendingMachine` | `Examples.VendingMachine` | 76 | three event rows, two protocols, one loop | none |

Each example builds (`lake build Examples.<Name>`), checks (`lake exe effect4 check --group
<name>`) and prints (`emit --target ts`). The pinned tsgo, 7.0.0-dev.20260629.1, checks each
printed folder with no diagnostic. That check ran over a scratch tsconfig with `ts/prelude`'s
packages, because no `check-ts` lane takes an emitted folder. Finite probes on the Lean machine,
in a scratch file and not committed:

- `transfer(3)` answers 306;
- `transfer(1, 2, 30)` over balances 100 and 5 leaves 70 and 35; a short balance and a
  same-account transfer write nothing;
- `quotes` with the clock moved 10 ms answers two quotes and one none, after two host calls;
- `sell(tea, 30)` over coins 25 and 10 vends tea and returns 5.

### The run code removed

`tools/Compiler/Run.lean` (258 lines) and `tools/Tools/RunChecks.lean` (293 lines) are deleted.
`Compiler.Main` loses `runHosted`, `runCommand`, `Source.hosted?`, the `run` usage and the
`hosted` and `script` arguments of `Source.application` and `main`. `Compiler.Groups` loses
`todoHosted` and `todoScript`. `Test/Codegen/CompilerEmit.lean` loses its run section (120
lines). `lake exe effect4 run --group todo` is a usage error, exit 2. `Tools.RunRecord` stays: the
OCaml lane's host run reads it. The Lean machine and the batteries that run the to-do on it stay.

### The groups

`Compiler.Groups.all` is the wire corpus, the SQLite programs, then each example of
`Examples.all` under its application's name. A battery reads the corpus and the SQLite group, so
both stay. The to-do alone keeps native roots, `Compiler.Groups.todoLowered`: they are its host
lane's, under `Test`. `generated/graphs` stays as it is, because the Makefile's `GEN_GROUPS` and
`HERMETIC_GROUPS` name it and this seat appends only. `generated/examples/todo` holds the same
relations document without the session reading, so `graphs` can retire into it.

### The commands and their results

- `lake build Examples Compiler.Exe effect4` and each touched battery: built.
- `make batteries-touched BASE=007c7cd17`: 20 batteries, built.
- `python3 scripts/wire-roots.py --check`: PASS.
- `python3 scripts/generate.py --only examples`, then `--only graphs`, each in place and then with
  `--output-dir` (check mode): PASS, fresh bytes equal to the committed files.
- `make check-ts`: PASS on its six lanes (tsgo, target with 104 of 104 resolved, ts-reader,
  tsdiag, ingest-smoke, service identity).
- `make gen-lcnf`: PASS, and no lowered file changes. `make check-ocaml`: PASS
  (`gen-check: PASS`, `PASS ocaml`); its `Error:` lines are the red controls' expected compile
  failures.
- The to-do's printed module, surface and certificate are byte-identical to the emission of
  2026-10-21 (`.lake/effect4/todo/ts/` in the main checkout). Only the header's command line
  differs.
- `python3 scripts/check-language.py --strict` on this note, `generated/examples/index.md`, every
  `generated/examples/*/*.gen.md` and `generated/graphs/todo.gen.md`: PASS.

### The axiom output

- `#axiom_audit` over the eight `Examples` modules: 137 declarations within
  `[propext, Quot.sound]`, no planned goal.
- `#axiom_audit` over `Test.Dogfood.Scenario.Todo.Data`, `.CachedProgram`, `.Host`,
  `Test.Codegen.CompilerEmit` and `Test.Codegen.CompilerReport`: 101 declarations within
  `[propext, Quot.sound]`.
- `#axiom_audit` over `Compiler.Groups`, `Compiler.Main`, `Compiler.Graphs` and
  `Tools.RunRecord`: 35 of 691 reach `Classical.choice`. Each one is in `Compiler.Main`'s command
  line and IO, through the toolchain's string search and `ST.Ref`. Tool modules stand outside
  the axiom gate. `Groups`, `Graphs` and `RunRecord` reach none.

### What the examples met: the authoring gaps

1. A failure record whose fields are declared out of alphabetical order prints, and its module
   reads back to another program. `bankAccount` declares `available` before `needed`. The
   repair is in `src/`: `eff_failure` normalizes as `eff_record` does, or the reader orders the
   fields.
2. The printer refuses a method named by a TypeScript reserved word (`delete`), and its refusal
   names the service alone, not the method. The commit `01b30955f` also says that an entry named
   `get`, an atom's name, is refused. A later probe shows that `get`, `add` and `take` print, so
   that sentence is wrong. The entry keeps the name `lookup`.
3. `Application.Imposed` takes a banked block, an `Eff` value. The Semaphore and the Queue have
   service definitions (`serviceDefs`) and no block, so neither can be imposed on a service.
   `rateLimiter` makes its semaphore inside its entry, so the limit holds within one request.
4. An application holds no authored state across requests: its state is the context and the
   imposed blocks' cells. The bank keeps its balances at the host, and a transfer is two row
   calls, not one atomic step.
5. The Ref cache caches one list, loaded by the entry it wraps. `keyValueStore`'s `lookup` cannot
   read through it, and the two wrappers, read-through and invalidate-after, are written again in
   each application that imposes the cache.
6. `Run.runWith` does not move the test clock. A probe of `rateLimiter` plays a clock row first.

### The open obligations

- `lakefile.toml`: `globs = ["Examples", "Examples.+"]`, then `Compiler.Groups` may import
  `Examples` and the list may move into `examples/Examples.lean`.
- `scripts/check-program-object.py` line 23 names `Test.Dogfood.Scenario.Todo.application`; it
  reads `Examples.Todo.application` now. It is the build-hygiene seat's file.
- `docs/ARCHITECTURE.md`'s `tools/Compiler` row names `run` and `Compiler.Run`.
- `tools/Tools/ArchitectureRoles.lean` describes `Compiler.Groups` with "its host and script", and
  `Test/Dogfood` alone as the user roots; `examples/` is a new estate.
- The Makefile's `GEN_GROUPS`, `HERMETIC_GROUPS`, `GRAPH_OUT` and `help` lines: add `examples`,
  and retire `graphs` into `generated/examples/todo` if the session reading may go.
- The lakefile's `Compiler` comment names `run`.

The evidence is bounded where it is finite. The probes are finite runs on the Lean machine, and
the tsgo check of the new folders is a host check that no lane repeats.

### The proposed decisions row 449

The examples estate, the run code removed, the groups (the owner, 2026-10-22, by voice).

1. The examples leave the tests. An example is one application, a module `Examples.<Name>`
   under `examples/`, listed once in `Examples.all` (`examples/Examples/All.lean`). Nothing under
   `examples/` imports `Test`. A battery that reads an example imports it.
2. The run code goes: the `run` command, `Compiler.Run`, the host and the script of a source, and
   `Tools.RunChecks`. The Lean machine stays, and a run on it is a battery's finite evaluation.
3. The groups of `lake exe effect4` are the corpus, the SQLite programs, then each example under
   its application's name.
4. Each example's folder `generated/examples/<name>/` holds the printed module and surface, the
   certificate, the relations in md and json, the boundary figures and the handlers.
   `make gen-examples` writes it; `generated/examples/index.md` lists the examples. The manifest
   and any run stay out.
5. The five rc.112 programs P1 to P5 stay batteries (row 206). The examples hold their subjects
   as authored programs: the bounded buffer, the bank account, the key-value store and the rate
   limiter. The vending machine is the state machine.
6. Open: the six gaps above and the obligations above.
