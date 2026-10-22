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
  there, so the recipe does not change. The lowered closure names the moved declarations, so
  `make gen-lcnf` re-cuts `ocaml/engine/test/lanes/lanes_gen.ml`.
- `scripts/check-program-object.py` names `Test.Dogfood.Scenario.Todo.application`. It is the
  build-hygiene seat's file; the receipt names the one-line repair.
- The certificate's text names a key's Lean declaration. The battery's pinned line moves from
  `Test.Dogfood.Scenario.Todo.todoRepoKey` to `Examples.Todo.todoRepoKey`.
