# 2026-10-13 seat SVC receipt: the application emitted as one Effect service (E1, E2, E4)

**The one thing to know before merging:** `make check-host-protocol` now runs slice E4. It writes
the to-do's service file, checks it and its consumer with tsgo 7, and performs the 13 to-do
scripts on it under rc.112. Lean replays each run, and the gate fails when a service run is
decided otherwise than its script's own run. The keyed lane's driver
(`harness/truth/session/Keyed.lean`) gains `replayedOf` and the subcommand `service-checks`.

Status: receipt (history, not authority). Brief: the coordinator's dispatch of 2026-10-13, slices
E1 and E2 of `docs/research/2026-10-13-emitted-services/README.md` under row 378 (19) and (20).
The coordinator's later messages added the key spelling's move, four merges of main, the join
of the rows' services and slice E4. A last message put E4 in the host-protocol gate. The sections
on E1 and E2 below record the state before seat ROWS landed. The section on E4 at the end records
the state after it.

## Base and head

Branch `seat/svc`, worktree `/Users/pooks/Dev/lean4-effect4-svc`, base `c2620b4ac`. The head is
the commit of this receipt, after `d317f5cd3`.

| Commit | What |
| --- | --- |
| `b002e17c5` | the context type prints; the key spelling moves to `Types.lean` (merged to main as `9be016a0a`) |
| `09e8637a2` | merge of `refactor/phase1-phase3` at `6f32c88cd`: the coordinator's one key reader |
| `088de151b` | merge of `refactor/phase1-phase3` at `516f13bf8`: `serviceKeyDecl`, the corpus rows |
| `39c876adf` | E1, E2, the battery, the laws and this check's evidence (merged to main as `45761a86a`) |
| `1e553c712` | the receipt for E1 and E2 |
| `56dc69365` | merge of `refactor/phase1-phase3` at `c4f56a879`: E3, the rows as Effect services |
| `da44d1e88` | the join: the file declares the rows' services; the battery follows the rows' key |
| `693b65a79` | E4: the consumer, the runner, the service file's writer and the Lean checks (merged to main as `60f10bc4c`) |
| `b811faeb7` | merge of `refactor/phase1-phase3` at `60f10bc4c` |
| `d317f5cd3` | the gate: `check-host-protocol` runs E4 and fails on a disagreement |

## Changed files

| File | Change |
| --- | --- |
| `src/Effect4/Codegen/Types.lean` | `keyText`, `keyIdentifier` and `requirementType` arrive unchanged; `ofTy` prints `Ty.contextOf`; `ofTy_contextOf` |
| `src/Effect4/Codegen/PrintLeaf.lean` | the three moved definitions leave, and nothing else changes |
| `src/Effect4/Codegen/Classes.lean` | `readTy` reads `Context.Context<R>`; the coordinator's `6f32c88cd` then reads its row through `readRequirement` |
| `Test/Codegen/TypeReader.lean` | five context types that read back, and three red controls |
| `src/Effect4/Program/Authoring/ApplicationService.lean` | new (E1): `Application.serviceDefs`, `serviceModule`, `contextDef`, `methodDef`, `entryTy`, `ServiceRefusal` |
| `src/Effect4/Codegen/Checked.lean` | E2: `moduleImports`, `freeNames`, `preludeNames`, `fromEffect`, `bytesLe`, `fileOf`, `ModuleEmission.file`, `ModuleEmission.file_decls` |
| `tools/Tools/Code/Module.lean` | its imports are the core's (`moduleImports` at `preludePath`); its own copies of the four helpers are gone |
| `src/Effect4/Laws/Program/ApplicationService.lean` | new: `methodDef_decl`, `serviceDefs_mem`, `serviceDefs_error`, `serviceDefs_of_refused` and two `mapM` steps |
| `Test/Dogfood/Scenario/TodoService.lean` | new battery: the to-do's block and file, the read-back's reach, two refusals |
| `src/Effect4.lean`, `src/Effect4/Laws.lean`, `Test/All.lean` | one appended import each |
| `docs/research/2026-10-13-seat-svc/` | the tsgo check's driver (`EmitTodo.lean`), consumer, red controls, configurations and outputs |

## The emitted module, for the to-do

`EmitTodo.lean` writes it from `Application.serviceModule "TodoApp"`, `Api.Author.build`,
`Api.emitModule "main"` and `ModuleEmission.file "../prelude/prelude.ts"`, laid out by
`Tools.Code.moduleText` at Effect's width. It is
`docs/research/2026-10-13-seat-svc/todo.gen.ts`, byte for byte:

```ts
/**
 * todo: the to-do application as one Effect service, written by the Effect4 code
 * generator (decisions row 378 (20)). Do not edit.
 */
import { Context, Data, Effect, Layer } from "effect"
import { eq, fst, ifCase, optionCase, pair, snd } from "../prelude/prelude.ts"

export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}

export const TodoAppContext = (a0: void): Effect.Effect<Context.Context<never>, never, never> => Effect.suspend(
  () => Effect.context<never>()
)

export const TodoApp_add = (a0: readonly [Context.Context<never>, string]): Effect.Effect<{ readonly done: boolean; readonly id: number; readonly title: string }, readonly ["SqlError", string] | readonly ["EmptyTitle", "a title is required"], never> => Effect.suspend(
  () => Effect.provideContext(
    Effect.flatMap(
      Effect.succeed(snd(a0)),
      (a1) => ifCase(
        () => eq(a1, ""),
        () => Effect.fail(pair("EmptyTitle", "a title is required")),
        () => TodoRepo.insert(a1)
      )
    ),
    fst(a0)
  )
)

export const TodoApp_list = (a0: Context.Context<never>): Effect.Effect<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never> => Effect.suspend(
  () => Effect.provideContext(TodoRepo.all(), a0)
)

export const TodoApp_complete = (a0: readonly [Context.Context<never>, number]): Effect.Effect<{ readonly done: boolean; readonly id: number; readonly title: string }, readonly ["SqlError", string] | NotFound, never> => Effect.suspend(
  () => Effect.provideContext(
    Effect.flatMap(
      Effect.succeed(snd(a0)),
      (a1) => Effect.flatMap(
        TodoRepo.setDone(pair(a1, true)),
        (a2) => optionCase(a2, () => Effect.fail(new NotFound({ id: a1 })), (a3) => Effect.succeed(a3))
      )
    ),
    fst(a0)
  )
)

export const TodoApp_remove = (a0: readonly [Context.Context<never>, number]): Effect.Effect<void, readonly ["SqlError", string] | NotFound, never> => Effect.suspend(
  () => Effect.provideContext(
    Effect.flatMap(
      Effect.succeed(snd(a0)),
      (a1) => Effect.flatMap(
        TodoRepo.delete(a1),
        (a2) => ifCase(() => a2, () => Effect.succeed(undefined), () => Effect.fail(new NotFound({ id: a1 })))
      )
    ),
    fst(a0)
  )
)

export const TodoApp = Context.Service<"TodoApp", { readonly add: (a1: string) => Effect.Effect<{ readonly done: boolean; readonly id: number; readonly title: string }, readonly ["SqlError", string] | readonly ["EmptyTitle", "a title is required"], never>; readonly list: () => Effect.Effect<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never>; readonly complete: (a1: number) => Effect.Effect<{ readonly done: boolean; readonly id: number; readonly title: string }, readonly ["SqlError", string] | NotFound, never>; readonly remove: (a1: number) => Effect.Effect<void, readonly ["SqlError", string] | NotFound, never> }>(
  "TodoApp"
)

export const TodoAppLayer = Layer.effect(TodoApp, Effect.map(TodoAppContext(), (a0) => {
  return {
    add: (a1: string) => TodoApp_add(pair(a0, a1)),
    list: () => TodoApp_list(a0),
    complete: (a1: number) => TodoApp_complete(pair(a0, a1)),
    remove: (a1: number) => TodoApp_remove(pair(a0, a1))
  }
}))

export const main: Effect.Effect<void, never, never> = Effect.succeed(undefined)
```

Three readings of the text:

- Every declaration is exported already (`ConstDecl.exported` defaults to true, and the admission
  envelope requires it). The service key, its layer and the main are among them. E2 adds no
  export.
- `TodoRepo` is the one free name (`freeNames`, tested in the battery). It is the rows'
  namespace, which seat ROWS turns into a declared service key.
- `Entry.applied` binds each parameter by `Effect.flatMap(Effect.succeed(part), …)`. The printed
  method keeps that binding: correct, and one step longer than a direct read of the part.

## Commands and results

Each Lean command ran from the worktree inside `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`.
Each TypeScript command ran in the check folder named below.

1. A probe (`lake env lean`, a scratch file): a prototype of the to-do's service block built and
   typed. `Api.emitModule` refused it: `print (typeSpelling "Context.Context<never>")`, the open
   item of row 349. Commit `b002e17c5` repairs it.
2. `lake build Effect4.Codegen.Types Effect4.Codegen.Classes Effect4.Codegen.PrintLeaf`, then
   their 13 direct importers, then eight printing batteries and laws (`PrintContract`,
   `ReadContract`, `TemplatesContract`, `ServicesPrint`, `DefinitionsPrint`, `ModuleReadable`,
   `Laws.Codegen.Admit`, `Tools.Code.Module`): each "Build completed successfully".
3. After the merge of `6f32c88cd`: `lake build Test.Dogfood.Scenario.Todo
   Effect4.Program.Authoring.ApplicationService Effect4.Laws.Api.ModuleReadable Tools.Code.Module
   Test.Codegen.TypeReader ProofGraph.AxiomAudit`, then `lake build Effect4.Codegen.Checked
   Tools.Code.Module Effect4.Program.Authoring.ApplicationService`: "Build completed
   successfully (158 jobs)".
4. `lake build Test.Dogfood.Scenario.TodoService`: "Build completed successfully (1129 jobs)";
   every guard holds.
5. `lake build Effect4.Laws.Program.ApplicationService`: "Build completed successfully (243 jobs)".
6. After the merge of `516f13bf8`, the changed modules and their direct importers built: "Build
   completed successfully (1162 jobs)". The command:

   ```text
   lake build Effect4.Codegen.Checked Effect4.Api Effect4.Codegen.Admit Effect4.Emit
     Effect4.Laws.Codegen.Checked Tools.Code.Module Drivers.Emit Tools.View.Build Tools.View.Program
     Tools.View.Run Effect4.Program.Authoring.ApplicationService
     Effect4.Laws.Program.ApplicationService Test.Dogfood.Scenario.TodoService ProofGraph.AxiomAudit
   ```

   A build of the roots `Effect4` and `Effect4.Laws` started and was stopped unfinished, since it
   is no narrow build. Each root gains one appended import of a module that builds alone. The
   coordinator builds the roots at the merge.
7. `lake env lean -M4096 --run docs/research/2026-10-13-seat-svc/EmitTodo.lean $W`, with `$W` a
   fresh folder of the session's scratchpad: "EmitTodo: wrote the to-do's service module, its host
   declaration and the prelude".
8. The check folder `$W` holds the evidence folder's TypeScript files under `todo/` and its
   `tsconfig*.json` at the root. `$W/node_modules` is a link to
   `/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules`. Nothing was installed or downloaded.
9. `node …/ts/eff/node_modules/@typescript/native-preview/bin/tsgo --version`: "Version
   7.0.0-dev.20260629.1". The linked `effect` is "4.0.0-rc.112" (its `package.json`).
10. `node $TSGO --pretty false --noEmit -p tsconfig.json` (the module, the host declaration, the
    prelude, the consumer): exit 0, no diagnostic.
11. `node $TSGO --pretty false --noEmit -p tsconfig.red.json` (the three red consumers): exit 1,
    exactly three diagnostics, one for each red file:
    - `red-argument.ts(7,26)`: TS2345, a `number` where `add` takes a `string`;
    - `red-layer.ts(6,14)`: TS2375, `Layer<"TodoApp", never, never>` is no `Layer<"Other", …>`;
    - `red-requirement.ts(6,14)`: TS2375, the unprovided program still requires `"TodoApp"`.
12. `node $TSGO --pretty false --noEmit -p tsconfig.nohost.json` (the module without the host
    declaration): exit 1, four TS2304 "Cannot find name 'TodoRepo'" and two diagnostics that follow
    from them.
13. After the merge of `516f13bf8`, commands 7 to 12 ran again in a fresh folder. `cmp` finds both
    written files byte for byte the ones above, and tsgo answers as before.

Not run: `make` and every `check-*` gate, `lake build Test`, the whole-tree axiom gate, bun and
rc.112. The brief's builds are named modules only.

## Axiom output

- `#axiom_audit Effect4.Codegen.Types Effect4.Codegen.Classes Effect4.Codegen.PrintLeaf
  Test.Codegen.TypeReader` (before the merge): "694 declarations within [propext, Quot.sound], 0
  of them modulo planned goals; 0 planned goals".
- `#axiom_audit Effect4.Program.Authoring.ApplicationService
  Effect4.Laws.Program.ApplicationService Effect4.Codegen.Checked Test.Dogfood.Scenario.TodoService`
  (after the first merge): "184 declarations within [propext, Quot.sound], 0 of them modulo
  planned goals; 0 planned goals".
- The final audit ran after the merge of `516f13bf8`: "880 declarations within [propext,
  Quot.sound], 0 of them modulo planned goals; 0 planned goals". The command:

  ```text
  #axiom_audit Effect4.Codegen.Types Effect4.Codegen.Classes Effect4.Codegen.PrintLeaf
    Effect4.Codegen.Checked Effect4.Program.Authoring.ApplicationService
    Effect4.Laws.Program.ApplicationService Test.Codegen.TypeReader Test.Dogfood.Scenario.TodoService
  ```

## Evidence

| Claim | Evidence |
| --- | --- |
| A context type prints as `Context.Context<R>`, `R` in the requirement row's one spelling | proved: `Types.ofTy_contextOf` (`src/Effect4/Codegen/Types.lean`), by `rfl` |
| The checked type reader reads five context types back and refuses three spellings | tested: `Test/Codegen/TypeReader.lean` |
| The to-do's service block builds, and each method declares its entry's open type | tested: `Test/Dogfood/Scenario/TodoService.lean` |
| Each method of any built block declares its entry's checked type, less the rows' keys | proved: `Application.serviceDefs_mem`, `Application.methodDef_decl` |
| A block's refusal is an entry's, by its name; a refused entry refuses the block | proved: `Application.serviceDefs_error`, `Application.serviceDefs_of_refused` |
| The file imports four `effect` names and six prelude names; `TodoRepo` stays free | tested: the battery |
| The file's declarations are the envelope's, so the envelope's read-back law holds of it | proved: `ModuleEmission.file_decls`, by `rfl` |
| The to-do's module reads back | tested, and false: `Api.readModule` refuses it, and its block is outside `blockReadable` |
| A class-free application's module reads back, inside `blockReadable` | tested: the battery's `classFree` (the to-do's `add` and `list`) |
| tsgo 7 accepts the to-do's file, beside a host declaration of `TodoRepo`, and the consumer | tested, host-only: commands 10 to 12, finite, one compiler |
| The consumer's types are the ones an Effect user expects | tested, host-only: `provided` at `Effect<ReadonlyArray<Todo>, …, never>`, `layer` at `Layer<"TodoApp", never, never>` |

The tsgo evidence is bounded: one module, one consumer, three red controls and one host
declaration, under one compiler build. No run on rc.112 took place.

## Landed theorems and their placement

`Types.ofTy_contextOf` (`src/Effect4/Codegen/Types.lean`):

- Concept: `context-requirements`; property: `emission-requirements-complete`, a checked
  emission's declarations carry their complete types.
- Question: registry claim `emission-requirements-complete` (role compatibility). Consumer: the
  printed headers of the service's definitions (`printDef`), whose state is a context.
- Reach: the type projection `Types.ofTy`, at the native scope key; every key of the row.
- Does not establish: target typing; a signature with another scope key spells `Scope.Scope`
  otherwise in `requirementType sig.scopeKey`.
- Unlocks: R5 and R8, a module whose declarations hold a context (rows 349, 378 (20)).

`ModuleEmission.file_decls` (`src/Effect4/Codegen/Checked.lean`):

- Concept: `exact-codecs`; property: `module-defs-round-trip`.
- Question: registry claim `module-defs-round-trip` (role compatibility); consumer: the read-back
  of a file, through `ModuleEmission.readModule`.
- Reach: the declarations of the file envelope, at every prelude path.
- Does not establish: the bindings check of the imports (`admitModule`), or target typing.
- Unlocks: R8, one emission route for agents (row 373 (11)).

`Application.methodDef_decl`, `Application.serviceDefs_mem`
(`src/Effect4/Laws/Program/ApplicationService.lean`):

- Concept: `context-requirements`; property: a provided region discharges its context's keys
  (`provide-discharges`, at a definition's declaration).
- Question: proposed claim `application-service-methods` (role compatibility), below; consumer: an
  application's claims carried to its service's methods, and the battery's method columns.
- Reach: any application at the native table, any service name; the block that
  `serviceDefs` answers.
- Does not establish: that the block type-checks (the build's `Checker.checkModule` checks it);
  what a method means; anything of the printed text.
- Unlocks: R8 and R10, the application as one export (row 378 (20)).

`Application.serviceDefs_error`, `Application.serviceDefs_of_refused`, with the steps
`mapM_error_mem`, `mapM_ok_each` and `Application.entryTy_error`:

- Concept: `residual-program-typing`; property: a located refusal, complete against the entries'
  checks.
- Question: proposed claim `application-service-refusal` (role inversion), below; consumer: the
  emission entry of an application, which reports a refused block by its entry.
- Reach: any application at the native table; refusals of the scope reader and of the checker.
- Does not establish: which refused entry comes first beyond entry order; any typing of a body.
- Unlocks: R8.

## Reused declarations

- `DefSrc.serviceInit`, `DefSrc.serviceMethod`, `DefSrc.decl`, `requestTy`
  (`src/Effect4/Program/Authoring.lean`); `Application.openProgram`, `Application.Entry.applied`,
  `Application.declarations`, `Application.table` (`src/Effect4/Program/Authoring/Application.lean`).
- `withFiber`, `Action.context`, `provideContext` (`src/Effect4/Program/Authoring/Lifts.lean`);
  `Checker.check` (`src/Effect4/Program/Checker.lean`); `Requirement.ofList`, `Row.diff`.
- `printServices` and the module printer, unchanged (`src/Effect4/Codegen/Print.lean`).
- `SourceBindings.moduleUses`, `SourceBindings.useResolved`; the tool's former import logic, moved
  into the core and then reused by the tool.
- `bind_ok`, `mapM_ok_mem` (`src/Effect4/Laws/Program/Authoring.lean`).
- `ModuleEmission.readModule`, `blockReadable` (`src/Effect4/Laws/Api/ModuleReadable.lean`).
- The keyed lane's bindings type (`bindingsType`, `harness/truth/session/Keyed.lean`), rewritten
  as the check's host declaration; `tools/Drivers/Emit.lean`'s four prelude files.

## Open obligations

1. **The read-back at the to-do.** The definition header reader (`readDefHead`,
   `DefDecl.readable`, `src/Effect4/Codegen/Read.lean`) reads no payload class. A class-aware
   header reader puts the to-do's block inside `blockReadable`. The coordinator schedules it
   after ROWS lands.
2. **The rows' keys.** The coordinator joins ROWS's namespace declarations (`serviceKeyDecl`, and
   `TodoRepo` as `Object.assign(TodoRepoKey, …)`) to the file, exported as ROWS declares them.
   `moduleImports` reads the joined declarations: `Context` comes from `effect`, and `TodoRepo`
   is bound. `Object` is a standard global of the binding analysis
   (`src/Effect4/Codegen/SourceBindings.lean`), so it needs no import. The join is
   `fileOf prelude { e.module with decls := classes ++ rows ++ declarations }`. The reading
   boundary's `layersPlain` (`src/Effect4/Codegen/Admit.lean`) requires every declaration before
   the main to be exported, so a key const that is not exported is refused there. With a key in
   `R`, the initial program's requirement row is not empty, so `DefDecl.readable` refuses it; the
   header reader reads only `never` there.
3. **The prelude's place.** The file takes the prelude's path as an argument. V3's prelude
   package gives it one name.
4. **`check-corpus`** is reached by `b002e17c5` and not run here: the corpus programs typed at a
   context print a declaration now. The coordinator runs it on main (message of 2026-10-13).
5. **The meaning law** of the note (a method at arguments means its entry applied to them, under
   the layer's context) is not stated. Its placement is the note's.
6. **The tool's output for host rows changes.** `Tools.Code.importsOf` imported every free name
   that was not `effect`'s from the prelude. It now imports prelude names only and leaves a row's
   namespace free. The reading verdict of such a module stays `unbound`.
7. **An application's entry in `Api`.** The note's V2 row names one emission entry for an
   application in `src/Effect4/Api.lean`. This brief did not give that file, so `EmitTodo.lean`
   composes the steps itself. The main's name is the caller's: the check passes `main`.

## E4: the to-do's service on rc.112, after E3

Seat ROWS landed E3 at `c4f56a879`: the to-do's rows require `todoRepoKey`, so the namespace
`TodoRepo` is an Effect service. The coordinator asked for the join and for E4.

### What changed

- **The join** (`da44d1e88`). `ModuleEmission.file` (`src/Effect4/Codegen/Checked.lean`) holds the
  payload classes, the rows' services (`rowServiceDecls`) and then the declarations, with the
  imports over the whole. It answers `Except PrintRefusal`, and `fileOf` takes the names that are
  no import. `Tools.Code.Module` writes its modules through the file. `ModuleEmission.file_decls`
  goes, since the file's declarations are no longer the envelope's.
- **The battery** follows the rows' key: the state is `Context.Context<"k30_6">`, the layer
  requires the key, and no name stays free.
- **E4** (`693b65a79`), in the new folder `harness/truth/service/`:
  - `EmitTodo.lean` writes the service file into the keyed lane's work folder;
  - `consumer.ts` holds the typed consumer programs (`withTodo`, `programs`);
  - `run-todo.ts` performs the to-do's keyed scripts on those programs with the lane's recorder;
  - `tsconfig.json` and `red/` hold the compiler's check and its two red controls.
- **The keyed driver** (`harness/truth/session/Keyed.lean`) gains `replayedOf`, which `replayRun`
  now shares, and the subcommand `service-checks`.
- **The gate** (`d317f5cd3`). The coordinator asked that the existing host-protocol gate run E4,
  with no new target and no wrapper script:
  - The recipe builds what the script's four Lean files import (`build_imports`): the
    projection's writer, the keyed driver, the legacy adapter and `EmitTodo.lean`.
  - Before the compiler's run, `scripts/check-host-protocol.py` writes the service file with
    `EmitTodo.lean`. The compiler's project includes `harness/truth/service/*.ts`.
  - `refused` requires the two red files to fail with exactly their two diagnostics.
  - After the keyed lane's checks, it runs `run-todo.ts` on the scenarios' fixtures. Lean replays
    the recordings (`scenario-batch`) and decides the checks (`service-checks`).
  - `check_service` fails at the first disagreement, and its summary joins the PASS line.
  - `service_controls`, three red controls, require that a changed replay, run or pair fails
    `check_service`.
  - `service-checks` writes each decision twice: on the replayed run and on the script's own run
    (`scriptedSettled`, `scriptedConforming`, `scriptedAgrees`). The gate compares the two, so it
    pins no count.
  - The `Makefile` adds the folder's Lean, TypeScript, JSON and red files to the stamp's inputs
    (`HOST_PROTOCOL_SERVICE`).

### The joined module, for the to-do

The file's first part, written by `EmitTodo.lean` with the prelude at `../../../prelude.ts`:

```ts
import { Context, Data, Effect, Layer, type Option } from "effect"
import { eq, fst, ifCase, optionCase, pair, snd } from "../../../prelude.ts"

export class NotFound extends Data.TaggedError("NotFound")<{ readonly id: number }> {}

export const TodoRepoKey = Context.Service<"k30_6", { readonly insert: (a0: string) => Effect.Effect<{ readonly done: boolean; readonly id: number; readonly title: string }, readonly ["SqlError", string], never>; readonly all: () => Effect.Effect<ReadonlyArray<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never>; readonly setDone: (a0: readonly [number, boolean]) => Effect.Effect<Option.Option<{ readonly done: boolean; readonly id: number; readonly title: string }>, readonly ["SqlError", string], never>; readonly "delete": (a0: number) => Effect.Effect<boolean, readonly ["SqlError", string], never> }>(
  "k30_6"
)

export const TodoRepo = Object.assign(
  TodoRepoKey,
  {
    insert: (a0: string) => TodoRepoKey.use((a1) => a1.insert(a0)),
    all: () => TodoRepoKey.use((a0) => a0.all()),
    setDone: (a0: readonly [number, boolean]) => TodoRepoKey.use((a1) => a1.setDone(a0)),
    delete: (a0: number) => TodoRepoKey.use((a1) => a1.delete(a0))
  }
)

export const TodoAppContext = (a0: void): Effect.Effect<Context.Context<"k30_6">, never, "k30_6"> => Effect.suspend(
  () => Effect.context<"k30_6">()
)
```

The rest is the text of the earlier section with `Context.Context<never>` read as
`Context.Context<"k30_6">`: the four methods, `TodoApp`, `TodoAppLayer` and the main.

### Commands and results (E4)

Each Lean command ran inside the slot script, from the worktree. The worktree's
`ts/eff/node_modules` links to the main checkout's install, and `harness/truth/node_modules` links
to it, as the `Makefile` keeps them. Nothing was installed or downloaded.

1. `lake build` of the battery and the keyed driver's imports, then `Test.Dogfood.Scenario.TodoService`
   alone after its import guard was repaired: "Build completed successfully (1131 jobs)".
2. `lake env lean -M4096 --run harness/truth/service/EmitTodo.lean harness/truth/session/.work/service
   ../../../prelude.ts`: "EmitTodo: wrote the to-do's service module".
3. `node ts/eff/node_modules/@typescript/native-preview/bin/tsgo --noEmit -p
   harness/truth/service/tsconfig.json` (version 7.0.0-dev.20260629.1): exit 0.
4. The same with `-p harness/truth/service/red/tsconfig.json`: exit 1 with two diagnostics:
   `red/argument.ts` TS2345, a number where `add` takes a string; `red/unprovided.ts` TS2375,
   `"k30_6"` is not `never`.
5. `lake env lean -DwarningAsError=true -M4096 --run harness/truth/session/Keyed.lean scenarios`
   into the work folder: exit 0, in 8 minutes interpreted. The to-do holds 13 performable scripts.
   Two wait (`other-tag`, `wide`): the session refuses their replies.
6. `bun --no-install harness/truth/service/run-todo.ts .work/service/scenarios.json .work/service/out`
   printed two lines:

   ```text
   effect 4.0.0-rc.112 under bun 1.4.2
   PASS the to-do's service on rc.112: 13 scripts performed on its consumer's programs, each with
   the host's outcome, calls and predicted refusals equal to Lean's observation; 2 scripts with no
   host run; 2 red controls
   ```
7. `Keyed.lean scenario-batch .work/service/out/service-cases.json`: each of the 13 recordings
   replays with `same` and `journal` true and no refusal.
8. `Keyed.lean service-checks .work/service/out/service-cases.json`: all 13 runs settled. Two
   runs do not conform: `other-todo` and `toggling-twice`. The pairs `model-add`/`model-list` and
   `model-once`/`model-twice` agree with the reference model. The forgetful and toggling pairs
   do not.
9. `#axiom_audit Effect4.Codegen.Checked Effect4.Program.Authoring.ApplicationService
   Effect4.Laws.Program.ApplicationService Test.Dogfood.Scenario.TodoService`: "185 declarations
   within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals".
10. `lake build` of the importers of `Checked` and of `Tools.Code.Module`: "Build completed
    successfully (440 jobs)".

The gate ran three times after the merge `b811faeb7`, each time inside the slot script and from
the worktree. The command:

```text
lean-slot.sh make -o ts/eff/node_modules -o harness/truth/node_modules check-host-protocol
```

The two `-o` flags keep `make` from remaking the two linked installs.

11. The first run exited 2 before any step of E4. The script's `run` stopped `lake build
    Test.Dogfood.Scenario.Atomic` at its limit of 180 seconds (`subprocess.TimeoutExpired`). The
    build was cold, and two other seats' builds ran beside it.
12. The gate's remaining modules were then built by name: "Build completed successfully (1324
    jobs)". The command:

    ```text
    lake build Test.Dogfood.Scenario.Atomic Test.Dogfood.Scenario.Timeout
      Test.Dogfood.Scenario.Todo.Claims Tools.ProfileJson
      Effect4.Program.Authoring.ApplicationService Tools.Code.Module
    ```

    The second run exited 2 at its first Lean file. `lean --run tools/Tools/HostProtocol.lean`
    found no object file of `Tools.GeneratedStamp`: the gate built no import of the four Lean
    files that its script runs. The recipe now builds them (`build_imports`), and the script's
    own list of builds stays as it was.
13. The third run exited 0, from 18:02:10 to 18:12:53 with its wait for a slot. The recipe's build
    answered "Build completed successfully (1374 jobs)". The keyed lane's lines passed as before,
    and the gate's last two lines read:

    ```text
    PASS the to-do's service on rc.112: 13 scripts performed on its consumer's programs, each with
    the host's outcome, calls and predicted refusals equal to Lean's observation; 2 scripts with no
    host run; 2 red controls
    PASS host-protocol: fresh projections, typed host programs, keyed replay and negative controls;
    the scenarios' scripts on their printed modules; the to-do's service: 13 scripts on rc.112,
    each replayed to its journal; 11 conform, 2 of 4 pairs agree with the model, as on the scripts
    ```

    In `service-checks.json`, each decision equals its script's own: all 13 runs settled, and
    `other-todo` and `toggling-twice` do not conform. The pairs `model-add`/`model-list` and
    `model-once`/`model-twice` agree, and the forgetful and toggling pairs do not.

Not run: every other gate. The keyed lane's own runs use `replayRun`, which now calls
`replayedOf`; the gate's keyed lines pass with it (command 13).

### Evidence (E4)

| Claim | Evidence |
| --- | --- |
| The joined file, its consumer and the runner type-check | tested, host-only: tsgo 7, one build |
| A program over the service requires the repository's key, and nothing once a repository is provided | tested: `added`, `listed`, `completed` and `closed` in `consumer.ts`; red control `red/unprovided.ts` |
| The service answers each to-do script as Lean's observation of the script's program | tested, host-only: 13 runs on rc.112 under bun 1.4.2, one run each |
| Each service run replays in Lean to the script's journal | tested: `scenario-batch` on the 13 recordings |
| Settled, conforming and agreeing, as the battery's controls predict | tested: `service-checks`, decided on each replayed run |
| Each run's decisions are the ones of its script's own run | tested: `check_service` in the gate, one run (command 13) |
| The gate fails when a replay, a run or a pair is decided otherwise | tested: `service_controls`, three red controls, in command 13 |

The evidence is bounded: one script set, one run of each, one host. It is the claims' premise
decided on these runs, so `agrees_hostRun` and `conforms_sat` carry the to-do's claims to them.
No claim is made of another run.

### Open obligations (E4)

1. **The script's limit of 180 seconds.** The script's `run` stops each command at 180 seconds.
   The recipe's `build_imports` now builds the scenarios' batteries before the script, with no
   limit (commands 11 and 12). The script's own builds of the two contract batteries keep the
   limit. The coordinator decides whether it stays.
2. **`docs/GENERATED.md` does not name the service run.** Its host-protocol paragraph lists what
   the check performs, and this brief did not give the file. The proposed text:

   ```text
   The same check performs the to-do's scripts on its emitted Effect service (decisions row 378
   (20), `harness/truth/service/`). Lean decides each run's checks beside the script's own run.
   ```
3. **The read-back law at the to-do** needed two repairs: the header reader must read a payload
   class and a requirement row other than `never`. Seat READ's `5d602f331` makes both, on main
   after this seat's base. Main's `ab8aeefa7` flips the battery's two guards: the to-do's block is
   `blockReadable`, and its module reads back (tested, by evaluation). The law
   `readModule_printModule_defs` applied at the to-do's block, as one reader line, is not written.
4. **`other-tag` and `wide` wait**, as on the keyed lane: the session refuses their replies.

## Proposed decisions rows (proposals only)

- **Registry claims for an application's service** (to `tools/ProofGraph/Registry.lean`):
  `application-service-methods` (`context-requirements`, compatibility, pointer
  `Application.serviceDefs_mem`), and `application-service-refusal`
  (`residual-program-typing`, inversion, pointer `Application.serviceDefs_error`).
- **The file envelope beside the block envelope.** `ModuleEmission.module` stays import-free: it
  is the block that an embedding host wraps, and five batteries admit it under an ambient
  prelude. `ModuleEmission.file prelude` is the agent's file. The alternative, imports inside
  `module`, changes `emitModule_erasure` and those five batteries.
