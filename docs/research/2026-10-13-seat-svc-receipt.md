# 2026-10-13 seat SVC receipt: the application emitted as one Effect service (E1, E2)

**The one thing to know before merging:** the to-do emits as one Effect service. The compiler
tsgo 7 accepts the file and a consumer, but only beside a host declaration of `TodoRepo`. The
rows' namespace stays a free name until seat ROWS declares the rows' keys. The read-back law
reaches a class-free application but not the to-do. Two of the to-do's methods declare the
payload class `NotFound`, which the definition header reader does not read.

Status: receipt (history, not authority). Brief: the coordinator's dispatch of 2026-10-13, slices
E1 and E2 of `docs/research/2026-10-13-emitted-services/README.md` under row 378 (19) and (20).
The coordinator's later messages added the key spelling's move and the merge of `6f32c88cd`.

## Base and head

Branch `seat/svc`, worktree `/Users/pooks/Dev/lean4-effect4-svc`, base `c2620b4ac`. The head is
the commit of this receipt, after `39c876adf`.

| Commit | What |
| --- | --- |
| `b002e17c5` | the context type prints; the key spelling moves to `Types.lean` (merged to main as `9be016a0a`) |
| `09e8637a2` | merge of `refactor/phase1-phase3` at `6f32c88cd`: the coordinator's one key reader |
| `088de151b` | merge of `refactor/phase1-phase3` at `516f13bf8`: `serviceKeyDecl`, the corpus rows |
| `39c876adf` | E1, E2, the battery, the laws and this check's evidence (merged to main as `45761a86a`) |

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

## Proposed decisions rows (proposals only)

- **Registry claims for an application's service** (to `tools/ProofGraph/Registry.lean`):
  `application-service-methods` (`context-requirements`, compatibility, pointer
  `Application.serviceDefs_mem`), and `application-service-refusal`
  (`residual-program-typing`, inversion, pointer `Application.serviceDefs_error`).
- **The file envelope beside the block envelope.** `ModuleEmission.module` stays import-free: it
  is the block that an embedding host wraps, and five batteries admit it under an ambient
  prelude. `ModuleEmission.file prelude` is the agent's file. The alternative, imports inside
  `module`, changes `emitModule_erasure` and those five batteries.
