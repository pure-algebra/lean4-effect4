# Proposals for the Effect Face and Module Reader (2026-10-13)

Status: proposals for owner ruling (history, not authority).

Running `lake env lean --run apps/todo/EmitTodo.lean OUT ../../../harness/truth/prelude.ts` writes
the to-do application as `todo.gen.ts`. An Effect user reading `todo.gen.ts` meets three shapes
that idiomatic Effect code does not write. Probing `cached` (`Test/Dogfood/Scenario/Todo/Cached.lean`)
exposed a fourth shape at the module reader boundary. Each change alters printed TypeScript
(`Print.printModule`), a judgment, or a representation's boundary, so this document records all
four as proposals for the owner to rule.

---

## Proposal 1 — Emit Message-Only Tagged Failures as `Data.TaggedError` Classes Instead of Pairs

### Why It Arises

In `Test/Dogfood/Scenario/Todo.lean`, `NotFound` has field `id : .nat`, whereas `SqlError` and
`EmptyTitle` carry only a message (`errorSqlError := Ty.taggedError "SqlError"`). Under decisions
row 120 (`src/Effect4/Codegen/Classes.lean`, `errorClass?`), a tagged error with fields beyond
`message` becomes a `Data.TaggedError` class (`NotFound`). A message-only tagged error stays the
DB-15 pair `Ty.prod (.litString tag) .string`. Consequently, `todo.gen.ts` mixes `NotFound` class
instances with `readonly ["SqlError", string]` and `readonly ["EmptyTitle", string]` tuples in the
same error union.

### Text Now (`todo.gen.ts`)

```ts
export class NotFound extends Data.TaggedError("NotFound")<{
  readonly id: number
}> {}

export class TodoRepoKey extends ServiceMap.Service<TodoRepoKey, {
  readonly all: () => Effect.Effect<ReadonlyArray<Todo>, readonly ["SqlError", string], never>
  readonly find: (a0: number) => Effect.Effect<Option.Option<Todo>, readonly ["SqlError", string], never>
  readonly insert: (a0: string) => Effect.Effect<Todo, readonly ["SqlError", string], never>
  readonly setDone: (a0: readonly [number, boolean]) => Effect.Effect<boolean, readonly ["SqlError", string], never>
  readonly remove: (a0: number) => Effect.Effect<boolean, readonly ["SqlError", string], never>
}>()("TodoRepo") {}

export const TodoApp_add = (a0: readonly [ServiceMap.ServiceMap<TodoRepo>, string]): Effect.Effect<
  Todo,
  readonly ["EmptyTitle", string] | readonly ["SqlError", string],
  never
> =>
  Effect.if(eq(a0[1], ""), {
    onTrue: () => Effect.fail(pair("EmptyTitle", "title must not be empty")),
    onFalse: () => Effect.provide(Effect.flatMap(Effect.service(TodoRepo), (_s) => _s.insert(a0[1])), a0[0])
  });
```

### Proposed Text

```ts
export class EmptyTitle extends Data.TaggedError("EmptyTitle")<{
  readonly message: string
}> {}

export class NotFound extends Data.TaggedError("NotFound")<{
  readonly id: number
}> {}

export class SqlError extends Data.TaggedError("SqlError")<{
  readonly message: string
}> {}

export class TodoRepoKey extends ServiceMap.Service<TodoRepoKey, {
  readonly all: () => Effect.Effect<ReadonlyArray<Todo>, SqlError, never>
  readonly find: (a0: number) => Effect.Effect<Option.Option<Todo>, SqlError, never>
  readonly insert: (a0: string) => Effect.Effect<Todo, SqlError, never>
  readonly setDone: (a0: readonly [number, boolean]) => Effect.Effect<boolean, SqlError, never>
  readonly remove: (a0: number) => Effect.Effect<boolean, SqlError, never>
}>()("TodoRepo") {}

export const TodoApp_add = (a0: readonly [ServiceMap.ServiceMap<TodoRepo>, string]): Effect.Effect<
  Todo,
  EmptyTitle | SqlError,
  never
> =>
  Effect.if(eq(a0[1], ""), {
    onTrue: () => Effect.fail(new EmptyTitle({ message: "title must not be empty" })),
    onFalse: () => Effect.provide(Effect.flatMap(Effect.service(TodoRepo), (_s) => _s.insert(a0[1])), a0[0])
  });
```

### Law That Must Keep Holding

- **Exact embedding of printed modules**: `read_print` (`src/Effect4/Laws/Codegen/ReadPrint.lean`),
  `readModule_printModule_defs` (`src/Effect4/Laws/Api/ModuleReadable.lean`), and `ModuleEmission.admit`
  (`src/Effect4/Laws/Codegen/Admit.lean`).
- **One wire representation at the host boundary**: In `harness/truth/prelude.ts`, `pairOf` case 3
  already projects a message-only `Data.TaggedError` instance to `[tag, message]` on the wire.
  `Tools.RunChecks.decodeReason` (`tools/Tools/RunChecks.lean`) and `Truth.lean` continue to
  observe `.fail (.tagged tag msg)` with `Err` unchanged.
- **Disjointness from two-element string tuples**: Within `Eff`, a message-only error carries
  `_ty_error` metadata (as payload errors do in `Authoring/Error.lean`) or a dedicated `Ty`
  constructor. An ordinary pair `Ty.prod (.litString "SqlError") .string` stays distinct from the
  error class `SqlError`.

### What rc.112 Does

- `Data.TaggedError` (`vendor/effect-4.0.0-rc.112/src/Data.ts`, declaration `TaggedError` and
  `vendor/effect-4.0.0-rc.112/src/internal/core.ts`, declaration `TaggedError`) constructs a
  yieldable `Error` subclass carrying `readonly _tag: Tag` and `Readonly<A>`, including
  `readonly message: string`.
- `Effect.catchTag` (`vendor/effect-4.0.0-rc.112/src/Effect.ts`, declaration `catchTag`) dispatches
  on `{ readonly _tag: string }` objects and class instances, never on `readonly [Tag, string]`
  tuples.

### Cost

- **Medium (M)**: Update `Authoring/Error.lean`, `Classes.errorClass?`
  (`src/Effect4/Codegen/Classes.lean`), `PrintLeaf.lean`, `Read.lean`, `ts/eff/read.ts`, and their
  round-trip theorems in `src/Effect4/Laws/Codegen/{Classes,ReadPrint,Module,Admit}.lean`.

---

## Proposal 2 — Keep Internal Service Helpers Unexported (`const` Instead of `export const`)

### Why It Arises

`Print.printDef` (`src/Effect4/Codegen/Print.lean`) emits every `DefDecl` in `defsOf p` as
`Stmt.exportConst`. `Print.printServices` also emits `Stmt.exportConst (sv.name ++ "Context")`. In
`Application.serviceModule`, `TodoAppContext`, `TodoApp_*`, `listCacheMake`, `listCacheGet`, and
`listCacheInvalidate` are internal helpers wired into `TodoAppLayer` and `ListCacheLayer`.
Exporting them pollutes the module's public TypeScript surface.

### Text Now (`todo.gen.ts`)

```ts
export const TodoAppContext: Effect.Effect<ServiceMap.ServiceMap<TodoRepo>, never, TodoRepo> =
  Effect.context<TodoRepo>();
export const TodoApp_add = (a0: readonly [ServiceMap.ServiceMap<TodoRepo>, string]): Effect.Effect<…> => …;
export const TodoApp_list = (a0: readonly [ServiceMap.ServiceMap<TodoRepo>, void]): Effect.Effect<…> => …;
export const TodoApp_complete = (a0: readonly [ServiceMap.ServiceMap<TodoRepo>, number]): Effect.Effect<…> => …;
export const TodoApp_remove = (a0: readonly [ServiceMap.ServiceMap<TodoRepo>, number]): Effect.Effect<…> => …;
export class TodoApp extends ServiceMap.Service<TodoApp, { … }>()("TodoApp") {}
export const TodoAppLayer: Layer.Layer<TodoApp, never, TodoRepo> =
  Layer.effect(TodoApp, Effect.map(TodoAppContext, (_s) => ({ … })));
export const main: Effect.Effect<void, never, never> = Effect.succeed(undefined);
```

### Proposed Text

```ts
const TodoAppContext: Effect.Effect<ServiceMap.ServiceMap<TodoRepo>, never, TodoRepo> =
  Effect.context<TodoRepo>();
const TodoApp_add = (a0: readonly [ServiceMap.ServiceMap<TodoRepo>, string]): Effect.Effect<…> => …;
const TodoApp_list = (a0: readonly [ServiceMap.ServiceMap<TodoRepo>, void]): Effect.Effect<…> => …;
const TodoApp_complete = (a0: readonly [ServiceMap.ServiceMap<TodoRepo>, number]): Effect.Effect<…> => …;
const TodoApp_remove = (a0: readonly [ServiceMap.ServiceMap<TodoRepo>, number]): Effect.Effect<…> => …;
export class TodoApp extends ServiceMap.Service<TodoApp, { … }>()("TodoApp") {}
export const TodoAppLayer: Layer.Layer<TodoApp, never, TodoRepo> =
  Layer.effect(TodoApp, Effect.map(TodoAppContext, (_s) => ({ … })));
export const main: Effect.Effect<void, never, never> = Effect.succeed(undefined);
```

### Law That Must Keep Holding

- **Module round-trip and exactness**: `readModule_printModule_defs` and `printModule_roundTrip`
  (`src/Effect4/Laws/Api/ModuleReadable.lean`), plus `ModuleEmission.admit`
  (`src/Effect4/Laws/Codegen/Admit.lean`).
- When `servicesOf p` is non-empty, service-backed definitions (`sv.methods` and `sv.make`) and
  `sv.name ++ "Context"` print with `Stmt.constDecl`. Standalone definition blocks without services
  (`servicesOf p = []`) keep `export const` so existing corpus modules do not change.

### What rc.112 Does

- Compare `vendor/effect-4.0.0-rc.112/src/Layer.ts` (`effect`, `succeed`) and
  `vendor/effect-4.0.0-rc.112/src/Context.ts` (`Service`). A module exports its `Context.Service`
  tag class and its `Layer.Layer` value while keeping helper functions local (`const`).

### Cost

- **Small–Medium (S–M)**: Add `Stmt.constDecl` in `vendor/typescript`, and update
  `src/Effect4/Codegen/{Print,Read}.lean`, `ts/eff/read.ts`, and
  `src/Effect4/Laws/Codegen/{Module,Admit}.lean`.

---

## Proposal 3 — Curried or Multi-Parameter Service Entry Definitions Instead of a `[Context, Arg]` Tuple

### Why It Arises

`Application.methodDef` (`src/Effect4/Program/Authoring/ApplicationService.lean`) gives every
service method definition a single parameter `"state"` of type `Ty.prod ctx e.requestTy`, where
`ctx` is the product of the application's context types (`Context.Context<"TodoRepo">`). Inside the
body, the context is projected as `fst(a0)` and the method's request is projected as `snd(a0)`.
Consequently, `TodoApp_add` takes `a0: readonly [ServiceMap.ServiceMap<TodoRepo>, string]`, and
`TodoAppLayer` wraps each method in a closure `(a0: string) => TodoApp_add(pair(_s, a0))` that
allocates a two-element array at every call.

### Text Now (`todo.gen.ts`)

```ts
export const TodoApp_add = (
  a0: readonly [ServiceMap.ServiceMap<TodoRepo>, string]
): Effect.Effect<Todo, readonly ["EmptyTitle", string] | readonly ["SqlError", string], never> =>
  Effect.if(eq(a0[1], ""), {
    onTrue: () => Effect.fail(pair("EmptyTitle", "title must not be empty")),
    onFalse: () => Effect.provide(Effect.flatMap(Effect.service(TodoRepo), (_s) => _s.insert(a0[1])), a0[0])
  });

export const TodoAppLayer: Layer.Layer<TodoApp, never, TodoRepo> =
  Layer.effect(
    TodoApp,
    Effect.map(TodoAppContext, (_s) => ({
      add: (a0: string) => TodoApp_add(pair(_s, a0)),
      list: () => TodoApp_list(pair(_s, undefined)),
      complete: (a0: number) => TodoApp_complete(pair(_s, a0)),
      remove: (a0: number) => TodoApp_remove(pair(_s, a0))
    }))
  );
```

### Proposed Text

`DefDecl` (`src/Effect4/Program/Eff.lean`) already holds a parameter list (`params : List
ParamDecl`). `Application.methodDef` can pass the context and the entry's parameters as separate
`ParamDecl` entries:


```ts
export const TodoApp_add = (
  a0: ServiceMap.ServiceMap<TodoRepo>,
  a1: string
): Effect.Effect<Todo, readonly ["EmptyTitle", string] | readonly ["SqlError", string], never> =>
  Effect.if(eq(a1, ""), {
    onTrue: () => Effect.fail(pair("EmptyTitle", "title must not be empty")),
    onFalse: () => Effect.provide(Effect.flatMap(Effect.service(TodoRepo), (_s) => _s.insert(a1)), a0)
  });

export const TodoApp_list = (
  a0: ServiceMap.ServiceMap<TodoRepo>
): Effect.Effect<ReadonlyArray<Todo>, readonly ["SqlError", string], never> =>
  Effect.provide(Effect.flatMap(Effect.service(TodoRepo), (_s) => _s.all()), a0);

export const TodoAppLayer: Layer.Layer<TodoApp, never, TodoRepo> =
  Layer.effect(
    TodoApp,
    Effect.map(TodoAppContext, (_s) => ({
      add: (a0: string) => TodoApp_add(_s, a0),
      list: () => TodoApp_list(_s),
      complete: (a0: number) => TodoApp_complete(_s, a0),
      remove: (a0: number) => TodoApp_remove(_s, a0)
    }))
  );
```

### Law That Must Keep Holding

- **Service-module typing and readability**: `checked_of_serviceModule`
  (`src/Effect4/Laws/Program/ApplicationService.lean`), `serviceWF` (`src/Effect4/Program/Eff.lean`),
  and `readModule_printModule_defs` (`src/Effect4/Laws/Api/ModuleReadable.lean`).
- Currently `serviceWF` checks that each service method's backing `DefDecl` has a single parameter
  of type `Ty.prod stateTy reqTy` (`methodShape?` in `src/Effect4/Program/Eff.lean`). Under this
  proposal, `methodShape?` matches `d.params` as `(stateParam :: reqParams)` directly, eliminating
  `pair(_s, a0)` and `pair(_s, undefined)` from `printServices` and `readServices`.

### What rc.112 Does

- Compare `vendor/effect-4.0.0-rc.112/src/Layer.ts` (`effect`) and
  `vendor/effect-4.0.0-rc.112/src/Context.ts` (`Service`). Service methods pass the captured
  `Context` and method arguments as separate parameters without packing `[context, arg]` into a
  tuple.

### Cost

- **Medium (M)**: Update `Application.methodDef`
  (`src/Effect4/Program/Authoring/ApplicationService.lean`), `methodShape?`
  (`src/Effect4/Program/Eff.lean`), `printServices` (`src/Effect4/Codegen/Print.lean`),
  `readServices` (`src/Effect4/Codegen/Read.lean` and `ts/eff/read.ts`), and their laws in
  `src/Effect4/Laws/Program/ApplicationService.lean` and `src/Effect4/Laws/Codegen/{Module,Admit}.lean`.

---

## Proposal 4 (From the Probe) — Read `Ref.Ref<A>` in Definition Headers (`readDefHead`, `readParam`) While Preserving §B19 on Expression Type Arguments

### Why It Arises

In `Test/Dogfood/Scenario/Todo/Cached.lean`, imposing `refCache` on the to-do application splices
`listCacheMake`, `listCacheGet`, and `listCacheInvalidate` into the emitted module. Their headers
take and return `Ref.Ref<Option.Option<ReadonlyArray<Todo>>>`, and `TodoApp_*` takes
`readonly [ServiceMap.ServiceMap<TodoRepo>, Ref.Ref<Option.Option<ReadonlyArray<Todo>>>]`.
`Api.emitModule` prints those headers cleanly via `Types.ofNormalized` (`| .refOf a => ...`).
However, `Api.readFile`, `Api.readModule`, and `ts/eff/read.ts` refuse the emitted module with
`ReadRefusal.shape "definition"` because `readDefHead` and `readParam` call `Classes.readTyChecked`,
which has no arm for `["Ref", "Ref"]`.

Adding `["Ref", "Ref"]` unconditionally to `Classes.readNamed` breaks `Test/Codegen/TermRows.lean`
and `ts/eff/test/term-rows.test.ts`. The frozen contract `Test/contracts/faces.contract.md` (§B19)
pins that `Classes.readTy {}` refuses `Ref.Ref<A>` at expression type arguments and loop cursor
annotations.

### Text Now (`src/Effect4/Codegen/Read.lean`)

```lean
def readParam (env : Classes.TypeEnv) : TypeScript.Param → Option ParamDecl
  | .value _ (some t) => (env.readTyChecked t).map (.value ·)
  | .effect _ a e => do
    return .effect (← env.readTyChecked a) (← env.readTyChecked e)
  | _ => none

def readDefHead (env : Classes.TypeEnv) (ps : List TypeScript.Param)
    (ret : Option TypeScript.TypeRef) : Option (List ParamDecl × Ty × Ty × List Ty) := do
  let params ← ps.mapM (readParam env)
  let .app (.ident ["Effect", "Effect"]) [aRef, eRef, rRef] ← ret | none
  let a ← env.readTyChecked aRef
  let e ← env.readTyChecked eRef
  let rs ← readReqs env.names rRef
  return (params, a, e, rs)
```

### Proposed Text

A dedicated header reader `env.readHeaderTyChecked` (and `readHeaderType` in `ts/eff/read.ts`)
serves `readParam` and `readDefHead`. It extends `readNamed` with `| ["Ref", "Ref"], [x] => some
(.refOf x)` and leaves `env.readTyChecked` unchanged for expressions and loop cursors:

```lean
def readParam (env : Classes.TypeEnv) : TypeScript.Param → Option ParamDecl
  | .value _ (some t) => (env.readHeaderTyChecked t).map (.value ·)
  | .effect _ a e => do
    return .effect (← env.readHeaderTyChecked a) (← env.readHeaderTyChecked e)
  | _ => none

def readDefHead (env : Classes.TypeEnv) (ps : List TypeScript.Param)
    (ret : Option TypeScript.TypeRef) : Option (List ParamDecl × Ty × Ty × List Ty) := do
  let params ← ps.mapM (readParam env)
  let .app (.ident ["Effect", "Effect"]) [aRef, eRef, rRef] ← ret | none
  let a ← env.readHeaderTyChecked aRef
  let e ← env.readHeaderTyChecked eRef
  let rs ← readReqs env.names rRef
  return (params, a, e, rs)
```

### Law That Must Keep Holding

- **Frozen contract §B19**: `Classes.readTy {}` still returns `none` on `Ref.Ref<number>`, so
  `Deferred.make<Ref.Ref<number>, never>()` and `let a0: Ref.Ref<number>` remain refused by
  `readEff` (`Test/Codegen/TermRows.lean` and `ts/eff/test/term-rows.test.ts`).
- **Header retraction**: `env.readHeaderTyChecked (env.declarationType ty) = some ty` for every
  header-readable `ty` (including `.refOf a`), so `readModule_printModule_defs` and
  `Api.readFile` succeed on `cached` (`Test/Dogfood/Scenario/Todo/Cached.lean`).

### What rc.112 Does

- `Ref.Ref<A>` (`vendor/effect-4.0.0-rc.112/src/Ref.ts`, interface `Ref`) is the type annotation of
  a mutable cell passed to or returned from a helper function (`Ref.make`, `Ref.get`, `Ref.set`).

### Cost

- **Small (S)**: Add `TypeEnv.readHeaderTyChecked` in `src/Effect4/Codegen/Classes.lean`, wire it in
  `src/Effect4/Codegen/Read.lean` and `ts/eff/read.ts`, and update
  `src/Effect4/Laws/Codegen/{Classes,ReadPrint,Module,Admit}.lean`.

