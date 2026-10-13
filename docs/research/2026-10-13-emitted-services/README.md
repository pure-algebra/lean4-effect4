# An application emitted as an Effect service (2026-10-13)

Status: design note (history, not authority). It plans slice V2 of decisions row 378, under its
rulings (19) and (20). Base: `f5dec36a3` on `refactor/phase1-phase3`.

## The one thing to know first

The emitted to-do needs no new program syntax and no second TypeScript printer. An application becomes one
definition block in the shape the library's services already have (`Semaphore.serviceDefs`,
`src/Effect4/Library/Semaphore/Defs.lean`). It prints through `printServices`
(`src/Effect4/Codegen/Print.lean`) as an Effect service key and its layer. Its host rows become
services of their own, and two typed constructs the machine already has join the two:
`withFiber (.context keys)` and `provideContext`.

## The goal

A person imports the emitted module into an Effect program and uses it, typed:

```ts
import { TodoApp, TodoAppLayer, TodoRepo } from "./todo.gen.ts"

const program = Effect.gen(function* () {
  const todo = yield* TodoApp
  return yield* todo.add("milk")
}).pipe(Effect.provide(TodoAppLayer), Effect.provide(SqliteTodoRepo))
```

`SqliteTodoRepo` is the person's layer for `TodoRepo`. Nothing else is wired by hand.

## The semantics

Let an application have entries `e_i(x_i : P_i) : Eff A_i E_i R_i`, and let `R` be the union of
the rows' service keys. The emitted block has three kinds of definition.

| Definition | Role | Request | Body | Type |
| --- | --- | --- | --- | --- |
| `<App>Context` | `serviceInit <App>` | none | `withFiber (.context R)`: `Effect.context<R>()` | `Eff (contextOf R) never R` |
| `<App>_<e_i>` | `serviceMethod <App> e_i` | the state, then `P_i` | `provideContext state (e_i x_i)` | `Eff A_i E_i never` |
| the rows' keys | (printed from the row table) | — | `Context.Service<Shape>("Ns")` | — |

So the service's state is the context its layer read once, and each method runs its entry's
body under that context. A method's requirement is discharged by the region, so its type has
`never` there. The layer's requirement is `R`: `Layer<App, never, R>`. These are the types an
Effect user expects from a hand-written service with dependencies.

A host row call prints as `Ns.use((r) => r.method(x))` and requires the key `Ns`. It is still the
same `perform (.external i) request`; only the row's declared requirement and its printed form
change.

## The laws it owes, and where they come from

- **Read back.** The module reads back to its block: an instance of `readModule_printModule_defs`
  (`src/Effect4/Laws/Api/ModuleReadable.lean`), at the application's signature.
- **Typing.** Each method's type is its entry's type with the requirement discharged:
  `provideContext`'s typing rule (row 349) at the state's type.
- **Meaning.** A method called at arguments means its entry applied to them, under the context
  the layer read: the region's meaning. The application's claims are stated of entries, so they
  carry to methods by this one equation.
- **Checks, not laws.** tsgo 7 type-checks the module and a consumer program. rc.112 runs the
  consumer. Lean decides the per-run premises (`agrees`, `conforms`), as V4 plans.

## The slices

| Slice | What | Files | Cost |
| --- | --- | --- | --- |
| E1 | `Application.serviceDefs`: the block of the table above, each entry's type from the checker; a refused entry refuses the block | `src/Effect4/Program/Authoring/Application.lean`; a law module beside `Laws/Program/Block.lean` | M |
| E2 | The module's envelope: `export` on the service, its layer and the rows' keys; imports written from Lean data (row 373 (11)) | `src/Effect4/Codegen/Checked.lean` (`ModuleEmission.module`), `tools/Tools/Code/Module.lean` | S |
| E3 | Host rows as services: a row shape whose call prints `Ns.use((r) => r.m(x))`, read back by the same template; the row's requirement names `Ns`; the keys printed from the table | `src/Effect4/Codegen/Templates.lean`, `PrintLeaf.lean`, `Read.lean`; `ts/eff/read.ts`; the keyed lane's bindings | M–L |
| E4 | The to-do emitted, a consumer program checked by tsgo 7 and run on rc.112 against a recorded `TodoRepo` layer, and Lean's per-run checks | `Test/Dogfood/Scenario/Todo*`; `harness/truth/session/` | M |
| E5, later | Provenance: the module carries its program's digest and JSON | the envelope | S |

E1 and E2 need nothing from E3: before E3 a row is still a free name. E3 is the change of
representation; the rows' printed form changes in the printer, the Lean reader and the
TypeScript reader together, from one template.

## Questions this leaves open

1. The block's main program. The printer prints one; an application module has none of its own.
   Recommended: a main of `succeed unit` under a reserved name, until the printer takes a
   module with no main.
2. Layers (later, by the owner): an application's own layers printed as `Layer` exports beside
   the service's.
3. The service key's name and the rows' keys may collide with a user's names. The module
   exports them under the application's and the rows' names only.

## What this does not establish

No slice has run. The table's types are the design, not the checker's answers. The meaning law is
stated, not proved.
