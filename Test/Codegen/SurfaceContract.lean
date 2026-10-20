import Test.Codegen.ServicesPrint
import Effect4.Codegen.Surface

/-!
# An emission's surface: finite evaluations and the controls of a data service (CR-4)

The surface (`ModuleEmission.surface`, `src/Effect4/Codegen/Surface.lean`) is the second module of
an emission, which a consumer imports: each data service's Schemas, and its layer that decodes each
entry's input. Each guard below is a finite evaluation that no theorem covers, or a red control.
Every pin is the rendered bytes of `TypeScript.Render`, inlined in the guard, since a battery
definition over a rendered `String` reaches `Classical.choice`.

What ran the surface was rc.112, and what typed it was tsgo 7: the keyed host lane emitted the
to-do's surface, type-checked it with its consumer and ran the consumer through its layer
(`git:8e93a284f:scripts/check-host-protocol.py`). The lane was retired on 2026-10-18 and deleted
on 2026-10-20, so no gate runs the surface now.
-/

namespace Test.Codegen.SurfaceContract

open Effect4 Effect4.Program Effect4.Codegen
open TypeScript (house0)

-- The counter's surface: its Schemas, and its layer, whose `add` decodes its one argument at entry
-- and whose `get` takes none; the imports come from `effect` and the program module.
#guard (match Api.emitModule "main" Test.Codegen.ServicesPrint.counter [] with
  | .ok emission => (emission.surface "./prelude.ts" "./counter.ts").toOption.map fun m =>
      String.join (m.imports.map (TypeScript.Render.import_ house0)) ++
        String.join (m.decls.map (TypeScript.Render.decl house0))
  | .error _ => none) = some (
  "import { Effect, Layer, Schema } from \"effect\"\n" ++
  "import { Counter, CounterLayer } from \"./counter.ts\"\n" ++
  "/** The Schemas of Counter's methods: each method's arguments as one tuple, its answer and its " ++
    "error. */\n" ++
  "export const CounterSchemas = { get: { input: Schema.Tuple([]), answer: " ++
    "Schema.Number.check(Schema.isInt()).check(Schema.isGreaterThanOrEqualTo(0)), error: Schema.Never }, " ++
    "add: { input: Schema.Tuple([Schema.Number.check(Schema.isInt()).check(Schema.isGreaterThanOrEqualTo(0))]), " ++
    "answer: Schema.Number.check(Schema.isInt()).check(Schema.isGreaterThanOrEqualTo(0)), error: Schema.Never } }\n" ++
  "/** Counter from its program's layer, each method's arguments decoded at entry by its Schema; a " ++
    "failed decode dies. */\n" ++
  "export const CounterLive = Layer.provide(Layer.effect(Counter, Effect.map(Counter, (a0) => {\n" ++
  "  return { get: () => a0.get(), add: (a1: number) => Effect.flatMap(Effect.orDie(" ++
    "Schema.decodeUnknownEffect(CounterSchemas.add.input)([a1])), (a2) => a0.add(a2[0])) }\n" ++
  "})), CounterLayer)\n")

-- A queue of numbers is a data service: its surface is its Schemas and its layer.
#guard (match Test.Codegen.ServicesPrint.queueProgram with
  | some p => match Api.emitModule "main" p [] with
    | .ok emission => (emission.surface "./prelude.ts" "./queue.ts").toOption.map
        fun m => m.decls.length
    | .error _ => none
  | none => none) = some 2

/-! ## Red controls: what holds no surface -/

-- A program with no definition block has an empty surface, and imports nothing.
#guard (match Api.emitModule "main" (.succeed (.lit (.nat 1))) [] with
  | .ok emission => (emission.surface "./prelude.ts" "./main.ts").toOption.map
      fun m => (m.decls.length, m.imports.length)
  | .error _ => none) = some (0, 0)

-- A method that takes a `Ref` has no Schemas: no decode checks a handle.
#guard (entrySchemas
  { method := "read", args := [.refOf .nat],
    definition := { name := "cellRead", request := .unit, answer := .nat } }).isNone
-- A method of a generic service takes its caller's type, which no Schema fixes.
#guard (entrySchemas
  { method := "offer", args := [.var 0],
    definition := { name := "queueOffer", request := .unit, answer := .unit } }).isNone
-- A method that answers a number has its Schemas: the bridge lowers `number` (the types audit,
-- §6.1).
#guard (entrySchemas
  { method := "now", args := [],
    definition := { name := "clockNow", request := .unit, answer := .number } }).isSome

end Test.Codegen.SurfaceContract
