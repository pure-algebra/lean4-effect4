import Effect4.Laws.Api.ModuleReadable
import Effect4.Library.Queue.Defs
import Effect4.Library.Semaphore.Defs
import Effect4.Api.Author

/-!
# A block's services printed (decisions rows 338 and 339, slice CO-6b)

A block's roles declare its services (`DefRole`). The module printer prints each service after
the definitions, as its key and its layer (`printServices`): the layer runs the service's initial
program once, and each method closes over the state it built. The reader gives the roles back
from the layers (`roleOf`), and the round trip is `Api.printModule_roundTrip` on a program in
`blockReadable` (the claim `module-defs-round-trip`, `readModule_printModule_defs`).

The lines below are finite evaluations of the printed text, of the round trip and of the readable
domain at fixed programs, a control of the readable domain, and the controls of each refusal. The printed text is target syntax
only: tsgo's verdict and rc.112's run are the truth lane's.
-/

namespace Test.Codegen.ServicesPrint

open Effect4 Effect4.Program Effect4.Program.Authoring

/-- A counter service: its initial program answers 5; `get` answers the state; `add` adds its
argument to the state. -/
def counter (init : DefRole := .serviceInit "Counter") (initRequest : Ty := .unit)
    (getTy : Ty := .nat) (main : NativeEff := .perform (.call 0) (.lit .unit))
    (getName : String := "get") : NativeEff :=
  .defs [{ name := "counterMake", request := initRequest, answer := .nat, role := init },
         { name := "counterGet", request := getTy, answer := getTy,
           role := .serviceMethod "Counter" getName 0 },
         { name := "counterAdd", request := .prod .nat .nat, answer := .nat,
           role := .serviceMethod "Counter" "add" 1 }]
    (.cons (.succeed (.lit (.nat 5))) (.cons (.succeed (.var 0))
      (.cons (.succeed (.app "add" (.cons (.app "fst" (.cons (.var 0) .nil))
        (.cons (.app "snd" (.cons (.var 0) .nil)) .nil)))) .nil)))
    main

/-- Whether a program's module reads back to the program. -/
def roundTrips (p : NativeEff) : Bool :=
  match (Api.printModule "main" p).map Api.readModule with
  | some (.ok q) => decide (q = p)
  | _ => false

/-! ## The printed text (finite evaluations) -/

-- the key and the layer follow the definitions: the layer runs `counterMake` once, and each
-- method closes over its answer `a0`
#guard (Api.printModule "main" (counter)).map
    (fun m => String.join (m.decls.drop 3 |>.map (TypeScript.Render.decl TypeScript.house0))) =
  some ("export const Counter = Context.Service<\"Counter\", { readonly get: () => " ++
    "Effect.Effect<number, never, never>; readonly add: (a1: number) => " ++
    "Effect.Effect<number, never, never> }>(\"Counter\")\n" ++
    "export const CounterLayer = Layer.effect(Counter, Effect.map(counterMake(), (a0) => {\n" ++
    "  return { get: () => counterGet(a0), add: (a1: number) => counterAdd(pair(a0, a1)) }\n" ++
    "}))\n" ++
    "export const main: Effect.Effect<number, never, never> = counterMake()\n")

/-! ## The round trip (finite evaluations) -/

-- the counter's module reads back to the program, roles included, and the program is in the
-- readable domain of a block, so `Api.printModule_roundTrip` covers it
#guard roundTrips counter
#guard blockReadable [] (nativeSignature []) counter

/-- A queue of numbers as a service, used by the main program through its initial program and two
of its methods. -/
def queueModule : Module NativeOp :=
  { defs := Queue.serviceDefs .nat "NumberQueue" 2,
    main := eff do
      let q ← Def.invoke "queueMake" []
      let a ← (Queue.offerD .nat).call q (nat 1)
      let x ← (Queue.takeD .nat).call q
      return tuple [a, x] }

/-- The queue module's program. -/
def queueProgram : Option Api.Program :=
  (Effect4.Api.Author.build queueModule).toOption.map (·.program)

-- the Queue's service prints its key and its layer after the five definitions
#guard (queueProgram.bind fun p => (Api.printModule "main" p).map fun m =>
    m.decls.filterMap (fun d => match d with | .const c => some c.name | _ => none)) =
  some ["queueMake", "queueTake", "queueOffer", "queuePoll", "queueSize", "NumberQueue",
    "NumberQueueLayer", "main"]
-- control: the Queue's module is outside the readable domain, since its handle, a reference to
-- the queue's record, is no readable type; so the round trip says nothing of it
#guard !Effect4.Codegen.Classes.ReadableTy (Queue.handleTy .nat)
#guard queueProgram.map (blockReadable [] (nativeSignature [])) = some false

/-- A semaphore of two permits as a service, used by the main program through its initial
program and its three methods. -/
def semaphoreModule : Module NativeOp :=
  { defs := Semaphore.serviceDefs "Permits" 2,
    main := eff do
      let s ← Def.invoke "semaphoreMake" []
      let a ← Def.invoke "semaphoreTake" [s, nat 1]
      let b ← Def.invoke "semaphoreTakeIfAvailable" [s, nat 5]
      let c ← Def.invoke "semaphoreRelease" [s, nat 1]
      return tuple [a, b, c] }

/-- The semaphore module's program. -/
def semaphoreProgram : Option Api.Program :=
  (Effect4.Api.Author.build semaphoreModule).toOption.map (·.program)

-- the Semaphore's service prints its key and its layer after the four definitions
#guard (semaphoreProgram.bind fun p => (Api.printModule "main" p).map fun m =>
    m.decls.filterMap (fun d => match d with | .const c => some c.name | _ => none)) =
  some ["semaphoreMake", "semaphoreTake", "semaphoreRelease", "semaphoreTakeIfAvailable",
    "Permits", "PermitsLayer", "main"]

/-! ## Controls: what the printer refuses -/

/-- A main program that invokes nothing. -/
def one : NativeEff := .succeed (.lit (.nat 1))

-- each control program is admitted: only its services are refused
#guard [counter (init := .plain) (main := one), counter (initRequest := .nat) (main := one),
    counter (getTy := .string) (main := one)].all fun p => (Api.check p).isOk
-- a method of a service that the block does not declare
#guard (Api.printModule "main" (counter (init := .plain) (main := one))).isNone
-- an initial program whose request is not `unit`
#guard (Api.printModule "main" (counter (initRequest := .nat) (main := one))).isNone
-- a method whose request is not the state
#guard (Api.printModule "main" (counter (getTy := .string) (main := one))).isNone
-- a method whose name is no plain key: a literal would read `__proto__` as the prototype, and
-- `bad-name` is no identifier (Codex's CO6B-KEYS)
#guard [counter (getName := "__proto__"), counter (getName := "bad-name")].all fun p =>
  (Api.check p).isOk && (Api.printModule "main" p).isNone

/-- Two services whose names collide: the second's key is the first's layer (Codex's
CO6B-NAMES). -/
def colliding : NativeEff :=
  .defs [{ name := "sMake", request := .unit, answer := .nat, role := .serviceInit "S" },
         { name := "sGet", request := .nat, answer := .nat, role := .serviceMethod "S" "get" 0 },
         { name := "tMake", request := .unit, answer := .nat, role := .serviceInit "SLayer" },
         { name := "tGet", request := .nat, answer := .nat,
           role := .serviceMethod "SLayer" "get" 0 }]
    (.cons (.succeed (.lit (.nat 1))) (.cons (.succeed (.var 0))
      (.cons (.succeed (.lit (.nat 2))) (.cons (.succeed (.var 0)) .nil))))
    one

-- the program is admitted, and its services do not print
#guard (Api.check colliding).isOk && (Api.printModule "main" colliding).isNone

/-! ## The reader refuses a service image the printer would not write -/

/-- A layer whose `get` passes `99` where the printer passes the state `a0` (Codex's
CO6B-READ): the method answers otherwise on the host. -/
def changeGet (c : TypeScript.ConstDecl) : TypeScript.ConstDecl :=
  match c.value with
  | .call (.ident "Layer.effect")
      [k, .call (.ident "Effect.map") [i, .arrowBlock ps [.ret (.object closures)] t]] =>
    { c with value := .call (.ident "Layer.effect") [k, .call (.ident "Effect.map") [i,
        .arrowBlock ps [.ret (.object (closures.map fun x =>
          if x.1 = "get" then (x.1, .lambda [] (.call (.ident "counterGet") [.int 99]) none)
          else x))] t]] }
  | _ => c

/-- The counter's module with its layer changed by `changeGet`. -/
def changedCounter : Option TypeScript.Module :=
  (Api.printModule "main" counter).map fun m =>
    { m with decls := m.decls.map fun d => match d with
      | .const c => .const (if c.name = "CounterLayer" then changeGet c else c)
      | d => d }

-- the change reaches the module, and the reader refuses it (the printed module itself reads
-- back: `roundTrips counter`, above)
#guard changedCounter.isSome && changedCounter != Api.printModule "main" counter
#guard (changedCounter.map fun m => (Api.readModule m).toOption.isNone) = some true

end Test.Codegen.ServicesPrint
