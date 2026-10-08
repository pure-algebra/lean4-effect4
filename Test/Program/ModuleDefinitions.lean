import Test.Program.QueueDefs
import Effect4.Modules.Semaphore.Defs

/-!
# Declared modules at their public authoring interface

These finite controls run Queue and Semaphore through generated invocations.
They check composition, explicit dependencies, specialization names and TypeScript printing.
The runs observe one fuel budget and one schedule. They establish no scheduling theorem.
The general inlining observation remains G7 under decisions row 329.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.ModuleDefinitions

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Program.QueueScenarios (Ops library scenariosWith)
open Test.Program.QueueDefs (programOf exitAt)

/-- Two specializations, each constructed once with its own names and invocations. -/
def numbers : Queue.Definitions := Queue.Definitions.make "Number Queue" .nat
def strings : Queue.Definitions := Queue.Definitions.make "String.Queue" .string

def invoked : Ops :=
  { take := fun _ => numbers.take, offer := fun _ => numbers.offer, size := fun _ => numbers.size }

-- Each existing Queue scenario runs through the generated interface.
#guard (List.zip (scenariosWith invoked) (scenariosWith library)).all fun (d, l) =>
  let defined := (programOf (numbers.module d)).bind (exitAt 1000)
  defined.isSome && decide (defined = (programOf { main := l }).bind (exitAt 1000))

/-- Run a built module at the finite budget used by these scenarios. -/
def runModule (m : Module NativeOp) : Option ExitV := (programOf m).bind (exitAt 1000)

/-- The target printer accepts a built module. -/
def prints (m : Module NativeOp) : Bool :=
  match Api.Author.build m with
  | .error _ => false
  | .ok built =>
    (Api.printModule "main" built.program built.table).isSome

/-- The existing reader refuses unreadable handle headers after successful printing. -/
def readResult (m : Module NativeOp) : Option (Except ReadRefusal Api.Program) :=
  (Api.Author.build m).toOption.bind fun built =>
    (Api.printModule "main" built.program built.table).map fun printed =>
      Api.readModule printed built.table

/-- The two Queue instances retain their separate message types and names. -/
def twoTypes : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let s ← Queue.bounded .string 2
  let _ ← numbers.offer q (nat 3)
  let _ ← strings.offer s (str "three")
  let n ← numbers.take q
  let t ← strings.take s
  let empty ← strings.poll s
  return tuple [n, t, empty]

def twoTypesModule : Module NativeOp := numbers.install (strings.module twoTypes)

#guard runModule twoTypesModule = some (.success (.list [.nat 3, .str "three", .none]))
#guard prints twoTypesModule
-- The handle request is outside the existing type reader's domain, on both authoring surfaces.
#guard (Queue.defs .nat).all fun d => !d.decl.readable
#guard numbers.defs.all fun d => !d.decl.readable
#guard readResult { defs := Queue.defs .nat, main := succeed unit } =
  some (.error (.shape "definition"))
#guard readResult twoTypesModule = some (.error (.shape "definition"))
-- Changing installation order changes indices, but these invocations still resolve by name.
#guard runModule (strings.install (numbers.module twoTypes)) = runModule twoTypesModule
-- The wrong message type still refuses through ordinary program admission.
#guard (Api.Author.build (strings.module (eff do
  let q ← Queue.bounded .string 1
  strings.offer q (nat 7)))).toOption.isNone

/-- Semaphore is the second library using the same declaration command. -/
def permits : Semaphore.Definitions := Semaphore.Definitions.make "Permits"

def immediate : Src NativeOp := eff do
  let q ← Semaphore.make 2
  let taken ← permits.take q (nat 1)
  let free ← permits.release q (nat 1)
  let first ← permits.takeIfAvailable q (nat 2)
  let second ← permits.takeIfAvailable q (nat 1)
  return tuple [taken, free, first, second]

#guard runModule (permits.module immediate) =
  some (.success (.list [.nat 1, .nat 2, .bool true, .bool false]))
#guard prints (permits.module immediate)
#guard permits.defs.all fun d => !d.decl.readable
#guard readResult (permits.module immediate) = some (.error (.shape "definition"))

/-- A stored invocation waits in a child and resumes after a release. -/
def waiting : Src NativeOp := eff do
  let q ← Semaphore.make 1
  let _ ← permits.take q (nat 1)
  let worker ← fork (permits.take q (nat 1))
  let free ← permits.release q (nat 1)
  let acquired ← join worker
  return tuple [free, acquired]

#guard runModule (permits.module waiting) = some (.success (.list [.nat 1, .nat 1]))

/-- Queue and Semaphore share one authored module. -/
def combined : Src NativeOp := eff do
  let q ← Queue.bounded .nat 1
  let s ← Semaphore.make 1
  let _ ← permits.take s (nat 1)
  let _ ← numbers.offer q (nat 23)
  let value ← numbers.take q
  let free ← permits.release s (nat 1)
  return tuple [value, free]

#guard runModule (numbers.install (permits.module combined)) =
  some (.success (.list [.nat 23, .nat 1]))
#guard prints (numbers.install (permits.module combined))

-- An authored operation can use another instance's invocations.
eff_module Relay (queueApi : Queue.Definitions) where
  exchange (queue : Queue.handleTy .nat) (value : .nat) : .nat := eff do
    let _ ← queueApi.offer queue value
    queueApi.take queue

def relay : Relay := Relay.make "Relay" numbers

def relayed : Src NativeOp := eff do
  let q ← Queue.bounded .nat 1
  relay.exchange q (nat 29)

#guard runModule (numbers.install (relay.module relayed)) = some (.success (.nat 29))
#guard runModule (relay.install (numbers.module relayed)) = some (.success (.nat 29))
-- Omitted dependencies report the name missing from the authored module.
#guard match Api.Author.build (relay.module relayed) with
  | .error (.scope r) => r.reason == .unboundDef "e4$Number_32_Queue$offer"
  | _ => false
-- Installing an instance twice retains the existing duplicate-name refusal.
#guard match Api.Author.build (numbers.install (numbers.module (succeed unit))) with
  | .error (.scope r) => r.reason == .duplicateDef "e4$Number_32_Queue$take"
  | _ => false
-- Giving two specializations the same name never silently chooses one.
#guard match Api.Author.build
    (numbers.install ((Queue.Definitions.make "Number Queue" .string).module (succeed unit))) with
  | .error (.scope r) => r.reason == .duplicateDef "e4$Number_32_Queue$take"
  | _ => false

end Test.Program.ModuleDefinitions
