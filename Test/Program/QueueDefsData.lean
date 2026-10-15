import Test.Program.QueueScenariosData
import Effect4.Library.Queue.Defs
import Effect4.Api.Codegen

/-! Program data shared by the battery and engine fixture writer. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueDefs

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Program.QueueScenarios (Ops library mk scenariosWith r1With)

/-- The operations as invocations of the module's definitions, at number messages. -/
def invoked : Ops :=
  { take := fun _ => (Queue.takeD .nat).call, offer := fun _ => (Queue.offerD .nat).call,
    size := fun _ => (Queue.sizeD .nat).call }

/-- A scenario's module over the definitions: its main program and the four definitions. -/
def mkDefs (src : Src NativeOp) : Module NativeOp := { main := src, defs := Queue.defs .nat }

/-- The program of a module that builds. -/
def programOf (m : Module NativeOp) : Option Api.Program :=
  (Effect4.Api.Author.build m).toOption.map (·.program)

/-- The root exit of the ordinary run at a fuel: the root evaluated, then one flush. -/
def exitAt (budget : Nat) (p : Api.Program) : Option ExitV := (Api.run p budget).exit

/-- The least fuel at which the ordinary run has an exit, below 20000: a search by halves. -/
def leastFuel (p : Api.Program) : Nat := Id.run do
  let mut lo := 0
  let mut hi := 20000
  for _ in [0:20] do
    if lo + 1 < hi then
      let mid := (lo + hi) / 2
      if (exitAt mid p).isSome then hi := mid else lo := mid
  return hi

/-- The refusal of a module that does not build, as a word. -/
def refusalOf (m : Module NativeOp) : String :=
  match Effect4.Api.Author.build m with
  | .ok _ => "built"
  | .error (.scope r) => match r.reason with
    | .unboundDef name => "unboundDef " ++ name
    | .duplicateDef name => "duplicateDef " ++ name
    | _ => "scope"
  | .error (.typing r) => "typing: " ++ r.reason.head
  | .error (.admission _) => "admission"
  | .error (.serviceCarrier _ _ _) => "serviceCarrier"

/-! ## Two message types, under two suffixes -/

/-- A queue of numbers and a queue of strings in one program. -/
def twoTypes : Src NativeOp := eff do
  let q ← Queue.bounded .nat 2
  let s ← Queue.bounded .string 2
  let _ ← (Queue.offerD .nat).call q (nat 1)
  let _ ← (Queue.offerD .string "Str").call s (str "a")
  let x ← (Queue.takeD .nat).call q
  let y ← (Queue.takeD .string "Str").call s
  return tuple [x, y]
/-- `take` declared with a Boolean answer, below the body's type. -/
def takeAsBool : Defined (TermSrc → Src NativeOp) :=
  Def.of "queueTake" [("queue", Queue.handleTy .nat)] .bool (Queue.take .nat)

/-- A number offered through the strings' definition. -/
def numberAsString : Src NativeOp := eff do
  let s ← Queue.bounded .string 2
  let a ← (Queue.offerD .string).call s (nat 1)
  return a

end Test.Program.QueueDefs
