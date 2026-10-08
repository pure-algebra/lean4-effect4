import Test.Program.QueueScenarios
import Effect4.Modules.Queue.Defs

/-!
# The Queue's operations as definitions (decisions row 328, slice PROC-4)

The eight scenarios of `Test/Program/QueueScenarios.lean`, written over the Queue's definitions
(`src/Effect4/Modules/Queue/Defs.lean`): each operation is declared once in the module's
block, by `Def.of`, and each site is one invocation. The scenarios do not change: they take the
operations as a record (`Ops`), and the invocations have the operations' own types.

What is measured here, at the lane's fuel and on one schedule each:

- each scenario builds, and its exit is the exit over the inline operations;
- the least fuel of each run, over either form: each invocation is one more step;
- the printed module: each definition once, and each use one call.

None of these is a theorem. That an invocation and its inlining have one observation is goal G7
of the procedures note, under decisions row 329's relation; these runs are finite controls of
it. The controls show each refusal of the surface: an undeclared name, a name declared twice, a
declared row below the body's type, and a message of the wrong type.
-/

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

/-! ## The scenarios over the definitions (finite evaluations) -/

-- Each scenario builds, with the block at its root: the four definitions in their order.
#guard (scenariosWith invoked).all fun s => (programOf (mkDefs s)).isSome
#guard (programOf (mkDefs (r1With invoked))).map (fun p => p.defsOf.map (·.name)) =
  some ["queueTake", "queueOffer", "queuePoll", "queueSize"]
-- Each scenario's exit at the lane's fuel is its exit over the inline operations.
#guard (List.zip (scenariosWith invoked) (scenariosWith library)).all fun (d, l) =>
  let defined := (programOf (mkDefs d)).bind (exitAt 1000)
  defined.isSome && decide (defined = (programOf (mk l)).bind (exitAt 1000))
-- Red control of the comparison: the two forms are two trees in each scenario.
#guard (List.zip (scenariosWith invoked) (scenariosWith library)).all fun (d, l) =>
  (programOf (mkDefs d)).map Api.bytesOf != (programOf (mk l)).map Api.bytesOf

/-! ## The least fuel, measured again (finite evaluations) -/

-- Over the inline operations, the eight scenarios R1 to R8.
#guard (scenariosWith library).map (fun s => (programOf (mk s)).map leastFuel) =
  [some 119, some 73, some 138, some 98, some 133, some 131, some 75, some 151]
-- Over the definitions: one more step for each invocation that a run reaches.
#guard (scenariosWith invoked).map (fun s => (programOf (mkDefs s)).map leastFuel) =
  [some 123, some 75, some 142, some 101, some 136, some 135, some 76, some 155]

/-! ## The printed module (finite evaluations) -/

-- R1's module: the four definitions, each once, then the main declaration.
#guard (programOf (mkDefs (r1With invoked))).bind (fun p =>
  (Api.printModule "main" p).map fun m => m.decls.length) = some 5
-- R1 uses each of `offer` and `take` twice: its module over the definitions prints shorter than
-- its module over the inline operations.
#guard match (programOf (mkDefs (r1With invoked))).bind (fun p => (Api.printModule "main" p).map
    fun m => (String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))).length),
  (programOf (mk (r1With library))).bind (fun p => (Api.printModule "main" p).map
    fun m => (String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))).length) with
  | some defined, some inline => decide (defined < inline)
  | _, _ => false
-- A main declaration over the definitions holds no step of the Queue: no `Ref.modify` in it.
#guard (programOf (mkDefs (r1With invoked))).bind (fun p => (Api.printModule "main" p).bind
  fun m => m.decls.getLast?.map fun d =>
    ((TypeScript.Render.decl TypeScript.house0 d).splitOn "Ref.modify").length) = some 1

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

#guard (programOf { main := twoTypes, defs := Queue.defs .nat ++ Queue.defs .string "Str" }).bind
    (exitAt 1000) = some (.success (.list [.nat 1, .str "a"]))

/-! ## Controls: what the surface and the checker refuse -/

-- An invocation of an undeclared definition refuses at its site, by name.
#guard refusalOf (mk (r1With invoked)) = "unboundDef queueOffer"
-- Two definitions under one name.
#guard refusalOf { main := r1With invoked, defs := Queue.defs .nat ++ Queue.defs .nat } =
  "duplicateDef queueTake"
/-- `take` declared with a Boolean answer, below the body's type. -/
def takeAsBool : Defined (TermSrc → Src NativeOp) :=
  Def.of "queueTake" [("queue", Queue.handleTy .nat)] .bool (Queue.take .nat)

/-- A number offered through the strings' definition. -/
def numberAsString : Src NativeOp := eff do
  let s ← Queue.bounded .string 2
  let a ← (Queue.offerD .string).call s (nat 1)
  return a

-- A declared answer below the body's type: the checker refuses the body against its row.
#guard refusalOf { main := takeAsBool.call (nat 0), defs := [takeAsBool.src] } =
  "typing: bodyNotDeclared"
-- A number offered through the strings' definition does not build.
#guard refusalOf { main := numberAsString, defs := Queue.defs .string } != "built"

end Test.Program.QueueDefs
