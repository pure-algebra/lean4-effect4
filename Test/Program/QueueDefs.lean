import Test.Program.QueueDefsData
import Test.Program.QueueScenarios
import Effect4.Library.Queue.Defs
import Effect4.Api.Codegen

/-!
# The Queue's operations as definitions (decisions row 328, slice PROC-4)

The eight scenarios of `Test/Program/QueueScenarios.lean`, written over the Queue's definitions
(`src/Effect4/Library/Queue/Defs.lean`): each operation is declared once in the module's
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

#guard (programOf { main := twoTypes, defs := Queue.defs .nat ++ Queue.defs .string "Str" }).bind
    (exitAt 1000) = some (.success (.list [.nat 1, .str "a"]))

/-! ## Controls: what the surface and the checker refuse -/

-- An invocation of an undeclared definition refuses at its site, by name.
#guard refusalOf (mk (r1With invoked)) = "unboundDef queueOffer"
-- Two definitions under one name.
#guard refusalOf { main := r1With invoked, defs := Queue.defs .nat ++ Queue.defs .nat } =
  "duplicateDef queueTake"

-- A declared answer below the body's type: the checker refuses the body against its row.
#guard refusalOf { main := takeAsBool.call (nat 0), defs := [takeAsBool.src] } =
  "typing: bodyNotDeclared"
-- A number offered through the strings' definition does not build.
#guard refusalOf { main := numberAsString, defs := Queue.defs .string } != "built"

end Test.Program.QueueDefs
