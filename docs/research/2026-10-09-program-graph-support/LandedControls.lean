import Tools.View.Flow
import Effect4.Api.Author

/-! Finite controls of the landed Flow at 78f7bcbe.
They read the real draft. No alternative program or layout implementation is defined.
-/

open Effect4 Effect4.Program Effect4.Machine Tools.View
open Tools.View.Flow

namespace ProgramGraphSupportFlow

def value (n : Nat) : NativeEff := .succeed (.lit (.nat n))
def mark (n : Nat) (next : NativeEff) : NativeEff :=
  .bind (.perform .refMake (.lit (.nat n))) next

def child : NativeEff := .withFiber (.fork (value 7) ⟨true, false, .inherit⟩)

structure BindingCase where
  name : String
  program : NativeEff
  expected : List (List Nat × List Nat)

def bindingCases : List BindingCase :=
  [⟨"single-binder", .bind child (.awaitFiber (.var 0) .joinEffect), [([1], [0, 0])]⟩,
   ⟨"first-of-two-fibers", .bind child (.bind child (.awaitFiber (.var 0) .joinEffect)),
      [([1, 1], [0, 0])]⟩,
   ⟨"second-of-two-fibers", .bind child (.bind child (.awaitFiber (.var 1) .joinEffect)),
      [([1, 1], [1, 0, 0])]⟩,
   ⟨"unrelated-newer-value", .bind child
      (.bind (.perform .refMake (.lit (.nat 1))) (.awaitFiber (.var 0) .joinEffect)),
      [([1, 1], [0, 0])]⟩,
   ⟨"closed-layer-resets-bindings", .bind child
      (.provideLayer (.effectDiscard (.bind child (.awaitFiber (.var 0) .joinEffect)))
        false (value 2)), [([1, 0, 0, 1], [1, 0, 0, 0, 0])]⟩,
   ⟨"generator-bindings", .gen (.cons (.bindYield child)
      (.cons (.bindYield (.perform .refMake (.lit (.nat 1))))
        (.cons (.yieldDiscard (.awaitFiber (.var 0) .joinEffect))
          (.cons (.ret (.lit .unit)) .nil)))),
      [([0, 1, 1, 0, 0], [0, 0, 0, 0])]⟩,
   ⟨"release-has-two-binders", .scoped (.bind child
      (.acquireRelease (value 1) (.bind child
        (.bind (.awaitFiber (.var 0) .joinEffect) (.awaitFiber (.var 3) .joinEffect))))),
      [([0, 1, 1, 1, 0], [0, 0, 0]), ([0, 1, 1, 1, 1], [0, 1, 1, 0, 0])]⟩,
   ⟨"alias-is-outside-direct-spawn-reading",
      .bind child (.bind (.succeed (.var 0)) (.awaitFiber (.var 1) .joinEffect)), []⟩]

def expectedKeys (c : BindingCase) : List (Key × Key) :=
  c.expected.map fun (a, f) => (Tools.View.Program.bracket a, Tools.View.Program.bracket f)

def checkBinding (c : BindingCase) : IO Lean.Json := do
  match Api.Author.Internal.finishBuild c.program [] [] with
  | .error _ => throw (IO.userError s!"{c.name}: program admission refused")
  | .ok _ => pure ()
  let actual := (waits c.program).flatMap fun (a, fs) => fs.map fun f => (a, f)
  let expected := expectedKeys c
  pure (Lean.Json.mkObj [
    ("name", Lean.toJson c.name), ("admitted", .bool true),
    ("actual", Lean.toJson actual), ("expected", Lean.toJson expected),
    ("matches", Lean.toJson (actual == expected))])

def projectedTarget : Term :=
  .tupleAt (.app "tuple" (.cons (.var 0) (.cons (.var 1) .nil))) 0

def projectedWait : BindingCase :=
  ⟨"tuple-projection-waits-for-first-fiber-only",
    .bind child (.bind child (.awaitFiber projectedTarget .joinEffect)), [([1, 1], [0, 0])]⟩

def scopedRelease : NativeEff :=
  .scoped (.bind (.acquireRelease (mark 10 (value 1)) (mark 30 (value 3)))
    (mark 20 (value 2)))

def boxJson (b : Laid) : Lean.Json := Lean.Json.mkObj [
  ("width", Lean.toJson b.width), ("height", Lean.toJson b.height),
  ("routes", Lean.toJson (b.routes.toList.map fun r => reprStr r)),
  ("marks", Lean.toJson (reprStr b.marks.toList)),
  ("boxesApart", Lean.toJson b.boxesApart), ("edgesDescend", Lean.toJson b.edgesDescend),
  ("nodes", Lean.toJson (b.placed.toList.filterMap fun p => p.node.map fun n =>
    Lean.Json.mkObj [("key", Lean.toJson p.key), ("text", Lean.toJson n.line1),
      ("x", Lean.toJson p.x), ("y", Lean.toJson p.y)]))]

def choice : Flow := .par .choice "control" [.node "left" "left" "", .node "right" "right" ""]
def parallel : Flow := .par .fork "control" [.node "left" "left" "", .node "right" "right" ""]

end ProgramGraphSupportFlow

def main (args : List String) : IO Unit := do
  let rows ← ProgramGraphSupportFlow.bindingCases.mapM ProgramGraphSupportFlow.checkBinding
  let allMatch := ProgramGraphSupportFlow.bindingCases.all fun c =>
    (waits c.program).flatMap (fun (a, fs) => fs.map fun f => (a, f)) == ProgramGraphSupportFlow.expectedKeys c
  let cleanup := layout (ofProgram ProgramGraphSupportFlow.scopedRelease)
  let emptyRace : NativeEff := .withFiber (.raceAll .nil)
  let empty := layout (ofProgram emptyRace)
  let choice := ProgramGraphSupportFlow.boxJson (layout ProgramGraphSupportFlow.choice)
  let parallel := ProgramGraphSupportFlow.boxJson (layout ProgramGraphSupportFlow.parallel)
  let spawn := ProgramGraphSupportFlow.boxJson (layout (.par .spawn "spawn-control"
    [.node "parent" "parent" "", .node "child" "child" ""]))
  let projection ← ProgramGraphSupportFlow.checkBinding ProgramGraphSupportFlow.projectedWait
  let selected := evalTerm [Val.fiber ⟨1⟩, Val.fiber ⟨2⟩] ProgramGraphSupportFlow.projectedTarget
  if selected != some (Val.fiber ⟨1⟩) then
    throw (IO.userError "Tuple projection did not select the first fiber")
  IO.println (Lean.Json.mkObj [
    ("reviewedCommit", Lean.toJson "78f7bcbe"),
    ("spawn", spawn), ("projection", projection), ("projectionSelectedFiber", Lean.toJson (1 : Nat)),
    ("bindingCount", Lean.toJson rows.length), ("bindings", Lean.toJson rows),
    ("allBindingsMatch", Lean.toJson allMatch),
    ("scopedRelease", ProgramGraphSupportFlow.boxJson cleanup),
    ("emptyRace", ProgramGraphSupportFlow.boxJson empty),
    ("choiceAndParallelHaveIdenticalGeometry", Lean.toJson (choice.compress == parallel.compress))]).compress
  if args.contains "--require-bindings" && !allMatch then
    throw (IO.userError "Binding-origin controls failed")
