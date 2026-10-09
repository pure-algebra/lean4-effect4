import Tools.View.FlowSpecimen
import Lean.Data.Json

open Lean (Json toJson)
open Tools.View Tools.View.Flow

namespace LayoutReview

def leaf (key : String) : Flow := .node key key ""
def unique : Flow := .seq [leaf "a", leaf "b"]
def duplicate : Flow := .seq [leaf "same", leaf "same"]
def sampleWait : Flow := ofProgram (FlowSpecimen.programs[1].2.2)
def cyclicWait : Flow := .seq [.node "wait" "wait" "" ["fiber"], .par .spawn "fiber" [leaf "end"]]

def orderPasses (f : Flow) : Bool :=
  let b := lay f
  let dag := (acceptWaits b.items.length b.edges b.waitEdges).1
  orders (kahn b.items.length dag) dag

def waitsMeet (f : Flow) : Bool :=
  let b := lay f
  let y := heightsOf b
  b.waitEdges.all fun (source, target) => y source + hAt b.items source + VGAP ≤ y target

def lookupMatches (f : Flow) : Bool :=
  let result := layout f
  result.placed.toList.all fun p =>
    match result.find p.key with
    | none => false
    | some q => p.x == q.x && p.y == q.y && p.w == q.w

def row (name : String) (actual expected : Json) := (name, actual, expected)

def checks : List (String × Json × Json) :=
  [row "unique-keys-lookup" (toJson (lookupMatches unique)) (toJson true),
   row "duplicate-keys-lookup" (toJson (lookupMatches duplicate)) (toJson false),
   row "unique-keys-rendered-edges-descend" (toJson (layout unique).edgesDescend) (toJson true),
   row "duplicate-keys-rendered-edges-descend" (toJson (layout duplicate).edgesDescend) (toJson false),
   row "duplicate-keys-boxes-still-apart" (toJson (layout duplicate).boxesApart) (toJson true),
   row "zero-width-admitted-premise" (toJson (decide ((layWith (fun _ => 0) unique).w = 0))) (toJson true),
   row "negative-width-outside-premise" (toJson (decide ((layWith (fun _ => -1) (leaf "negative")).w < 0))) (toJson true),
   row "sample-cross-wait-present" (toJson (!(lay sampleWait).waitEdges.isEmpty)) (toJson true),
   row "sample-cross-wait-order-accepted" (toJson (orderPasses sampleWait)) (toJson true),
   row "sample-cross-wait-height-met" (toJson (waitsMeet sampleWait)) (toJson true),
   row "cycle-wait-present" (toJson (!(lay cyclicWait).waitEdges.isEmpty)) (toJson true),
   row "cycle-wait-retained-as-lane" (toJson (!(place cyclicWait).lanes.isEmpty)) (toJson true),
   row "cycle-wait-does-not-constrain-height" (toJson (waitsMeet cyclicWait)) (toJson false),
   row "cycle-own-edges-descend" (toJson (layout cyclicWait).edgesDescend) (toJson true),
   row "empty-layout-dimensions" (toJson (layout (.seq [])).dimsValid) (toJson true),
   row "parallel-edge-counts"
     (toJson ([1, 2, 4, 8, 16].map fun n =>
       (n, (lay (.par .fork "p" ((List.range n).map fun i => leaf (toString i)))).edges.length)))
     (toJson [(1, 5), (2, 12), (4, 32), (8, 96), (16, 320)])]

end LayoutReview

def main : IO Unit := do
  let rows := LayoutReview.checks.map fun (name, actual, expected) =>
    Json.mkObj [("name", .str name), ("actual", actual), ("expected", expected), ("pass", .bool (actual == expected))]
  IO.println (Json.arr rows.toArray).compress
  unless LayoutReview.checks.all (fun (_, actual, expected) => actual == expected) do
    throw (IO.userError "Layout review control failed")
