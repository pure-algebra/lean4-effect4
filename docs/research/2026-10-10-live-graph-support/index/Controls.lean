import Tools.Graph.Index
import Tools.View.FlowLaws
import Tools.View.FlowSpecimen

set_option autoImplicit false
namespace IndexControls
open Tools.Graph Tools.View Tools.View.Flow

-- Tagged values distinguish parallel occurrences and retain their order.
#guard (Index.ofList Prod.fst [(7, 0), (2, 1), (7, 2), (7, 2)]).bucket 7 =
  [(7, 0), (7, 2), (7, 2)]
#guard (Index.ofList Prod.fst [(1000000000000, 4)]).bucket 1000000000000 =
  [(1000000000000, 4)]
#guard (Index.ofList Prod.fst [(1000000000000, 4)]).bucket 1 = []
#guard (Index.ofList (fun n : Nat => n) []).bucket 0 = []

-- A reader at a real incoming constraint uses the bucket law.
example : (Index.ofList Prod.fst [(7, 0), (2, 1), (7, 2)]).bucket 7 =
    [(7, 0), (7, 2)] := Index.bucket_ofList _ _ _

-- Negative padding, parallel constraints, a self-loop, and an outside position.
def edges : List Edge :=
  [{ fr := 1000000000000, to := 7, pad := -50 },
   { fr := 1, to := 7, pad := -5 }, { fr := 1, to := 7, pad := -5 },
   { fr := 7, to := 7, pad := 2 }, { fr := 7, to := 1000000000000, pad := -20 }]

#guard relaxIndexed (fun _ => -3) (Index.ofList (·.to) edges) (fun _ => -10) (-30) 7 =
  relax (fun _ => -3) edges (fun _ => -10) (-30) 7
#guard relaxIndexed (fun _ => -3) (Index.ofList (·.to) edges) (fun _ => -10) (-30) 99 = -30
#guard (assignHeightsIndexed (fun _ => -3) (Index.ofList (·.to) edges) (-30)
    [1, 7, 7, 1000000000000, 7] [(1, -10), (7, -15)]).map Prod.snd =
  (assignHeights (fun _ => -3) edges (-30)
    [1, 7, 7, 1000000000000, 7] [(1, -10), (7, -15)]).map Prod.snd

-- Raw boxes need no dense position bound for retained assignment.
def outside : Box :=
  { w := 1, items := [pointAt "one" 0], exits := [("fiber", 0)], waits := [(1, "fiber")] }
#guard (preparePlacement outside).height 1 = heightsOf outside 1
#guard (preparePlacement outside).height 1 > outside.topPad
#guard (preparePlacement outside).height 1000000000000 = outside.topPad

-- Original specimen observations include waits, branches, loops, and an empty race.
#guard Tools.View.FlowSpecimen.programs.all fun (_, _, program) =>
  let flow := ofProgram program
  let b := lay flow
  let prepared := preparePlacement b
  (List.range (b.items.length + 3)).all fun i => prepared.height i == heightsOf b i
#guard (acceptWaits 2 [{ fr := 0, to := 1 }] [(1, 0)]).1.length == 1
#guard (acceptWaits 2 [] [(0, 1)]).1.length == 1

end IndexControls
