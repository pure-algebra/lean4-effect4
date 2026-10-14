import Tools.View.Motion
import Tools.View.GraphCheck
import Tools.View.SvgOut
import Tools.View.Tokens

/-! Rendered finite controls for graph service contracts, before aesthetic changes. -/

open Tools.View

private def linear : Choreography :=
  { move := { duration := 1000, ease := .linear } }

private def fork (y : Int) : Laid :=
  { placed := #[
      { key := "op/fork/0", x := 32, y, w := 16 },
      { key := "op/fork/1", x := 152, y, w := 16 },
      { key := "a", x := 8, y := y + 100, w := 72,
        node := some { key := "a", line1 := "left" } },
      { key := "b", x := 128, y := y + 100, w := 72,
        node := some { key := "b", line1 := "right" } }],
    marks := #[.bar "op/fork" 24 176 y],
    routes := #[.down "op/fork/0→a" ["op/fork/0", "a"],
      .down "op/fork/1→b" ["op/fork/1", "b"]], width := 220, height := 280 }

private def boxes (swapped : Bool) : Laid :=
  { placed := #[
      { key := "a", x := if swapped then 128 else 8, y := 80, w := 72,
        node := some { key := "a", line1 := "alpha" } },
      { key := "b", x := if swapped then 8 else 128, y := 80, w := 72,
        node := some { key := "b", line1 := "beta" } }], width := 220, height := 160 }

private def loopGraph : Graph :=
  { nodes := #[⟨"loop-node", "loop", "", false⟩], edges := #[⟨"loop-edge", 0, 0⟩] }

#guard (fork 40).placed.toList.filter (·.node.isNone) |>.all ((fork 40).onBar ·)
#guard (fork 120).placed.toList.filter (·.node.isNone) |>.all ((fork 120).onBar ·)
#guard let mid := sampleLaid linear (fork 40) (fork 120) 500
  !(mid.placed.toList.filter (·.node.isNone) |>.any (mid.onBar ·))
#guard (boxes false).boxesApart && (boxes true).boxesApart
#guard !(sampleLaid linear (boxes false) (boxes true) 500).boxesApart
#guard (GraphCheck.laid loopGraph.layout).isOk

private def write (out : System.FilePath) (L : Look) (name : String) (laid : Laid) : IO Unit := do
  let calls := [⟨"ground", .fill .ground 1000 0 0 300 340⟩] ++ laid.calls L 24 24 ++
    [⟨"allocation", .frame .failure 24 24 laid.width laid.height 1⟩]
  match SvgOut.fileText (SvgOut.picture L 300 340 1 (lowerAll 1 calls)) with
  | .error why => throw (IO.userError why)
  | .ok svg => IO.FS.writeFile (out / s!"{name}.svg") svg

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "tools/view/out/graph-contracts"
  IO.FS.createDirAll out
  let L : Look := { hue := true }
  IO.FS.writeFile (out / "look.css") (Tokens.css L ++ Tokens.rules)
  for t in [0, 250, 500, 750, 1000] do
    write out L s!"fork-{t}" (sampleLaid linear (fork 40) (fork 120) t)
    write out L s!"swap-{t}" (sampleLaid linear (boxes false) (boxes true) t)
  write out L "loop" loopGraph.layout
  IO.println "graph-contracts: moving bar docking, swapping box overlap, and loop canvas controls pass"
