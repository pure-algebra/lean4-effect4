import Tools.View.Flow

/-! Independent pre-change placement policies, retained before their consumers move. -/
namespace GraphToolsProbe.Baseline
open Tools.View Tools.View.Flow

def reaches (es : List Edge) : Nat → List Nat → List Nat → Nat → Bool
  | 0, _, _, _ => false
  | fuel + 1, frontier, seen, u =>
    if frontier.contains u then true else
    let next := (es.filterMap fun e => if frontier.contains e.fr && !seen.contains e.to then some e.to else none).eraseDups
    if next.isEmpty then false else reaches es fuel next (seen ++ next) u

def heightsOf (b : Box) : Nat → Int :=
  let o := orderFor b.items.length b.edges (acceptWaits b.items.length b.edges b.waitEdges).1
  assign (hAt b.items) o.1 b.topPad o.2 fun _ => b.topPad

def placeWith (width : GNode → Int) (f : Flow) : Placement :=
  let b := layWith width f
  let y := heightsOf b
  { box := b, placed := atHeights y 0 b.items,
    lanes := b.backs ++ (acceptWaits b.items.length b.edges b.waitEdges).2 }
end GraphToolsProbe.Baseline
