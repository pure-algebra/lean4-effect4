import Tools.View.Page

/-!
# Motion between two frames, from the laws

Slice V3 of the visual pipeline (`docs/research/2026-10-09-visual-pipeline.md`). Three facts make
a transition between two frames, and the module adds no rule of its own:

- **What changes** is the session's: an edit that splices its table repaints only its subtree
  (`EditSession.feed_repaint`, `Sketch.table_fill`). So every line outside the edited subtree
  keeps its key, its text and its type. `keptUnchanged` checks this on each pair of frames.
- **Who is who** is the key's: each device call carries the key of its call (`lower_key`), and a
  line's key is its address.
- **Where it is drawn** is exact at every step: a call moved by whole pixels lowers to its device
  calls, moved (`lowerCall_move`, and `lower_move` below for a keyed call).

So a transition is: each line that both frames hold moves from its old row to its new one; a
line of the new frame alone enters at the end; a line of the old frame alone has left. The
step is linear in whole pixels. Which motion a person sees, and how fast, is the owner's to walk
(decisions row 336; the plan's slice V3): this is the plainest one the laws give.
-/

namespace Tools.View

/-- A keyed call moved by whole logical pixels. -/
def Keyed.move (dx dy : Int) (c : Keyed Call) : Keyed Call := ⟨c.key, c.call.move dx dy⟩

/-- A keyed device call moved by whole logical pixels at the ratio `r`. -/
def Keyed.moveDev (r dx dy : Int) (d : Keyed Dev) : Keyed Dev := ⟨d.key, d.call.move r dx dy⟩

/-- **The move law, keyed.** A keyed call moved by whole logical pixels lowers to its device
calls, moved, each with the call's key. -/
theorem lower_move (r dx dy : Int) (c : Keyed Call) :
    lower r (c.move dx dy) = (lower r c).map (Keyed.moveDev r dx dy) := by
  simp only [lower, Keyed.move, lowerCall_move, List.map_map]
  rfl

/-- A list of keyed calls moved alike lowers to its device calls, moved. -/
theorem lowerAll_move (r dx dy : Int) (cs : List (Keyed Call)) :
    lowerAll r (cs.map (Keyed.move dx dy)) = (lowerAll r cs).map (Keyed.moveDev r dx dy) := by
  simp only [lowerAll, List.flatMap_map, List.map_flatMap, lower_move]

/-- The row of the line with key `k`. -/
def rowOf (g : Page) (k : Key) : Option Nat := g.lines.toList.findIdx? (·.key == k)

/-- The frame at step `t` of `n` between `g1` and `g2`: the ground and the title block of `g2`;
each line of `g2` that `g1` holds, moved from its row in `g1` toward its row in `g2`; each line
of `g2` alone, only at the last step. Its height is the taller page's. At step `n` its lines are
`g2`'s, at their rows. -/
def tween (W : Int) (g1 g2 : Page) (t n : Nat) : List (Keyed Call) :=
  let H := max (pageSize W g1).2 (pageSize W g2).2
  let B := gutterCols g2
  let lineAt (l : Line) (i : Nat) : List (Keyed Call) :=
    match rowOf g1 l.key with
    | some i1 =>
      let dy : Int := (ROWH * ((i1 : Int) - i) * ((n : Int) - t)) / (n : Int)
      (lineCalls W B i l).map (Keyed.move 0 dy)
    | none => if t < n then [] else lineCalls W B i l
  groundCalls W H ++ (g2.lines.toList.zipIdx.flatMap fun (l, i) => lineAt l i) ++ chromeCalls W H g2

/-- The size of the frames between `g1` and `g2`. -/
def tweenSize (W : Int) (g1 g2 : Page) : Int × Int := (W, max (pageSize W g1).2 (pageSize W g2).2)

/-- The key `k` lies in the subtree whose root has the key `a`, both written as `[1 0]`: it is
`a`, or it extends `a`'s address. The root `[]` holds every key. -/
def underKey (a k : Key) : Bool :=
  a == "[]" || k == a || k.startsWith ((a.dropEnd 1).toString ++ " ")

/-- The splice, read on two frames: the lines that both frames hold outside the subtree at
`edited`, and how many of them keep their text, their type and their note. -/
def keptUnchanged (g1 g2 : Page) (edited : Key) : Nat × Nat :=
  let outside (l : Line) : Bool := !(underKey edited l.key)
  let pairs := g2.lines.toList.filterMap fun l2 =>
    if outside l2 then (g1.lines.toList.find? (·.key == l2.key)).map (·, l2) else none
  (pairs.length, (pairs.filter fun (l1, l2) =>
    l1.text == l2.text && l1.type == l2.type && l1.note == l2.note).length)

end Tools.View
