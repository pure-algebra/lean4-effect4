import Tools.View.Build

/-!
# Probe: is an organic stroke equivariant under a move by whole pixels?

`Grow.stroke` on moved segments against the stroke moved, over a grid of segments, moves and
seeds. The input is in logical pixels; the stroke is in thousandths, so a move of `d` is `1000 d` there.
-/

open Tools.View

def moveC (dx dy : Int) (c : Cubic) : Cubic := c.move dx dy

def cubicsAt (i : Nat) : List Cubic :=
  let a : Int := (i * 37 % 200 : Nat)
  let b : Int := (i * 53 % 300 : Nat)
  [⟨(a, b), (a, b + 40), (a + 60, b + 50), (a + 60, b + 96)⟩,
   ⟨(a + 60, b + 96), (a + 60, b + 120), (a + 10, b + 130), (a + 10, b + 180)⟩]

#eval
  let o : Organic := {}
  let cases := (List.range 40).flatMap fun i => [(i, 8, -3), (i, -16, 24), (i, 1, 1), (i, 333, -777)]
  let bad := cases.filter fun (i, dx, dy) =>
    let cs := cubicsAt i
    (Grow.stroke (Grow.seedOf s!"k{i}") o 3000 (cs.map (moveC dx dy)) (i % 2 == 0)) !=
      (Grow.stroke (Grow.seedOf s!"k{i}") o 3000 cs (i % 2 == 0)).map (moveC (1000 * dx) (1000 * dy))
  (cases.length, bad.length)
