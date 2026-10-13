import Tools.View.Organic

/-!
# Tools.View.Living.Phyllotaxis — units in a round place, as a sunflower packs its florets

Vogel's model of the sunflower head ("A better way to construct the sunflower head",
*Mathematical Biosciences* 44:179–189, 1979; MathWorld, "Vogel Spiral"): the `k`-th floret
stands at the angle `k φ` and the radius `c √k`, where `φ` is the golden angle, about 137.5°.
Each floret then has the same share of the area, so a disc of radius `c √n` holds `n` of them,
and the golden angle packs them densest. A round place draws its units so: a Semaphore's
permits, a Pool's items, a queue above a capacity of eight (Gemini's review, question 2).

**The golden angle as an exact rotation.** `φ / 2` has `tan(φ/2) ≈ 0.38881`, whose continued
fraction `[0; 2, 1, 1, 2, 1, 39, …]` has the convergent `7/18`. The rotation by twice
`atan(7/18)` is the Pythagorean one `(275, 252) / 373`, since `275² + 252² = 373²`; turned past
half a turn it is `(−275, 252) / 373`, the angle `137.499…°`, within a hundredth of a degree of
the golden angle. A rotation by a Pythagorean triple keeps every length exactly
(`turn_norm`), so no point drifts off its circle however many times it turns.

**Age.** In a sunflower head the florets form at the rim of the growing zone and move inward, so
the youngest stand nearest the centre: `k` counts from the newest unit. A queue's newest message
stands at the centre and its front at the rim, from where it leaves; an offer grows the spiral
from the centre, as the head grows.

**The spacing is a law, not a choice.** `spacing` is the least spacing, in whole thousandths of a
pixel, for which no two units stand closer than their diameter and the cell-free layer between
them (`apart`, decided). The place's radius is the farthest unit's radius, the unit's own, and
the layer (`radius`): its area grows with its capacity, so a reader reads the capacity from its
size.

**Many units.** Above `MAX_MARKS` units a mark stands for several (`perMark`), as Neurath's
Isotype draws one figure for a round number of things.
-/

namespace Tools.View.Living.Phyllotaxis
open Tools.View

/-- The golden turn: the Pythagorean rotation `(−275, 252) / 373`. -/
def TURN_C : Int := -275
def TURN_S : Int := 252
def TURN_H : Int := 373

/-- A direction, in whole units at a scale. -/
structure Dir where
  x : Int
  y : Int
deriving Repr, DecidableEq

/-- **The golden turn of a direction**, unscaled: the rotation's integer matrix. -/
def Dir.turn (d : Dir) : Dir := ⟨TURN_C * d.x - TURN_S * d.y, TURN_S * d.x + TURN_C * d.y⟩

/-- A direction's square length. -/
def Dir.norm2 (d : Dir) : Int := d.x * d.x + d.y * d.y

/-- **The golden turn keeps every length**: its integer matrix multiplies a square length by
`373²`, so the rotation itself, divided by `373`, keeps it exactly. -/
theorem turn_norm (d : Dir) : d.turn.norm2 = TURN_H * TURN_H * d.norm2 := by
  simp only [Dir.turn, Dir.norm2, TURN_C, TURN_S, TURN_H]
  grind

/-- The scale of a direction: a million. -/
def UNIT : Int := 1000000

/-- The directions of the first `n` units, from the newest: the golden turn applied `k` times to
the direction across, renormalised to `UNIT` each time (the exact turn keeps the length; the
rounding of the division is the only loss). -/
def directions (n : Nat) : List Dir :=
  (List.range n).foldl (fun (d, out) _ =>
    let t := d.turn
    (⟨t.x / TURN_H, t.y / TURN_H⟩, out ++ [d])) ((⟨UNIT, 0⟩ : Dir), ([] : List Dir)) |>.2

/-- **The place of the `k`-th unit from the newest**, in thousandths of a pixel about the centre:
the radius `c √(k + 1/2)` along its direction. The half keeps the newest off the centre itself,
as Vogel's centred variant does. -/
def placeOf (c : Nat) (k : Nat) (d : Dir) : Int × Int :=
  let r : Int := (c : Int) * (Grow.isqrt (1000000 * k + 500000) : Int) / 1000
  (r * d.x / UNIT, r * d.y / UNIT)

/-- The places of `n` units at the spacing `c`. -/
def places (c n : Nat) : List (Int × Int) := ((directions n).zipIdx).map fun (d, k) => placeOf c k d

/-- The square distance between two places. -/
def dist2 (a b : Int × Int) : Int := (a.1 - b.1) * (a.1 - b.1) + (a.2 - b.2) * (a.2 - b.2)

/-- **No two units closer than `gap`** (thousandths of a pixel, centre to centre), decided. -/
def apart (gap : Int) (ps : List (Int × Int)) : Bool :=
  ps.zipIdx.all fun (p, i) => (ps.drop (i + 1)).all fun q => dist2 p q ≥ gap * gap

/-- **The least spacing that keeps `n` units apart**, searched upward in whole thousandths of a
pixel from the gap's half, a tenth of a pixel at a time. -/
def spacing (gap : Nat) (n : Nat) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, c => c
    | fuel + 1, c => if apart gap (places c n) then c else go fuel (c + 100)
  go 400 (gap / 2)

/-- **The radius of a round place** holding `n` units of radius `unit` with the layer `layer`
around each (thousandths of a pixel): its farthest unit, the unit, and the layer. -/
def radius (c n unit layer : Nat) : Nat :=
  c * Grow.isqrt (1000000 * (n - 1) + 500000) / 1000 + unit + layer

/-- The most marks a round place draws; above it a mark stands for several units. -/
def MAX_MARKS : Nat := 89

/-- **How many units a mark stands for**: one up to `MAX_MARKS`, then the least whole number
that brings the marks within it. -/
def perMark (n : Nat) : Nat := if n ≤ MAX_MARKS then 1 else (n + MAX_MARKS - 1) / MAX_MARKS

-- the turn's triple
#guard TURN_C * TURN_C + TURN_S * TURN_S == TURN_H * TURN_H
-- thirteen units of radius 9 with a layer of 4 keep apart at the spacing found, and not a tenth
-- of a pixel less
#guard apart 26000 (places (spacing 26000 13) 13)
#guard !apart 26000 (places (spacing 26000 13 - 100) 13)

end Tools.View.Living.Phyllotaxis
