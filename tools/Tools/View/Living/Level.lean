import Tools.View.Living.Organism
import Whatwg.Svg.Geometry.Monotone

/-!
# Tools.View.Living.Level — the run as one level, and the channels' lives

Two pictures of the whole run, folded from the same markings as the organism
(`Living.Organism`).

**The level.** On one axis: the takers waiting are a deficit below zero, the messages held fill
the vessel up to its brim, and the offers waiting are pressure above the brim. In the Queue's
first profile one signed level decides all three, except while a wake is in flight. Each area's
edge is lean4-whatwg's monotone curve (`Curve.monotoneX`, d3-shape's `curveMonotoneX` after
Steffen, 1990): it passes through every count and never leaves the range of its data
(`Curve.monotoneX_range`), so the level flows without inventing a quantity. A bar line stands at
each command; the units of each frame stand on it, countable.

**The lives of the channels.** Each channel of the organism as a ribbon along the run, as thick
at each beat as the channel is drawn there: its Physarum conductivity's fourth root. A channel
that carries thickens, and an idle one withers; the ribbon's edges are the monotone curve too.
-/

namespace Tools.View.Living.Level
open Tools.View Tools.View.Living
open Whatwg.Svg.Value (Vec Curve)

/-- The picture's room, and its grid: the beats across, a unit of quantity down. -/
def X0 : Int := 120
def DX : Int := 64
def U : Int := 22
def ZERO : Int := 150
def W (n : Nat) : Int := X0 + DX * n + 40

/-- A number in thousandths of a pixel, for a cubic of the view. -/
def milli (r : Rat) : Int := (r * 1000).floor

/-- The package's cubic as the view's, in thousandths. -/
def toView (c : Whatwg.Svg.Value.Cubic) : Cubic :=
  ⟨(milli c.p0.x, milli c.p0.y), (milli c.p1.x, milli c.p1.y), (milli c.p2.x, milli c.p2.y),
   (milli c.p3.x, milli c.p3.y)⟩

/-- A straight segment in thousandths. -/
def line (a b : Int × Int) : Cubic := ⟨a, a, b, b⟩

/-- **The monotone curve through points of the picture**, as the view's cubics. -/
def through (pts : List (Int × Int)) : List Cubic :=
  (Curve.monotoneX (pts.map fun (x, y) => (⟨x, y⟩ : Vec))).map toView

/-- **An area between two edges**, each the monotone curve through its points: the top from the
left, then the bottom back from the right, closed. -/
def area (top bottom : List (Int × Int)) : List Cubic :=
  match top.getLast?, bottom.getLast?, bottom.head?, top.head? with
  | some tr, some br, some bl, some tl =>
    let k (p : Int × Int) : Int × Int := (1000 * p.1, 1000 * p.2)
    through top ++ [line (k tr) (k br)] ++
      (through bottom.reverse) ++ [line (k bl) (k tl)]
  | _, _, _, _ => []

/-- A beat's place across. -/
def xAt (i : Nat) : Int := X0 + DX * i

/-- **The level of the run**: the vessel's band, the bar lines, the three areas, and the units. -/
def level (ms : List Organism.Marking) : List (Keyed Call) :=
  let n := ms.length
  let cap : Int := (ms.head?.map (·.capacity)).getD 0
  let xs := (List.range n).map xAt
  let held := ms.map fun m => (m.held.length : Int)
  let pend := ms.map fun m => (m.offers.length : Int)
  let wait := ms.map fun m => (m.takers.length : Int)
  let brim := ZERO - U * cap
  let at_ (vs : List Int) (f : Int → Int) : List (Int × Int) := xs.zip (vs.map f)
  let band : Keyed Call := ⟨"vessel", .shape .ink 50 [Grow.roundRect (1000 * (X0 - 24)) (1000 * brim)
      (1000 * (DX * (n - 1) + 48)) (1000 * (ZERO - brim)) 12000]⟩
  let bars := xs.map fun x => (⟨"beat", Call.vrule .rule x (brim - 3 * U) (6 * U + U * cap) 1⟩ : Keyed Call)
  let flat (y : Int) : List (Int × Int) := xs.map (·, y)
  let areas : List (Keyed Call) :=
    [⟨"held", .shape .ink 260 [area (at_ held fun h => ZERO - U * h) (flat ZERO)]⟩,
     ⟨"pressure", .shape .ink 140 [area (at_ pend fun p => brim - U * p) (flat brim)]⟩,
     ⟨"deficit", .shape .ink 140 [area (flat ZERO) (at_ wait fun w => ZERO + U * w)]⟩]
  let unitsAt (i : Nat) (m : Organism.Marking) : List (Keyed Call) :=
    let x := xAt i
    ((List.range m.held.length).map fun (k : Nat) =>
      (⟨s!"held/{i}/{k}", .shape .ink 1000 [Organism.disc x (ZERO - U * k - U / 2) 5]⟩ : Keyed Call)) ++
    ((List.range m.offers.length).map fun (k : Nat) =>
      ⟨s!"offer/{i}/{k}", .shape .ink 900 (Grow.ring (1000 * (x - 6)) (1000 * (brim - U * k - U / 2 - 6)) 12000 12000 3000 1100)⟩) ++
    ((List.range m.takers.length).map fun (k : Nat) =>
      ⟨s!"taker/{i}/{k}", .shape .ink 900 (Grow.ring (1000 * (x - 6)) (1000 * (ZERO + U * k + U / 2 - 6)) 12000 12000 3000 1100)⟩)
  let labels : List (Keyed Call) :=
    [⟨"pressure", .text .label 8 (brim - U / 2 + 4) 90 "pressure"⟩,
     ⟨"held", .text .label 8 (ZERO - U * cap / 2 + 4) 90 "held"⟩,
     ⟨"deficit", .text .label 8 (ZERO + U / 2 + 4) 90 "deficit"⟩]
  band :: bars ++ areas ++ (ms.zipIdx.flatMap fun (m, i) => unitsAt i m) ++ labels

/-- The height of the level's picture. -/
def LEVEL_H : Int := ZERO + 3 * U + 10

/-- **The lives of the channels**: each channel a ribbon along the run, as thick at each beat as
the organism draws it. -/
def lives (ds : List (List Nat)) : List (Keyed Call) :=
  let names := ["in", "enter", "leave", "out"]
  let n := ds.length
  let xs := (List.range n).map xAt
  (List.range Organism.CHANNELS).flatMap fun (k : Nat) =>
    let y0 : Int := 26 + 34 * k
    let half := ds.map fun d => ((Organism.channelR (d.getD k 0) : Int) * 1000 / 1600 + 1)
    let top := xs.zip (half.map (y0 - ·))
    let bottom := xs.zip (half.map (y0 + ·))
    [(⟨s!"channel/{k}", .shape .ink 420 [area top bottom]⟩ : Keyed Call),
     ⟨s!"channel/{k}", .text .label 8 (y0 + 4) 90 (names.getD k "")⟩]

/-- The height of the lives' picture. -/
def LIVES_H : Int := 26 + 34 * Organism.CHANNELS

end Tools.View.Living.Level
