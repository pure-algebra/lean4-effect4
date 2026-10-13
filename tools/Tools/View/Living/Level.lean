import Tools.View.Living.Organism
import Whatwg.Svg.Geometry.Monotone
import Whatwg.Svg.Scene.Scale
import Whatwg.Svg.Scene.Scale.Band

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

/-- **The picture's room**, whatever the run: a run of any length and any capacity is fitted to
it by two of lean4-whatwg's scales (ask W16): the beats across by a point scale (`Band.point`),
the counts down by a linear scale that falls down the screen (`Scale.linear`), from the most
takers that wait to the capacity and the most offers that wait above it. -/
def LW : Int := 880
def LH : Int := 230
def LEFT : Int := 96
def PADY : Int := 18

/-- The beats across: one point for each frame of the run. -/
def beatsOf (n : Nat) : Whatwg.Svg.Scene.Band := Whatwg.Svg.Scene.Band.point n (LEFT + 12) (LW - 16)

/-- A beat's place across. -/
def xOf (n i : Nat) : Int := Whatwg.Svg.Scene.Band.at (beatsOf n) i

/-- The counts down: the deficit's floor at the bottom, the brim and the pressure's ceiling at the
top. -/
def scaleOf (cap maxPend maxWait : Nat) : Whatwg.Svg.Scene.Scale :=
  .linear (-(maxWait : Int)) (cap + maxPend) (LH - PADY) PADY

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

/-- **The level of the run**: the vessel's band, the bar lines, the three areas, and the units,
all placed by the run's two scales. -/
def level (ms : List Organism.Marking) : List (Keyed Call) :=
  let n := ms.length
  let cap := (ms.head?.map (·.capacity)).getD 0
  let maxPend := ms.foldl (fun a m => max a m.offers.length) 0
  let maxWait := ms.foldl (fun a m => max a m.takers.length) 0
  let s := scaleOf cap maxPend maxWait
  let xs := (List.range n).map (xOf n)
  let y (v : Int) : Int := s.at v
  let U := max 1 (y 0 - y 1)
  let r : Int := max 2 (min 5 (U / 3))
  let zero := y 0
  let brim := y cap
  let x0 := (xs.head?).getD LEFT
  let x1 := (xs.getLast?).getD LW
  let band : Keyed Call := ⟨"vessel", .shape .ink 50 [Grow.roundRect (1000 * (x0 - 14)) (1000 * brim)
      (1000 * (x1 - x0 + 28)) (1000 * (zero - brim)) (1000 * (min 12 ((zero - brim) / 2)))]⟩
  let bars := xs.map fun x => (⟨"beat", Call.vrule .rule x PADY (LH - 2 * PADY) 1⟩ : Keyed Call)
  let flat (v : Int) : List (Int × Int) := xs.map (·, y v)
  let at_ (vs : List Int) : List (Int × Int) := xs.zip (vs.map y)
  let held := ms.map fun m => (m.held.length : Int)
  let pend := ms.map fun m => (cap : Int) + m.offers.length
  let wait := ms.map fun m => -(m.takers.length : Int)
  let areas : List (Keyed Call) :=
    [⟨"held", .shape .ink 260 [area (at_ held) (flat 0)]⟩,
     ⟨"pressure", .shape .ink 140 [area (at_ pend) (flat cap)]⟩,
     ⟨"deficit", .shape .ink 140 [area (flat 0) (at_ wait)]⟩]
  let mid (k : Int) : Int := (y k + y (k + 1)) / 2
  let unitsAt (i : Nat) (m : Organism.Marking) : List (Keyed Call) :=
    let x := xs.getD i 0
    ((List.range m.held.length).map fun (k : Nat) =>
      (⟨s!"held/{i}/{k}", .shape .ink 1000 [Organism.disc x (mid k) r]⟩ : Keyed Call)) ++
    ((List.range m.offers.length).map fun (k : Nat) =>
      ⟨s!"offer/{i}/{k}", .shape .ink 900 (Grow.ring (1000 * (x - r - 1)) (1000 * (mid (cap + k) - r - 1)) (2000 * (r + 1)) (2000 * (r + 1)) (1000 * (r / 2)) 1100)⟩) ++
    ((List.range m.takers.length).map fun (k : Nat) =>
      ⟨s!"taker/{i}/{k}", .shape .ink 900 (Grow.ring (1000 * (x - r - 1)) (1000 * (mid (-(k : Int) - 1) - r - 1)) (2000 * (r + 1)) (2000 * (r + 1)) (1000 * (r / 2)) 1100)⟩)
  let labels : List (Keyed Call) :=
    [⟨"pressure", .text .label 8 (y (cap + max 1 maxPend) / 2 + y cap / 2 + 4) 90 "pressure"⟩,
     ⟨"held", .text .label 8 ((zero + brim) / 2 + 4) 90 "held"⟩,
     ⟨"deficit", .text .label 8 (zero + U / 2 + 4) 90 "deficit"⟩]
  band :: bars ++ areas ++ (ms.zipIdx.flatMap fun (m, i) => unitsAt i m) ++ labels

/-- The height of the level's picture. -/
def LEVEL_H : Int := LH

/-- **The lives of the channels**: each channel a ribbon along the run, as thick at each beat as
the organism draws it, the beats placed by the run's point scale. -/
def lives (ds : List (List Nat)) : List (Keyed Call) :=
  let names := ["in", "enter", "leave", "out"]
  let n := ds.length
  let xs := (List.range n).map (xOf n)
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
