import Tools.View.Tube.Motion

/-!
# Tools.View.Tube.Physics — how units move: inertia, a queue's wave, a shape that keeps its amount

The owner's word of 2026-10-13: "working on pill / circle physics within the tubes... improving
deformation, turning, curves, inertia, merging". A prototype in the browser came first
(`tools/view/out/proto/physics.html`, kept out of the tree); this module is its law in whole
numbers, so every film is the same at every run.

**Inertia, by the Intelligent Driver Model** (Treiber, Hennecke and Helbing, "Congested traffic
states in empirical observations and microscopic simulations", Phys. Rev. E 62, 2000). A unit
gathers speed up to the law's `speed`, keeps a headway to the unit ahead, and brakes softly to a
stand at its slot in the next picture. Its acceleration is
`a · (1 − (v/v₀)⁴ − (s*/s)²)`, where `s` is the gap ahead and `s* = s₀ + v T + v Δv / (2 √(a b))`
the gap it wants. A queue that starts moves as a wave from its front, each unit waiting until the
one ahead has left it room, as cars leave a light. The law runs in the line's volume (the
coordinate of `Queue.fronts`), so one law serves every bore of the line. It steps every
`Law.step` milliseconds; the last moment of the beat stands exactly where the next picture puts
each unit, so a carried film ends where an eased one did.

**A shape that keeps its amount.** At rest a unit is its circle, or its pill in a narrow bore. As
it runs it stretches along its centreline by `k = 1 + stretch · v / v₀` and narrows across by
`√k`, its area kept, as a drop in a capillary lengthens with its speed. Along a bend the dash
follows the centreline, so a stretched unit bends with its tube.

Not here yet: two units that merge (the kit's coalescence, slice S24) and a unit's drift toward
the outer wall of a bend.
-/

namespace Tools.View.Tube.Physics
open Tools.View Tools.View.Tube

/-- **The law's numbers**, in the line's volume, thousandths of a square pixel (in a bore whose
contents are 10 px wide, ten of them a thousandth of a pixel along it), and milliseconds of a beat
of one second. -/
structure Law where
  /-- The speed a unit runs at, a millisecond: 8000 is 800 px a second in a pipe. -/
  speed : Int := 8000
  /-- The most speed it gathers, a millisecond squared. -/
  gather : Int := 50
  /-- How hard it brakes at ease, a millisecond squared. -/
  brake : Int := 80
  /-- The least gap it keeps to what is ahead. -/
  least : Int := 2000
  /-- The headway it keeps, in milliseconds. -/
  headway : Int := 30
  /-- How much it stretches at its full speed, in thousandths. -/
  stretch : Int := 350
  /-- The length of one step of the law, in milliseconds. -/
  step : Nat := 5
deriving Inhabited

/-- **The Intelligent Driver Model's acceleration** at the speed `v`, the gap `gap` ahead and the
speed `dv` at which it closes: the free road's term and the interaction's, held above four times
the braking. -/
def Law.accel (l : Law) (v gap dv : Int) : Int :=
  let root : Int := Grow.isqrt (l.gather * l.brake).toNat
  let want : Int := l.least + max 0 (v * l.headway + v * dv / (2 * max 1 root))
  let r := v * 1000 / l.speed
  let free := r * r / 1000 * r / 1000 * r / 1000
  let q := want * 1000 / max 1 gap
  max (-4 * l.brake) (l.gather * (1000 - free - q * q / 1000) / 1000)

/-- **A unit the law moves**: its id, where it stands in the line's volume at the beat's start and
at its end, the milliseconds it waits before it moves, and whether it moves at all (a unit that
stays is still a unit ahead of others). -/
structure Mover where
  id : Nat
  from_ : Int
  to : Int
  start : Nat := 0
  free : Bool := true
deriving Repr, Inhabited

/-- Where a unit stands and how fast it runs. -/
structure State where
  x : Int
  v : Int
deriving Repr, Inhabited, BEq

/-- **One step of the law** for every unit at the millisecond `t`: each that moves takes the
lesser of the accelerations its slot and the unit ahead ask for, and never passes either; `slot`
is a unit's amount, the room each takes. -/
def Law.stepAll (l : Law) (slot : Int) (ms : List Mover) (t : Nat) (ss : List State) : List State :=
  let all := ms.zip ss
  all.map fun (m, s) =>
    if !m.free || t < m.start then s else
    let lead : Option State := all.foldl (fun acc (m', s') =>
      if m'.id == m.id || s'.x ≤ s.x then acc else match acc with
        | some b => if s'.x < b.x then some s' else acc
        | none => some s') none
    let toSlot := l.accel s.v (m.to - s.x + l.least) s.v
    let a := match lead with
      | some b => min toSlot (l.accel s.v (b.x - slot - s.x + l.least) (s.v - b.v))
      | none => toSlot
    let v := max 0 (s.v + a * l.step)
    let cap := match lead with | some b => min m.to (b.x - slot) | none => m.to
    let x := min (s.x + v * l.step) (max s.x cap)
    if x == m.to then ⟨x, 0⟩
    else if x == cap then ⟨x, match lead with | some b => min v b.v | none => 0⟩
    else ⟨x, v⟩

/-- **The law run through one beat**: for each unit, where it stands and how fast it runs at the
`moments + 1` moments spread over the beat; at the last it stands at its slot in the next
picture. -/
def Law.run (l : Law) (slot : Int) (ms : List Mover) (moments : Nat := MOMENTS) : List (List State) :=
  let steps := 1000 / l.step
  let every := max 1 (steps / moments)
  let init := ms.map fun m => (⟨m.from_, 0⟩ : State)
  let frames := ((List.range steps).foldl (fun (acc : List State × List (List State)) k =>
      let ss := l.stepAll slot ms (k * l.step) acc.1
      (ss, if (k + 1) % every == 0 then acc.2 ++ [ss] else acc.2)) (init, [init])).2
  let frames := (frames.take moments) ++ [ms.map fun m => (⟨m.to, 0⟩ : State)]
  (List.range ms.length).map fun i => frames.map fun f => f.getD i default

/-- π in millionths. -/
def PI_M : Int := 3141593

/-- **A unit's dash and width at a speed**, from its dash at rest `(start, len)` in a bore whose
contents are `c` wide: stretched along its centreline by `k = 1 + stretch · v / v₀`, narrowed
across by `√k`, and as long as keeps the area of the pill at rest, `c · len + π c² / 4`, its
middle where it was. -/
def Law.shape (l : Law) (c : Nat) (rest : Int × Nat) (v : Int) : (Int × Int) × Int :=
  let k : Int := 1000 + l.stretch * min 1200 (v * 1000 / l.speed) / 1000
  let w : Int := (c : Int) * Grow.isqrt (1000000000 / k.toNat) / 1000
  let area : Int := (c : Int) * rest.2 + PI_M * c * c / 4000000
  let d : Int := max 0 ((area - PI_M * w * w / 4000000) / max 1 w)
  let middle := rest.1 + (rest.2 : Int) / 2
  ((middle - d / 2, d), w)

/-- **A unit's carry along a line of tubes**: for each tube, its key, and its dash and width at
each moment, from where it stands in the line's volume and how fast it runs along the tube (its
volume's speed over the contents' width, as a unit's circle runs); in a tube where the unit does
not stand, the dash lies off the tube and draws nothing. -/
def Law.carries (l : Law) (key : String) (line : List (String × Tube)) (states : List State) :
    List Carry :=
  let befores := (line.foldl (fun (acc : Int × List Int) (_, t) =>
    (acc.1 + ((t.length * contents t.bore / 1000 : Nat) : Int), acc.2 ++ [acc.1])) (0, [])).2
  (line.zip befores).map fun ((nm, t), before) =>
    let c := contents t.bore
    let at_ (st : State) := l.shape c (pillDash t ((st.x - before) * 1000 / max 1 (c : Int)))
      (st.v * (UNIT : Int) / max 1 (c : Int))
    { key := key ++ "@" ++ nm
      window := states.map fun st => (at_ st).1
      width := states.map fun st => (at_ st).2 }

-- the law: a unit at rest with room ahead gathers speed; one at its slot stays
#guard (({} : Law).accel 0 1000000 0) == 50
#guard (({} : Law).accel 0 2000 0) == 0
-- a circle at rest keeps its width and no dash; at full speed it narrows and lengthens
#guard ({} : Law).shape 10000 (100000, 0) 0 == ((100000, 0), 10000)
#guard let ((s, d), w) := ({} : Law).shape 10000 (100000, 0) 8000
  w < 10000 && d > 0 && s + d / 2 == 100000
-- two units 40 px of volume apart in a pipe run to their slots: the front first, no passing, and
-- at the last moment each stands at its slot
#guard
  let r := ({} : Law).run 120000 [⟨1, 600000, 1200000, 0, true⟩, ⟨2, 480000, 1080000, 70, true⟩]
  let a := r.getD 0 []; let b := r.getD 1 []
  (a.getLast?.map (·.x)) == some 1200000 && (b.getLast?.map (·.x)) == some 1080000 &&
  (a.zip b).all (fun (p, q) => q.x + 120000 ≤ p.x) &&
  ((a.zip a.tail).all fun (p, q) => p.x ≤ q.x)

end Tools.View.Tube.Physics
