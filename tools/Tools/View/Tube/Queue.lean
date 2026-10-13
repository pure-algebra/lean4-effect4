import Tools.View.Tube.Draw
import Tools.View.Living.Organism

/-!
# Tools.View.Tube.Queue — the Queue as plumbing: a vessel between an inlet and an outlet

The Queue's cell, at each command of a run, drawn in the tube language (`Tools.View.Tube.Draw`):

* **The vessel** holds the messages, the front at its outlet end. Its length is its capacity in
  units, so a full vessel is full to its ends: the capacity is the pipework, an invariant.
* **The inlet** brings offers from the world on the left. When the vessel is full its valve closes
  (a float valve, the cistern's way of refusing water), and the offers that wait stand behind it
  as backwater. **The inlet bends under what it holds**: a span loaded evenly turns at its ends in
  proportion to its load (a beam's end slope is `wL³/24EI`), so a waiting message weighs on it.
* **The outlet** takes messages to the world on the right. A taker that waits on an empty vessel
  is a hollow unit at the outlet's end: a promise of a message (hollow is a promise, filled is
  kept). An offer that finds a taker waiting runs through to it.
* **A unit moves by continuity**: its place is a volume along the line of tubes, so it is a length
  in each tube, and its speed in each is inverse to the tube's width.
-/

namespace Tools.View.Tube.Queue
open Tools.View Tools.View.Tube
open Tools.View.Living.Organism (Marking)

/-- The widths of the pipes' and the vessel's contents, in thousandths of a pixel. -/
def PIPE : Nat := 8000
def VESSEL : Nat := 16000
/-- The room at each end of the vessel, for its collars. -/
def HEAD : Nat := 5000
/-- A closed valve's plug, its length along the inlet, and how far the valve stands from the inlet's
end: clear of the vessel's head. -/
def PLUG : Nat := 6000
def VALVE_AT : Nat := 16000
/-- The inlet's end slope with nothing in it, and for each message it holds, in millionths of
a radian; and the most. -/
def SAG0 : Int := 15000
def SAG_PER : Int := 55000
def SAG_MAX : Int := 260000
/-- The picture's margin and the axis's height. -/
def MARGIN : Nat := 24000
def AXIS : Int := 26000

/-- **The pipework of a run**: how long the inlet's span, the vessel and the outlet are. -/
structure Layout where
  cap : Nat
  inLen : Nat
  vLen : Nat
  outLen : Nat

/-- The layout for a capacity, the most messages that wait at the inlet and the most takers that
wait at the outlet. -/
def Layout.of (cap waiting takers : Nat) : Layout :=
  { cap
    inLen := max 150000 ((waiting + 1) * unitLen PIPE + PLUG + VALVE_AT + 30000)
    vLen := cap * unitLen VESSEL + 2 * HEAD
    outLen := max 130000 ((takers + 1) * unitLen PIPE + 30000) }

def Layout.W (l : Layout) : Nat := (2 * MARGIN + l.inLen + l.vLen + l.outLen) / 1000
def Layout.H (_ : Layout) : Nat := 64

/-- **The inlet under a load of `n` messages**: a span from the margin to the vessel whose ends
turn by the slope of its load, so it is longer than its chord by the arc's ratio. -/
def Layout.inlet (l : Layout) (n : Nat) : Tube :=
  let α := min SAG_MAX (SAG0 + SAG_PER * n)
  let len := (l.inLen : Int) * ONE / sinc α
  ⟨MARGIN, AXIS, α, PIPE, [⟨len.toNat, -2 * α⟩]⟩

def Layout.vessel (l : Layout) : Tube := straight (MARGIN + l.inLen) AXIS 0 VESSEL l.vLen
def Layout.outlet (l : Layout) : Tube := straight (MARGIN + l.inLen + l.vLen) AXIS 0 PIPE l.outLen

/-- A tube's volume, in thousandths of a square pixel. -/
def volume (t : Tube) : Int := (t.length * t.bore / 1000 : Nat)

/-- A unit's amount, in thousandths of a square pixel. -/
def A : Int := (AREA * 1000 : Nat)

/-- **Where a unit whose front stands at the volume `v` is in each tube** of a line of tubes:
the length along it, `(v − the volume before it) / its width`. -/
def fronts (line : List Tube) (v : Int) : List Int :=
  (line.foldl (fun (acc : Int × List Int) t =>
    ((acc.1 + volume t), acc.2 ++ [(v - acc.1) * 1000 / (t.bore : Int)])) (0, [])).2

/-- **The picture of a marking**: the pipework at its load, the valve, the units of every message
of the run and the hollows of every taker of the run, each where the marking puts it. -/
def picture (l : Layout) (msgs takerIds : List Nat) (seenBefore : List Nat) (m : Marking) : List Mark :=
  let waiting := m.offers.flatMap (·.2)
  let inlet := l.inlet waiting.length
  let vessel := l.vessel
  let outlet := l.outlet
  let line := [inlet, vessel, outlet]
  let vIn := volume inlet
  let vV := volume vessel
  let total := vIn + vV + volume outlet
  let full := m.held.length ≥ l.cap
  let plugLen : Nat := if full then PLUG else 0
  let place (msg : Nat) : Int :=
    match m.held.idxOf? msg, waiting.idxOf? msg with
    | some k, _ => vIn + vV - ((HEAD * VESSEL / 1000 : Nat) : Int) - k * A
    | none, some k => vIn - (((VALVE_AT + plugLen) * PIPE / 1000 : Nat) : Int) - k * A
    | none, none => if seenBefore.contains msg || m.answered == some msg then total + A else 0
  let names := ["in", "vessel", "out"]
  let units := msgs.flatMap fun msg =>
    ((line.zip names).zip (fronts line (place msg))).map fun ((t, nm), s) =>
      unitOf s!"m{msg}@{nm}" t s
  let hollows := takerIds.flatMap fun id =>
    let s := match m.takers.idxOf? id with
      | some j => (outlet.length : Int) - j * unitLen PIPE
      | none => (outlet.length : Int) + unitLen PIPE
    hollowOf s!"t{id}" outlet s
  bodyOf "in" inlet ++ bodyOf "vessel" vessel ++ bodyOf "out" outlet ++
  let valveEnd : Int := (inlet.length : Int) - VALVE_AT
  [collarOf "valve:collar" inlet (valveEnd - PLUG - 2000) (PLUG + 4000),
   plugOf "valve" inlet (valveEnd - plugLen) plugLen] ++
  units ++ hollows

/-- **A run's frames**: its layout and, for each marking, its words and its picture. -/
def run (sc : CellSheet.Scene) : Except String (Layout × List (String × List Mark)) := do
  let fs ← sc.run
  let ms := fs.map Living.Organism.marking
  let l := Layout.of sc.capacity (ms.foldl (fun a m => max a (m.offers.flatMap (·.2)).length) 0)
    (ms.foldl (fun a m => max a m.takers.length) 0)
  let msgs := (ms.flatMap fun m => m.held ++ m.offers.flatMap (·.2) ++ m.answered.toList).eraseDups
  let takers := (ms.flatMap (·.takers)).eraseDups
  let seen (i : Nat) : List Nat :=
    ((ms.take i).flatMap fun m => m.held ++ m.offers.flatMap (·.2) ++ m.answered.toList).eraseDups
  return (l, (fs.zip ms).zipIdx.map fun ((f, m), i) => (f.words, picture l msgs takers (seen i) m))

end Tools.View.Tube.Queue
