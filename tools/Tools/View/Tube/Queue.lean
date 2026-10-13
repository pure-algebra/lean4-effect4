import Tools.View.Tube.Motion
import Tools.View.Tube.Marking
import Whatwg.Svg.Scene.Units

/-!
# Tools.View.Tube.Queue — the Queue as plumbing: a vessel between an inlet and an outlet

The Queue's cell, at each command of a run, drawn in the tube language (`Tools.View.Tube.Draw`):

* **The vessel** holds the messages as the kit's slots (`Units.slots`): the front in the slot at
  the outlet's end, the order kept, the room shown. Its length is its capacity in units, so a
  full vessel is full to its ends: the capacity is the pipework, an invariant.
* **The inlet** brings offers from the world, off the picture on the left. When the vessel is
  full its valve closes (a float valve, the cistern's way of refusing water): the inlet parts by
  an air gap, nothing passes, and the offers that wait stand behind it as backwater
  (`Units.lane`). **The inlet bends under what it holds**: it is clamped at the vessel's flange,
  so it meets the vessel on its tangent, and a span clamped at its ends and loaded evenly sags in
  three arcs, its slope at the inflections in proportion to its load (a beam's slope is
  `∝ wL³/EI`); a load that arrives at once carries it past its rest, and it comes back.
* **The vessel** joins its pipes by reducers, so its outline has no step.
* **The outlet** takes messages to the world, off the picture on the right. A taker that waits on
  an empty vessel is a bubble at the outlet: a promise of a message (hollow is a promise, filled
  is kept). It grows where it stands and, kept, shrinks there.
* **A unit moves by continuity**: its place is a volume along the line of tubes, so it is a length
  in each tube, and its speed in each is inverse to the tube's width. The tube swells round it
  as it goes.

**When.** A cause moves before its effect, so a step is staged within its beat (Heer and Robertson,
"Animated transitions in statistical data graphics", 2007: staging, and staggered starts): the
front leaves first and each unit behind follows a moment later, as a queue of cars starts from a
green light, one after another; a valve opens before the offer it lets in moves; an offer that
meets a closed valve stops against it, and the pressure of the stop runs back up the inlet
(Joukowsky's surge, `Δp = ρ a Δv`); the inlet takes the weight when it lands.
-/

namespace Tools.View.Tube.Queue
open Tools.View Tools.View.Tube
open Whatwg.Svg.Scene (Easing Slot)
open Whatwg.Svg.Scene.Units (slots lane)

/-- The widths of the pipes' and the vessel's contents, in thousandths of a pixel. -/
def PIPE : Nat := 12000
def VESSEL : Nat := 16000
/-- The room at each end of the vessel. -/
def HEAD : Nat := 6000
/-- A closed valve's air gap, its length along the inlet, and how far the valve stands from the
inlet's end, clear of the vessel's head. -/
def PLUG : Nat := GAP
/-- How far the offers that wait stand back from a closed valve: its gap and its round end. -/
def PARTED : Nat := PLUG + body PIPE / 2
def VALVE_AT : Nat := 22000
/-- How far the pipes run past the picture's edges, to the world. -/
def OFF : Nat := 40000
/-- The visible lead of the inlet and tail of the outlet. -/
def LEFT : Nat := 16000
def RIGHT : Nat := 16000
/-- The inlet's slope at its inflections with nothing in it and for each message it holds
(millionths of a radian), the most, and how far past its rest a sudden load carries it (per cent
of the change). -/
def SAG0 : Int := 8000
def SAG_PER : Int := 45000
def SAG_MAX : Int := 240000
def OVERSHOOT : Int := 35
/-- The axis's height and the picture's. -/
def AXIS : Int := 30000
def HEIGHT : Nat := 74

/-- The staging, in thousandths of a beat: the gap between one unit's start and the next's; how
long a valve takes to open; when an offer that meets a closed valve stops. -/
def STAGGER : Nat := 70
def OPENING : Nat := 180
def IMPACT : Nat := 560

/-- **The pipework of a run**: how long the inlet's visible span, the vessel and the outlet are. -/
structure Layout where
  cap : Nat
  inLen : Nat
  vLen : Nat
  outLen : Nat

/-- The layout for a capacity, the most messages that wait at the inlet and the most takers that
wait at the outlet. -/
def Layout.of (cap waiting takers : Nat) : Layout :=
  { cap
    inLen := max 200000 ((waiting + 1) * unitLen PIPE + PARTED + VALVE_AT + 30000)
    vLen := cap * unitLen VESSEL + 2 * HEAD
    outLen := max 160000 ((takers + 1) * unitLen PIPE + 40000) }

def Layout.W (l : Layout) : Nat := (LEFT + l.inLen + l.vLen + l.outLen + RIGHT) / 1000

/-- The inlet's slope under a load of `n` messages. -/
def slope (n : Nat) : Int := min SAG_MAX (SAG0 + SAG_PER * n)

/-- **The inlet at a slope** `β`: a span from off the picture to the vessel, clamped level at both
ends, that sags in three arcs, `ℓ` turning `β`, `2ℓ` turning back `2β`, `ℓ` turning `β`, so it
leaves and meets the vessel on its tangent. Its chord is `4ℓ · sinc(β/2) · cos(β/2)`. -/
def Layout.inletAt (l : Layout) (β : Int) : Tube :=
  let chord : Int := (OFF + LEFT + l.inLen : Nat)
  let q := (chord * ONE / sinc (β / 2) * ONE / (sinCos (β / 2)).2 / 4).toNat
  ⟨-(OFF : Int), AXIS, 0, PIPE, [⟨q, β⟩, ⟨2 * q, -2 * β⟩, ⟨q, β⟩]⟩

def Layout.inlet (l : Layout) (n : Nat) : Tube := l.inletAt (slope n)
def Layout.vessel (l : Layout) : Tube := straight (LEFT + l.inLen) AXIS 0 VESSEL l.vLen
def Layout.outlet (l : Layout) : Tube :=
  straight (LEFT + l.inLen + l.vLen) AXIS 0 PIPE (l.outLen + RIGHT + OFF)

/-- A tube's volume, in thousandths of a square pixel. -/
def volume (t : Tube) : Int := (t.length * t.bore / 1000 : Nat)

/-- A unit's amount, in thousandths of a square pixel. -/
def A : Int := (AREA * 1000 : Nat)

/-- **Where a unit whose slot's front stands at the volume `v` is in each tube** of a line of
tubes: the length along it, `(v − the volume before it) / its width`. -/
def fronts (line : List Tube) (v : Int) : List Int :=
  (line.foldl (fun (acc : Int × List Int) t =>
    ((acc.1 + volume t), acc.2 ++ [(v - acc.1) * 1000 / (t.bore : Int)])) (0, [])).2

/-- The index of a unit among a place's slots. -/
def slotOf (ss : List (Slot Nat)) (msg : Nat) : Option Nat :=
  ss.zipIdx.findSome? fun (s, i) => match s with | Slot.held u => if u == msg then some i else none | _ => none

/-- **Where a message stands** in a marking, as the volume of its slot's front: in its slot of the
vessel, in its place in the lane behind the valve, off the picture on the right once it has gone,
and off it on the left before it comes. -/
def place (l : Layout) (m : Marking) (gone : Bool) (msg : Nat) : Int :=
  let line := [l.inlet m.waiting.length, l.vessel, l.outlet]
  let vIn := volume (l.inlet m.waiting.length)
  let vV := volume l.vessel
  let total := line.foldl (· + volume ·) 0
  let plug : Nat := if m.held.length ≥ l.cap then PARTED else 0
  match slotOf (slots l.cap m.held) msg, slotOf (lane m.waiting) msg with
  | some i, _ => vIn + vV - ((HEAD * VESSEL / 1000 : Nat) : Int) - i * A
  | none, some k => vIn - (((VALVE_AT + plug) * PIPE / 1000 : Nat) : Int) - k * A
  | none, none => if gone then total + A else 0

/-- Whether the vessel is full, so its valve is closed. -/
def closed (l : Layout) (m : Marking) : Bool := m.held.length ≥ l.cap

/-- **The picture of a step**: the pipework at its load, the valve, a unit for every message of
the run and a bubble for every taker that waits, each where the marking puts it, and each timed
by what moved it. `prev` is the marking before, and `seen` the messages that stood in the run
before this marking. -/
def picture (l : Layout) (msgs : List Nat) (seen : List Nat) (prev : Option Marking)
    (m : Marking) : Picture :=
  let before := prev.getD m
  let wasClosed := prev.isSome && closed l before
  let isClosed := closed l m
  let n₀ := before.waiting.length
  let n₁ := m.waiting.length
  let inlet := l.inlet n₁
  let line := [inlet, l.vessel, l.outlet]
  let lineBefore := [l.inlet n₀, l.vessel, l.outlet]
  let names := ["in", "vessel", "out"]
  -- the inlet's shape: it takes a new load when the load lands, and gives one up as it leaves,
  -- passing its rest by `OVERSHOOT` per cent of the change
  let sagTiming : Timing :=
    if n₁ > n₀ then { delay := IMPACT - 40, duration := 1000 - (IMPACT - 40), ease := settle }
    else { delay := 120, duration := 760, ease := settle }
  let viaInlet : Option Tube :=
    if n₁ == n₀ then none
    else some (l.inletAt (slope n₁ + (slope n₁ - slope n₀) * OVERSHOOT / 100))
  let onInlet (mk : Mark) : Mark := { mk with shape := some sagTiming }
  -- a message's timing: the front first, each behind it a moment later; through a valve that
  -- opens, after it opens; against a valve that is closed, a stop
  let departed := before.held.filter fun msg => !(m.held.contains msg) && !(m.waiting.contains msg)
  let order := m.held ++ m.waiting
  let timingOf (msg : Nat) : Timing :=
    if departed.contains msg then { duration := 760, ease := settle } else
    let rank := (order.idxOf? msg).getD 0 + (if departed.isEmpty then 0 else 1)
    let through := before.waiting.contains msg && m.held.contains msg
    let fresh := !(seen.contains msg)
    if fresh && m.waiting.contains msg && isClosed then
      { duration := IMPACT, ease := Easing.cubicIn }
    else
      let d := STAGGER * rank + (if through then OPENING else 0)
      { delay := d, duration := 1000 - min 700 d, ease := settle }
  let gone (msg : Nat) : Bool := seen.contains msg || m.answered == some msg
  let goneBefore (msg : Nat) : Bool :=
    seen.contains msg && !(before.held.contains msg) && !(before.waiting.contains msg)
  -- each message's unit in each tube, the inlet's first
  let unitsIn : List (Nat × Mark) := msgs.flatMap fun msg =>
    let v := place l m (gone msg) msg
    let tm := timingOf msg
    (((line.zip names).zip (fronts line v)).zipIdx).map fun (((t, nm), s), i) =>
      let u := { unitOf s!"m{msg}@{nm}" t s with move := tm }
      (i, if i == 0 then onInlet u else u)
  let units := unitsIn.map (·.2)
  -- the swell round each unit that moves, in each tube it passes through
  let swells := if prev.isNone then [] else msgs.flatMap fun msg =>
    let v₀ := place l before (goneBefore msg) msg
    let v₁ := place l m (gone msg) msg
    if v₀ == v₁ then [] else
    let tm := timingOf msg
    ((line.zip ((fronts lineBefore v₀).zip (fronts line v₁))).zip names).flatMap
      fun ((t, (s₀, s₁)), nm) =>
        let len : Int := t.length
        let u : Int := unitLen t.bore
        if max s₀ s₁ < 0 || min s₀ s₁ - u > len then [] else
        let rise : Int := reducerLen (body PIPE) (body VESSEL)
        swellOf s!"s{msg}@{nm}" (if nm == "in" then "in:wall" else "") t (pillDash t s₀) (pillDash t s₁) tm
          (if nm == "vessel" then some (rise, len - rise) else none)
  -- the valve: closed when the vessel is full; it opens at once and closes after the unit that
  -- fills the vessel has come to rest
  let valveEnd : Int := (inlet.length : Int) - VALVE_AT
  let plugLen : Nat := if isClosed then PLUG else 0
  -- a full vessel that lets a waiting offer in as a take frees a slot: its valve opens and closes
  -- behind the offer within the beat
  let reopens := wasClosed && isClosed && before.waiting.any (m.held.contains ·)
  let valveTiming : Timing :=
    if isClosed && !wasClosed then { delay := 620, duration := 240, ease := settle }
    else if reopens then { duration := 900, ease := settle }
    else { duration := OPENING, ease := settle }
  let valve := [onInlet { plugOf "valve" inlet (valveEnd - plugLen) plugLen with move := valveTiming }]
  -- an offer that meets the closed valve: the surge runs back up the inlet from the valve
  let blocked := msgs.filter fun msg => !(seen.contains msg) && m.waiting.contains msg && isClosed
  let surge := if prev.isNone then [] else blocked.flatMap fun msg =>
    let tm : Timing := { delay := IMPACT, duration := 1000 - IMPACT, ease := Easing.linear }
    swellOf s!"surge{msg}" "in:wall" inlet (valveEnd - (PLUG : Int) - 40000, 30000)
      (-(OFF : Int) - 30000, 30000) tm
  -- the takers that wait: a bubble each at the outlet's visible end; a new one grows where it
  -- stands, and one that is kept shrinks there as its message reaches it
  let outEnd : Int := ((l.outLen + RIGHT : Nat) : Int) - 14000
  let bubble (id : Nat) (j : Nat) (tm : Timing) : List Mark :=
    (hollowOf s!"t{id}" l.outlet (outEnd - (j * unitLen PIPE : Nat))).map fun mk => { mk with move := tm }
  let waitingTakers := m.takers.zipIdx.flatMap fun (id, j) =>
    bubble id j (if prev.isSome && before.takers.contains id then { ease := settle }
      else { delay := 120, duration := 600, ease := settle })
  let keptTakers := (if prev.isSome then before.takers else []).zipIdx.flatMap fun (id, j) =>
    if m.takers.contains id then [] else
    (bubble id j { delay := 260, duration := 380, ease := settle }).map fun mk =>
      { mk.gone with move := mk.move }
  -- the poses passed through: the inlet past its rest, and the valve open
  let viaMarks : List Mark :=
    ((bodyOf "in" (into inlet true) (round := false)).map onInlet ++ valve ++ (unitsIn.filter (·.1 == 0)).map (·.2)).filterMap
      fun mk =>
        let t := if mk.key == "in:wall" then (viaInlet.map (into · true)).getD mk.tube
          else viaInlet.getD mk.tube
        let d := if reopens && mk.key == "valve" then some (valveEnd, 0) else mk.dash
        if viaInlet.isNone && d == mk.dash then none else some { mk with tube := t, dash := d }
  { marks := (bodyOf "in" (into inlet true) (round := false)).map onInlet ++
      reducedOf "vessel" l.vessel (body PIPE) (body PIPE) ++
      bodyOf "out" (into l.outlet false) (round := false) ++ valve ++ units ++ waitingTakers ++ keptTakers
    via := viaMarks
    events := swells ++ surge }

/-- **A run's pictures**: its layout and, for each marking, its words and its picture. -/
def run (sc : CellSheet.Scene) : Except String (Layout × List (String × Picture)) := do
  let fs ← sc.run
  let ms := fs.map marking
  let l := Layout.of sc.capacity (ms.foldl (fun a m => max a m.waiting.length) 0)
    (ms.foldl (fun a m => max a m.takers.length) 0)
  let msgs := (ms.flatMap fun m => m.held ++ m.waiting ++ m.answered.toList).eraseDups
  let seen (i : Nat) : List Nat :=
    ((ms.take i).flatMap fun m => m.held ++ m.waiting ++ m.answered.toList).eraseDups
  return (l, (fs.zip ms).zipIdx.map fun ((f, m), i) =>
    (f.words, picture l msgs (seen i) (if i == 0 then none else ms[i - 1]?) m))

end Tools.View.Tube.Queue
