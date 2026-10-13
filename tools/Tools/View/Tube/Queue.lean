import Tools.View.Tube.Motion
import Tools.View.Tube.Board.Film
import Tools.View.Tube.Marking
import Whatwg.Svg.Scene.Units

/-!
# Tools.View.Tube.Queue

The Queue film reads the evaluated cell after each command.
Its vessel holds messages in slots, its valve closes at capacity, and waiting takers are hollow.
One fixed inlet uses the greatest recorded load.
Contents change on command boundaries through the kit's changes-only writer.
The film samples no path and invents no store event.
Placement: view-only under rows 362 and 374.
-/

namespace Tools.View.Tube.Queue
open Tools.View Tools.View.Tube
open Whatwg.Svg.Scene (Easing Slot)
open Whatwg.Svg.Scene.Units (slots lane)

/-- The bores of the pipes and of the vessel, in thousandths of a pixel: bodies of 20 and 28 px
(`WIDTHS`). -/
def PIPE : Nat := 10000
def VESSEL : Nat := 18000
/-- The room at each end of the vessel: its reducer from the pipe, and six pixels more, so its
units stand where it is full width. -/
def HEAD : Nat := reducerLen (body PIPE) (body VESSEL) + 6000
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
/-- The inlet's slope at its inflections, in millionths of a radian, bounded at its greatest load. -/
def SAG0 : Int := 8000
def SAG_PER : Int := 45000
def SAG_MAX : Int := 240000
/-- The axis's height and the picture's. -/
def AXIS : Int := 30000
def HEIGHT : Nat := 74

/-- **The pipework of a run**: how long the inlet's visible span, the vessel and the outlet are. -/
structure Layout where
  cap : Nat
  inLen : Nat
  vLen : Nat
  outLen : Nat
  load : Nat := 0

/-- The layout for a capacity, the most messages that wait at the inlet and the most takers that
wait at the outlet. -/
def Layout.of (cap waiting takers : Nat) : Layout :=
  { cap
    inLen := max 200000 ((waiting + 1) * unitLen PIPE + PARTED + VALVE_AT + 30000)
    vLen := cap * unitLen VESSEL + 2 * HEAD
    outLen := max 160000 ((takers + 1) * unitLen PIPE + 40000)
    load := waiting }

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

/-- A tube's volume, in thousandths of a square pixel: its length by the width of its contents. -/
def volume (t : Tube) : Int := (t.length * contents t.bore / 1000 : Nat)

/-- A unit's amount, in thousandths of a square pixel. -/
def A : Int := (AREA * 1000 : Nat)

/-- **Where a unit whose slot's front stands at the volume `v` is in each tube** of a line of
tubes: the length along it, `(v − the volume before it) / its width`. -/
def fronts (line : List Tube) (v : Int) : List Int :=
  (line.foldl (fun (acc : Int × List Int) t =>
    ((acc.1 + volume t), acc.2 ++ [(v - acc.1) * 1000 / (contents t.bore : Int)])) (0, [])).2

/-- The index of a unit among a place's slots. -/
def slotOf (ss : List (Slot Nat)) (msg : Nat) : Option Nat :=
  ss.zipIdx.findSome? fun (s, i) => match s with | Slot.held u => if u == msg then some i else none | _ => none

/-- **Where a message stands** in a marking, as the volume of its slot's front: in its slot of the
vessel, in its place in the lane behind the valve, off the picture on the right once it has gone,
and off it on the left before it comes. -/
def place (l : Layout) (m : Marking) (gone : Bool) (msg : Nat) : Int :=
  let line := [l.inlet l.load, l.vessel, l.outlet]
  let vIn := volume (l.inlet l.load)
  let vV := volume l.vessel
  let total := line.foldl (· + volume ·) 0
  let plug : Nat := if m.held.length ≥ l.cap then PARTED else 0
  match slotOf (slots l.cap m.held) msg, slotOf (lane m.waiting) msg with
  | some i, _ => vIn + vV - ((HEAD * contents VESSEL / 1000 : Nat) : Int) - i * A
  | none, some k => vIn - (((VALVE_AT + plug) * PIPE / 1000 : Nat) : Int) - k * A
  | none, none => if gone then total + A else 0

/-- Whether the vessel is full, so its valve is closed. -/
def closed (l : Layout) (m : Marking) : Bool := m.held.length ≥ l.cap

/-- A Queue snapshot over fixed pipework. Contents come from its evaluated cell. -/
def picture (l : Layout) (msgs : List Nat) (seen : List Nat)
    (m : Marking) : Picture :=
  let inlet := l.inlet l.load
  let line := [inlet, l.vessel, l.outlet]
  let names := ["in", "vessel", "out"]
  let units := msgs.flatMap fun msg =>
    let gone := seen.contains msg || m.answered == some msg
    let v := place l m gone msg
    ((line.zip names).zip (fronts line v)).map fun ((t, name), front) =>
      unitOf s!"m{msg}@{name}" t front
  let valveEnd : Int := (inlet.length : Int) - VALVE_AT
  let valve := if closed l m then
      [plugOf "valve" inlet (valveEnd - (PLUG : Int)) PLUG]
    else []
  let outEnd : Int := ((l.outLen + RIGHT : Nat) : Int) - 14000
  let takers := m.takers.zipIdx.flatMap fun (req, slot) =>
    hollowOf s!"t{req}" l.outlet (outEnd - (slot * unitLen PIPE : Nat))
  { marks := bodyOf "in" (into inlet true) (round := false) ++
      reducedOf "vessel" l.vessel (body PIPE) (body PIPE) ++
      bodyOf "out" (into l.outlet false) (round := false) ++ valve ++ units ++ takers }

/-- Cell snapshots projected onto one fixed structure, including transient replies. -/
def markings (l : Layout) (ms : List Marking) : List (List Mark) :=
  let msgs := (ms.flatMap fun m => m.held ++ m.waiting ++ m.answered.toList).eraseDups
  ms.zipIdx.map fun (m, i) =>
    let seen := ((ms.take i).flatMap fun before =>
      before.held ++ before.waiting ++ before.answered.toList).eraseDups
    (picture l msgs seen m).marks

/-- The Queue film reads evaluated cell snapshots, never invented trace store events. -/
def film (id : String) (l : Layout) (ms : List Marking) (beat : Nat := 1000) :
    Except String Whatwg.Html.SvgNode :=
  Board.film id l.W HEIGHT (markings l ms) beat

/-- The last Queue marking for reduced motion. -/
def endStill (l : Layout) (ms : List Marking) : Whatwg.Html.SvgNode :=
  Tools.View.Tube.still l.W HEIGHT ((markings l ms).getLastD [])

/-- A scene's evaluated cell snapshots and their words, with one layout for the whole run. -/
def record (sc : CellSheet.Scene) : Except String (Layout × List (String × Marking)) := do
  let fs ← sc.run
  let ms := fs.map marking
  let l := Layout.of sc.capacity (ms.foldl (fun a m => max a m.waiting.length) 0)
    (ms.foldl (fun a m => max a m.takers.length) 0)
  return (l, fs.zip ms |>.map fun (frame, m) => (frame.words, m))

-- The real Queue scene includes a full valve, a waiting offer, and a waiting taker.
#guard (record CellSheet.scene).toOption.any fun (l, fs) =>
  let ms := fs.map (·.2)
  ms.any (closed l) && ms.any (fun m => !m.waiting.isEmpty) &&
    ms.any (fun m => !m.takers.isEmpty) &&
    (markings l ms).all (fun marks => (marks.map (·.key)).eraseDups.length == marks.length)

-- Every repeated key keeps its centreline and every filled mark keeps its outline data.
#guard (record CellSheet.scene).toOption.all fun (l, fs) =>
  let frames := markings l (fs.map (·.2))
  let all := frames.flatten
  all.all fun m => all.all fun n =>
    m.key != n.key || (m.tube == n.tube && m.fill == n.fill &&
      (m.fill == .stroke || m.dash == n.dash))

end Tools.View.Tube.Queue
