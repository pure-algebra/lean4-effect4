import Tools.View.CellSheet
import Tools.View.Living.Physarum
import Tools.View.Living.Soft

/-!
# Tools.View.Living.Organism — the Queue as a living network, drawn by the laws of tissue
(decisions row 367; `docs/research/2026-10-13-living-quantities/`, the anatomy note)

The Queue's numbers drawn as one organism. Its places stand in the order units flow: the world,
the inlet where offers wait, the vessel that holds the messages, the outlet where takers wait, and
the world again. The places are the module's roles, as data; they move to
`Library/Queue/View.lean` with VS-3. Everything else is folded from the run, and every measure of
the body is a law of physiology applied to a quantity of the Queue, not a choice of taste:

1. **The marking.** Each frame's cell (`CellSheet.frames`, the Queue's own step terms evaluated)
   read into its places.
2. **The flux of a step.** The keyed join of two markings: a message moves from the place it stood
   in to the place it stands in, crossing every channel between; a channel's flux in a beat is the
   number of messages that crossed it.
3. **A channel's sheath: its history** (Physarum, Tero et al. 2010). Its conductivity is the fold
   of its fluxes, and its radius the conductivity's fourth root (Hagen–Poiseuille,
   `D = π r⁴ / 8η`). **Its core: this step.** A lit core as wide as the beat's flux, so history and
   the present read apart.
4. **The vessel's distension: its pressure** (Laplace's law with Hooke's, a thin elastic tube:
   `ΔR / R = (R / E h) ΔP`). The transmural pressure is the messages held less the takers
   waiting, over the capacity: a full vessel distends, and an empty one under the suction of
   waiting takers draws in. The deficit shows on the body, never as a swelling.
5. **Room** (the cell-free layer of the Fåhræus effect). A waiting offer holds a message, so it
   takes room at the inlet: its size and the layer around it. A waiting taker holds nothing and
   takes none: it docks at the outlet as a receptor. A message in a channel narrower than itself
   distends the channel around it, single file, as a bolus does.
6. **The wall** (Laplace's law at a constant wall stress, `σ = P r / h`). A wall is as thick as its
   tube is wide, by one ratio; the local radius is read from the field's slope at the wall.

The membrane and the lamellae inside it are contours of the one soft field (`Living.Soft`), so
every line of the body comes from one structure. On the body stand the units: a solid droplet for
each message held (kept), its value above it; a hollow ring for each slot of room (promised); a
parked request's hollow box for each offer and each taker that waits.
-/

namespace Tools.View.Living.Organism
open Tools.View Tools.View.Living
open Effect4 Effect4.Program
open Tools.View.CellSheet (Frame frames)

abbrev Val := Effect4.Store.Val

/-! ## The places and the marking -/

/-- **The places, in the order units flow** (the Queue's roles). -/
inductive Place where
  | world | inlet | vessel | outlet | gone
  deriving DecidableEq, Repr

def Place.rank : Place → Nat
  | .world => 0 | .inlet => 1 | .vessel => 2 | .outlet => 3 | .gone => 4

/-- The channels: between each place and the next. -/
def CHANNELS : Nat := 4

/-- **A marking**: what each place holds. A message is its value; a request its numeral. -/
structure Marking where
  capacity : Nat
  held : List Nat
  offers : List (Nat × List Nat)
  takers : List Nat
  woken : List Nat := []
  answered : Option Nat := none

/-- A field of a record value. -/
def field (v : Val) (name : String) : Option Val := (Machine.Record.entries v).bind (·.lookup name)

def nats : Val → List Nat
  | .list xs => xs.filterMap fun | .nat n => some n | _ => none
  | _ => []

def handleOf : Option Val → Option Nat
  | some (.handle _ n) => some n
  | _ => none

def records : Option Val → List Val
  | some (.list xs) => xs
  | _ => []

/-- **A cell read into its places**, with what the step's answer gave out and woke. -/
def marking (f : Frame) : Marking :=
  let c := f.cell
  let answer : Option Val := f.answer.map (·.2)
  let parts : List Val := match answer with | some (Store.Val.list xs) => xs | _ => []
  { capacity := match field c "cap" with | some (.nat n) => n | _ => 0
    held := ((field c "msgs").map nats).getD []
    offers := (records (field c "offers")).filterMap fun o =>
      (handleOf (field o "id")).map fun i => (i, ((field o "rest").map nats).getD [])
    takers := (records (field c "takers")).filterMap fun t => handleOf (field t "id")
    woken := (records (parts.getLast?)).filterMap fun t => handleOf (field t "id")
    answered := match parts.head? with | some (.some (.nat m)) => some m | _ => none }

/-- Where a message stands in a marking. -/
def Marking.placeOf (m : Marking) (msg : Nat) : Place :=
  if m.held.contains msg then .vessel
  else if m.offers.any (·.2.contains msg) then .inlet
  else if m.answered == some msg then .gone
  else .world

/-- Every message a marking names. -/
def Marking.messages (m : Marking) : List Nat :=
  m.held ++ m.offers.flatMap (·.2) ++ m.answered.toList

/-- **The flux of each channel in a beat**: the messages of the join of two markings, each
counted on every channel between where it stood and where it stands. -/
def flux (before after : Marking) : List Nat :=
  let moved := after.messages.filterMap fun msg =>
    let a := (before.placeOf msg).rank
    let b := (after.placeOf msg).rank
    if a < b then some (a, b) else none
  (List.range CHANNELS).map fun k => (moved.filter fun (a, b) => a ≤ k && k < b).length

/-- The rate of the adaptation: four tenths of the way toward the gain, each beat. -/
def RATE : Nat := 400

/-- **The conductivity of each channel at each frame**: the Physarum fold of its fluxes, zero
at the first frame. -/
def conductivities (ms : List Marking) : List (List Nat) :=
  let beats := (ms.zip (ms.drop 1)).map fun (a, b) => flux a b
  let perChannel := (List.range CHANNELS).map fun k =>
    0 :: Physarum.history RATE (beats.map fun fl => fl.getD k 0 * Physarum.ONE)
  (List.range ms.length).map fun i => perChannel.map (·.getD i 0)

/-! ## The tissue: the constants of the laws -/

/-- The picture's room, its axis, and where the places stand. -/
def W : Int := 640
def H : Int := 130
def CY : Int := 65
def PITCH : Int := 34
def vx0 : Int := 270
def vx1 (cap : Nat) : Int := vx0 + PITCH * cap + 26
def inletX : Int := vx0 - 110
def outletX (cap : Nat) : Int := vx1 cap + 92

/-- A slot's centre, the front first, nearest the outlet. -/
def slotX (cap k : Nat) : Int := vx1 cap - 30 - PITCH * k

/-- A droplet's radius, and the cell-free layer around a unit (Fåhræus): the room a unit keeps
from a wall. -/
def DROP_R : Int := 9
def CLEARANCE : Int := 4

/-- The vessel's radius of influence at rest, its compliance (the share of the rest radius it
gains under the pressure of a full vessel: Laplace with Hooke), and the least share it keeps under
suction. -/
def VESSEL_R : Nat := 40
def COMPLIANCE : Int := 220
def COLLAPSE : Int := 620

/-- The field's level is at about 0.69 of a source's radius of influence at the body's level, so a
visible radius `r` asks a source of radius `r · 1000 / 686`. -/
def reach (visible : Int) : Nat := (visible * 1000 / 686).toNat

/-- The fourth root, in thousandths, of a conductivity in thousandths. -/
def root4 (d : Nat) : Nat := Grow.isqrt (Grow.isqrt (d * 1000000000))

/-- **A channel's sheath** from its conductivity: its visible half-width grows from two pixels with
the conductivity's fourth root (Hagen–Poiseuille). -/
def channelR (d : Nat) : Nat := reach ((2000 + 7 * (root4 d : Int)) / 1000)

/-- The ends of each channel. -/
def channelEnds (cap : Nat) : List ((Int × Int) × (Int × Int)) :=
  [((0, CY), (inletX, CY)), ((inletX, CY), (vx0 + 14, CY)),
   ((vx1 cap - 14, CY), (outletX cap, CY)), ((outletX cap, CY), (W, CY))]

/-- Where the `j`-th offer and the `j`-th taker wait, the front nearest the vessel. -/
def offerX (j : Nat) : Int := inletX + 12 - 44 * j
def takerX (cap j : Nat) : Int := outletX cap - 12 + 44 * j

/-- **What the body's field reads**: the conductivities, the vessel's transmural pressure in
thousandths of a full vessel (negative under suction), each waiting offer's place and presence,
and the messages in transit through a channel. -/
structure Body where
  cap : Nat
  ds : List Nat
  pressure : Int
  offers : List ((Int × Int) × Int) := []
  transit : List (Int × Int) := []

/-- **The vessel's radius** under its transmural pressure: the thin elastic tube's distension,
linear in the pressure, never below the share it keeps under suction. -/
def Body.vesselR (b : Body) : Nat :=
  let r : Int := VESSEL_R
  (max (r * COLLAPSE / 1000) (r + r * COMPLIANCE * b.pressure / 1000000)).toNat

/-- **The sources of the body's field**: the vessel at its distension, the channels at their
sheaths, the room of each waiting offer, and each message in transit. Nothing else: a place with
nothing in it has no field of its own. -/
def Body.sources (b : Body) : List Soft.Source :=
  [Soft.Source.segment (vx0 + 30) CY (vx1 b.cap - 30) CY b.vesselR] ++
  ((channelEnds b.cap).zip b.ds).map (fun (((ax, ay), (bx, by_)), d) =>
    Soft.Source.segment ax ay bx by_ (max (reach 3) (channelR d))) ++
  b.offers.map (fun ((x, y), pres) => Soft.Source.point x y (reach (17 + CLEARANCE)) (pres.toNat)) ++
  b.transit.map (fun (x, y) => Soft.Source.point x y (reach (DROP_R + CLEARANCE)) 1000)

/-- The grid of the body: two pixels a sample, reaching `MARGIN` past each side of the picture,
beyond any channel's reach, so the field is zero on its border. -/
def STEP : Nat := 2
def MARGIN : Int := 48

/-- The body's level: its membrane. A low level lets the sources' fields blend widely, so the necks
are soft. -/
def OUTER : Int := 220

/-- The lamellae's levels inside the membrane, each a fainter line. -/
def LAMELLAE : List Int := [430, 640]

/-- **The wall's width from the field's slope** (Laplace at a constant wall stress): at the body's
level the slope across a source of radius `R` is about `1321 / R` thousandths a pixel, so the
local radius is `1321 / slope`, and the wall is that radius over `WALL_RATIO`, between a fine and
a heavy line. -/
def WALL_RATIO : Int := 11
def wallOf (ratioScale : Int) (slope : Int) : Int :=
  max 800 (min 3000 (686 * 1321 / max 1 slope / WALL_RATIO * ratioScale / 1000))

/-- **The body of a field**: a faint fill inside the membrane, the membrane as a wall as thick as
its tube is wide, and the lamellae inside it, all contours of the one field. -/
def body (g : Soft.Grid) : List (Keyed Call) :=
  [⟨"body", .shape .ink 45 (g.paths OUTER 4)⟩, ⟨"membrane", .shape .ink 520 (g.walls OUTER (wallOf 1000) 4)⟩] ++
  LAMELLAE.zipIdx.map fun (lv, i) => ⟨s!"lamella/{i}", .shape .ink (190 - 70 * i) (g.walls lv (wallOf 450) 4)⟩

/-- The body's field on its grid. -/
def Body.grid (b : Body) : Soft.Grid :=
  Soft.Grid.of (-MARGIN) 0 STEP (((W + 2 * MARGIN) / STEP).toNat + 1) ((H / STEP).toNat + 1) b.sources

/-- **A channel's core: what it carries in this step**, lit along its axis, as wide as its flux. -/
def cores (cap : Nat) (fluxes : List Nat) (shareOfBeat : Int := 1000) : List (Keyed Call) :=
  ((channelEnds cap).zip fluxes).zipIdx.filterMap fun ((((ax, _), (bx, _)), q), k) =>
    if q == 0 then none else
    let half : Int := 700 + 600 * q
    some ⟨s!"core/{k}", .shape .ink (650 * shareOfBeat / 1000).toNat
      [Grow.roundRect (1000 * ax) (1000 * CY - half) (1000 * (bx - ax)) (2 * half) half]⟩

/-! ## The units -/

/-- The width of every unit's outline, in thousandths of a pixel: one material with the body. -/
def UNIT_W : Int := 1200

/-- A disc of radius `r` about a point, as one closed path in thousandths. -/
def disc (x y r : Int) : List Cubic := Grow.roundRect (1000 * (x - r)) (1000 * (y - r)) (2000 * r) (2000 * r) (1000 * r)

/-- A label of data centred over a point. -/
def labelOver (key : Key) (x y : Int) (s : String) : Keyed Call :=
  ⟨key, .cells (x - CELL * s.length / 2) (y - DROP_R - 5) s.length s⟩

/-- **A message held**: a solid droplet (kept), its value above it. -/
def droplet (key : Key) (x y : Int) (v : Nat) (tone : Nat := 1000) : List (Keyed Call) :=
  [⟨key, .shape .ink tone [disc x y DROP_R]⟩, labelOver key x y (toString v)]

/-- **Room**: a hollow ring (promised). -/
def room (key : Key) (x y : Int) : List (Keyed Call) :=
  [⟨key, .shape .ink 340 (Grow.ring (1000 * (x - DROP_R)) (1000 * (y - DROP_R)) (2000 * DROP_R) (2000 * DROP_R) (1000 * DROP_R) UNIT_W)⟩]

/-- **A request that waits**: the parked request's hollow box, its numeral under its lower corner,
clear of the value of the message it may hold. -/
def parked (key : Key) (x y : Int) (n : Nat) (tone : Nat := 700) : List (Keyed Call) :=
  [⟨key, .shape .ink tone (Grow.ring (1000 * (x - 17)) (1000 * (y - 17)) 34000 34000 12000 UNIT_W)⟩] ++
  (if tone < 350 then [] else [⟨key, .cells (x - 17) (y + 31) (toString n).length (toString n)⟩])

/-- Where a message stands in a marking, as a point of the picture. -/
def Marking.pointOf (m : Marking) (msg : Nat) : Option (Int × Int) :=
  match m.held.idxOf? msg with
  | some k => some (slotX m.capacity k, CY)
  | none =>
    match m.offers.findIdx? (·.2.contains msg) with
    | some j => some (offerX j, CY)
    | none => if m.answered == some msg then some (W - 26, CY) else none

/-- **The body of a marking at rest**: its pressure from what it holds and what waits for it. -/
def Marking.body (m : Marking) (ds : List Nat) : Body :=
  { cap := m.capacity, ds,
    pressure := ((m.held.length : Int) - m.takers.length) * 1000 / max 1 m.capacity
    offers := (List.range m.offers.length).map fun j => ((offerX j, CY), 1000)
    transit := (m.answered.toList).map fun _ => (W - 26, CY) }

/-- **The units of a marking.** -/
def units (m : Marking) : List (Keyed Call) :=
  let cap := m.capacity
  let slots := (List.range cap).flatMap fun k =>
    match m.held[k]? with
    | some v => droplet s!"held/{v}" (slotX cap k) CY v
    | none => room s!"room/{k}" (slotX cap k) CY
  let offers := m.offers.zipIdx.flatMap fun ((i, rest), j) =>
    parked s!"offer/{i}" (offerX j) CY i ++ (rest.take 1).flatMap fun v => droplet s!"held/{v}" (offerX j) CY v
  let takers := m.takers.zipIdx.flatMap fun (i, j) =>
    parked s!"taker/{i}" (takerX cap j) CY i ++
      (if m.woken.contains i then [⟨s!"taker/{i}", .shape .ink 1000 [disc (takerX cap j) CY 3]⟩] else [])
  let out := m.answered.toList.flatMap fun v => droplet s!"held/{v}" (W - 26) CY v
  slots ++ offers ++ takers ++ out

/-- **One frame of the organism**: the body, the cores of the step that led to it, then the units. -/
def picture (before : Option Marking) (m : Marking) (ds : List Nat) : List (Keyed Call) :=
  body (m.body ds).grid ++ (match before with | some b => cores m.capacity (flux b m) | none => []) ++ units m

/-- **Every frame of the scene**: its words, its marking and its picture. -/
def scene : Except String (List (String × Marking × List (Keyed Call))) := do
  let fs ← frames
  let ms := fs.map marking
  let ds := conductivities ms
  return (fs.zip (ms.zip ds)).zipIdx.map fun ((f, m, d), i) =>
    (f.words, m, picture (if i == 0 then none else ms[i - 1]?) m d)

end Tools.View.Living.Organism
