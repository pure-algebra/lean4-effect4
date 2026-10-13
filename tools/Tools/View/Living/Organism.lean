import Tools.View.CellSheet
import Tools.View.Living.Physarum
import Tools.View.Living.Soft
import Tools.View.Living.Phyllotaxis

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

/-- A droplet's radius at rest, and the least and the most it may take when a place is fitted to
its room; the cell-free layer around a unit (Fåhræus): the room a unit keeps from a wall. -/
def REST_UNIT : Int := 9
def MIN_UNIT : Int := 5
def CLEARANCE : Int := 4

/-- The vessel's compliance (the share of its rest radius it gains under the pressure of a full
vessel: Laplace with Hooke), and the least share it keeps under suction. -/
def COMPLIANCE : Int := 220
def COLLAPSE : Int := 620

/-- The largest capacity drawn as a lane; above it, a disc (Gemini's review, question 2). -/
def LANE_MAX : Nat := 8

/-- The step of a parked request, a neck between a waiting room and the vessel, the least run of a
channel to the world, and the margin above and below the body. -/
def REQ_STEP : Int := 44
def NECK : Int := 60
def WORLD : Int := 56
def MARGIN_Y : Int := 34

/-- The field's level is at about 0.69 of a source's radius of influence at the body's level, so a
visible radius `r` asks a source of radius `r · 1000 / 686`. -/
def reach (visible : Int) : Nat := (visible * 1000 / 686).toNat

/-- The fourth root, in thousandths, of a conductivity in thousandths. -/
def root4 (d : Nat) : Nat := Grow.isqrt (Grow.isqrt (d * 1000000000))

/-- **A channel's sheath** from its conductivity: its visible half-width grows from two pixels with
the conductivity's fourth root (Hagen–Poiseuille). -/
def channelR (d : Nat) : Nat := reach ((2000 + 7 * (root4 d : Int)) / 1000)

/-! ## The plan: the body's form and measures, from its capacity and its room -/

/-- **A place's form**: a lane of slots, or a disc whose units stand as a sunflower's florets. -/
inductive Form where
  | lane | disc
  deriving DecidableEq, Repr

/-- **The plan of a body**: its form, the radius of a unit, how many units a mark stands for, its
room, and where its places stand. Every frame and every beat of a run share one plan, so nothing
of the body moves between frames but what the run moves. -/
structure Plan where
  cap : Nat
  form : Form
  unit : Int
  per : Nat
  W : Int
  H : Int
  CY : Int
  vc : Int
  vhalf : Int
  inletX : Int
  outletX : Int
  zoneIn : Int
  zoneOut : Int
  pitch : Int
  spacing : Nat
deriving Repr

/-- The slot pitch of a lane at a unit's radius: the unit, the layer each side, and a gap. -/
def lanePitch (unit : Int) : Int := 2 * unit + 2 * CLEARANCE + 8

/-- The length of a lane vessel. -/
def laneLength (cap : Nat) (unit : Int) : Int := lanePitch unit * cap + 26

/-- The marks of a disc and Vogel's spacing for them, at a unit's radius (thousandths). -/
def discSpacing (marks : Nat) (unit : Int) : Nat :=
  Phyllotaxis.spacing (2000 * (unit + CLEARANCE)).toNat marks

/-- **The plan of a body** for a capacity, the most offers and takers that wait at once over the
run, and the width it may take. A lane takes the largest unit, from the rest size down to the
least, that fits the width; if none fits, or the capacity is above `LANE_MAX`, the place is a
disc, its radius by the room law (`Phyllotaxis.radius`). Above `Phyllotaxis.MAX_MARKS` units a
mark stands for several. -/
def Plan.of (cap maxOffers maxTakers : Nat) (room : Int := 900) : Plan :=
  let zoneIn := REQ_STEP * (max 1 maxOffers)
  let zoneOut := REQ_STEP * (max 1 maxTakers)
  let around := 2 * WORLD + zoneIn + zoneOut + 2 * NECK
  let fits (u : Int) := around + laneLength cap u ≤ room
  let laneUnit := ((List.range (REST_UNIT - MIN_UNIT + 1).toNat).map (fun (i : Nat) => REST_UNIT - i)).find? fits
  let place (form : Form) (unit : Int) (per : Nat) (vhalf : Int) (spacing : Nat) (pitch : Int) : Plan :=
    let H := 2 * vhalf + 2 * MARGIN_Y + 24
    let inletX := WORLD + zoneIn / 2
    let vc := WORLD + zoneIn + NECK + vhalf
    let outletX := vc + vhalf + NECK + zoneOut / 2
    { cap, form, unit, per, W := outletX + zoneOut / 2 + WORLD, H, CY := H / 2, vc, vhalf, inletX, outletX,
      zoneIn, zoneOut, pitch, spacing }
  match laneUnit, decide (cap ≤ LANE_MAX) with
  | some u, true => place .lane u 1 (laneLength cap u / 2) 0 (lanePitch u)
  | _, _ =>
    let per := Phyllotaxis.perMark cap
    let marks := (cap + per - 1) / per
    let unit := if marks > 34 then MIN_UNIT + 2 else REST_UNIT
    let c := discSpacing marks unit
    let r : Int := (Phyllotaxis.radius c marks (unit * 1000).toNat (CLEARANCE * 1000).toNat : Int) / 1000
    place .disc unit per r c 0

/-- The vessel's two ends across. -/
def Plan.vx0 (p : Plan) : Int := p.vc - p.vhalf
def Plan.vx1 (p : Plan) : Int := p.vc + p.vhalf

/-- **A slot's place by its age**, `a` counting from the newest unit held: in a lane the newest
stands at the back and the front nearest the outlet; in a disc the newest stands at the centre and
the oldest at the rim (Vogel, as the florets of a sunflower). `n` is the number of units held. -/
def Plan.slotAt (p : Plan) (n a : Nat) : Int × Int :=
  match p.form with
  | .lane => (p.vx1 - 30 - p.pitch * ((n - 1 - a : Nat) : Int), p.CY)
  | .disc =>
    let d := ((Phyllotaxis.directions (a + 1)).getLast?).getD ⟨Phyllotaxis.UNIT, 0⟩
    let q := Phyllotaxis.placeOf p.spacing a d
    (p.vc + q.1 / 1000, p.CY + q.2 / 1000)

/-- The place of the `k`-th message held, the front first, when `n` are held. -/
def Plan.heldAt (p : Plan) (n k : Nat) : Int × Int :=
  match p.form with
  | .lane => (p.vx1 - 30 - p.pitch * k, p.CY)
  | .disc => p.slotAt n (n - 1 - k)

/-- The places of the room: the slots no message holds, when `n` are held. -/
def Plan.roomAt (p : Plan) (n : Nat) : List (Int × Int) :=
  match p.form with
  | .lane => (List.range p.cap).filterMap fun k => if k < n then none else some (p.vx1 - 30 - p.pitch * k, p.CY)
  | .disc => ((List.range ((p.cap + p.per - 1) / p.per)).filter (· ≥ (n + p.per - 1) / p.per)).map fun a =>
      let d := ((Phyllotaxis.directions (a + 1)).getLast?).getD ⟨Phyllotaxis.UNIT, 0⟩
      let q := Phyllotaxis.placeOf p.spacing a d
      (p.vc + q.1 / 1000, p.CY + q.2 / 1000)

/-- The ends of each channel. -/
def Plan.channelEnds (p : Plan) : List ((Int × Int) × (Int × Int)) :=
  [((0, p.CY), (p.inletX, p.CY)), ((p.inletX, p.CY), (p.vx0 + 14, p.CY)),
   ((p.vx1 - 14, p.CY), (p.outletX, p.CY)), ((p.outletX, p.CY), (p.W, p.CY))]

/-- Where the `j`-th offer and the `j`-th taker wait, the front nearest the vessel. -/
def Plan.offerX (p : Plan) (j : Nat) : Int := p.inletX + p.zoneIn / 2 - REQ_STEP / 2 - REQ_STEP * j
def Plan.takerX (p : Plan) (j : Nat) : Int := p.outletX - p.zoneOut / 2 + REQ_STEP / 2 + REQ_STEP * j

/-- Where an answered message leaves. -/
def Plan.outX (p : Plan) : Int := p.W - 26

/-- **What the body's field reads**: its plan, the conductivities, the vessel's transmural pressure
in thousandths of a full vessel (negative under suction), each waiting offer's place and
presence, and the messages in transit through a channel. -/
structure Body where
  plan : Plan
  ds : List Nat
  pressure : Int
  offers : List ((Int × Int) × Int) := []
  transit : List (Int × Int) := []

/-- **The vessel's radius of influence** under its transmural pressure: the thin elastic tube's
distension, linear in the pressure, never below the share it keeps under suction. A lane's rest is
its unit, the layer and a margin of wall; a disc's is its radius by the room law. -/
def Body.vesselR (b : Body) : Nat :=
  let rest : Int := match b.plan.form with
    | .lane => b.plan.unit + CLEARANCE + 14
    | .disc => b.plan.vhalf + 4
  reach (max (rest * COLLAPSE / 1000) (rest + rest * COMPLIANCE * b.pressure / 1000000))

/-- **The sources of the body's field**: the vessel at its distension, the channels at their
sheaths, the room of each waiting offer, and each message in transit. Nothing else: a place with
nothing in it has no field of its own. -/
def Body.sources (b : Body) : List Soft.Source :=
  let p := b.plan
  let vessel := match p.form with
    | .lane => Soft.Source.segment (p.vx0 + 30) p.CY (p.vx1 - 30) p.CY b.vesselR
    | .disc => Soft.Source.point p.vc p.CY b.vesselR
  [vessel] ++
  (p.channelEnds.zip b.ds).map (fun (((ax, ay), (bx, by_)), d) =>
    Soft.Source.segment ax ay bx by_ (max (reach 3) (channelR d))) ++
  b.offers.map (fun ((x, y), pres) => Soft.Source.point x y (reach (17 + CLEARANCE)) (pres.toNat)) ++
  b.transit.map (fun (x, y) => Soft.Source.point x y (reach (p.unit + CLEARANCE)) 1000)

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
  Soft.Grid.of (-MARGIN) 0 STEP (((b.plan.W + 2 * MARGIN) / STEP).toNat + 1) ((b.plan.H / STEP).toNat + 1) b.sources

/-- **A channel's core: what it carries in this step**, lit along its axis, as wide as its share of
the flux: the cores of a split add as the flows do. -/
def cores (p : Plan) (fluxes : List Nat) : List (Keyed Call) :=
  (p.channelEnds.zip fluxes).zipIdx.filterMap fun ((((ax, _), (bx, _)), q), k) =>
    if q == 0 then none else
    let half : Int := 700 + 600 * q
    some ⟨s!"core/{k}", .shape .ink 650 [Grow.roundRect (1000 * ax) (1000 * p.CY - half) (1000 * (bx - ax)) (2 * half) half]⟩

/-! ## The units -/

/-- The width of every unit's outline, in thousandths of a pixel: one material with the body. -/
def UNIT_W : Int := 1200

/-- A disc of radius `r` about a point, as one closed path in thousandths. -/
def disc (x y r : Int) : List Cubic := Grow.roundRect (1000 * (x - r)) (1000 * (y - r)) (2000 * r) (2000 * r) (1000 * r)

/-- **A message held**: a solid droplet (kept), its value above it where the room allows. -/
def droplet (p : Plan) (key : Key) (x y : Int) (v : Nat) (tone : Nat := 1000) : List (Keyed Call) :=
  let s := toString v
  [⟨key, .shape .ink tone [disc x y p.unit]⟩] ++
  (if p.form == .disc then [] else [⟨key, .cells (x - CELL * s.length / 2) (y - p.unit - 5) s.length s⟩])

/-- **Room**: a hollow ring (promised). -/
def room (p : Plan) (key : Key) (x y : Int) : List (Keyed Call) :=
  let u := p.unit
  [⟨key, .shape .ink 340 (Grow.ring (1000 * (x - u)) (1000 * (y - u)) (2000 * u) (2000 * u) (1000 * u) UNIT_W)⟩]

/-- **A request that waits**: the parked request's hollow box, its numeral under its lower corner,
clear of the value of the message it may hold. -/
def parked (key : Key) (x y : Int) (n : Nat) (tone : Nat := 700) : List (Keyed Call) :=
  [⟨key, .shape .ink tone (Grow.ring (1000 * (x - 17)) (1000 * (y - 17)) 34000 34000 12000 UNIT_W)⟩] ++
  (if tone < 350 then [] else [⟨key, .cells (x - 17) (y + 31) (toString n).length (toString n)⟩])

/-- Where a message stands in a marking, as a point of the picture. -/
def Marking.pointOf (p : Plan) (m : Marking) (msg : Nat) : Option (Int × Int) :=
  match m.held.idxOf? msg with
  | some k => some (p.heldAt m.held.length k)
  | none =>
    match m.offers.findIdx? (·.2.contains msg) with
    | some j => some (p.offerX j, p.CY)
    | none => if m.answered == some msg then some (p.outX, p.CY) else none

/-- **The body of a marking at rest**: its pressure from what it holds and what waits for it. -/
def Marking.body (p : Plan) (m : Marking) (ds : List Nat) : Body :=
  { plan := p, ds,
    pressure := ((m.held.length : Int) - m.takers.length) * 1000 / max 1 m.capacity
    offers := (List.range m.offers.length).map fun j => ((p.offerX j, p.CY), 1000)
    transit := (m.answered.toList).map fun _ => (p.outX, p.CY) }

/-- **The units of a marking.** -/
def units (p : Plan) (m : Marking) : List (Keyed Call) :=
  let n := m.held.length
  let held := m.held.zipIdx.flatMap fun (v, k) => let (x, y) := p.heldAt n k; droplet p s!"held/{v}" x y v
  let rooms := (p.roomAt n).zipIdx.flatMap fun ((x, y), k) => room p s!"room/{k}" x y
  let offers := m.offers.zipIdx.flatMap fun ((i, rest), j) =>
    parked s!"offer/{i}" (p.offerX j) p.CY i ++ (rest.take 1).flatMap fun v => droplet { p with form := .lane } s!"held/{v}" (p.offerX j) p.CY v
  let takers := m.takers.zipIdx.flatMap fun (i, j) =>
    parked s!"taker/{i}" (p.takerX j) p.CY i ++
      (if m.woken.contains i then [⟨s!"taker/{i}", .shape .ink 1000 [disc (p.takerX j) p.CY 3]⟩] else [])
  let out := m.answered.toList.flatMap fun v => droplet { p with form := .lane } s!"held/{v}" p.outX p.CY v
  rooms ++ held ++ offers ++ takers ++ out

/-- **One frame of the organism**: the body, the cores of the step that led to it, then the units. -/
def picture (p : Plan) (before : Option Marking) (m : Marking) (ds : List Nat) : List (Keyed Call) :=
  body (m.body p ds).grid ++ (match before with | some b => cores p (flux b m) | none => []) ++ units p m

/-- **A scene drawn**: its plan, from the run's capacity and the most offers and takers that wait at
once, then each frame: its words, its marking and its picture. -/
def run (sc : CellSheet.Scene) : Except String (Plan × List (String × Marking × List (Keyed Call))) := do
  let fs ← sc.run
  let ms := fs.map marking
  let ds := conductivities ms
  let plan := Plan.of sc.capacity (ms.foldl (fun a m => max a m.offers.length) 0)
    (ms.foldl (fun a m => max a m.takers.length) 0)
  return (plan, (fs.zip (ms.zip ds)).zipIdx.map fun ((f, m, d), i) =>
    (f.words, m, picture plan (if i == 0 then none else ms[i - 1]?) m d))

end Tools.View.Living.Organism
