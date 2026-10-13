import Tools.View.CellSheet
import Tools.View.Living.Physarum
import Tools.View.Living.Soft

/-!
# Tools.View.Living.Organism — the Queue as a living network (decisions row 367; the note
`docs/research/2026-10-13-living-quantities/`)

The Queue's numbers drawn as one organism. Its places stand in the order units flow: the world,
the inlet where offers wait, the vessel that holds the messages, the outlet where takers wait, and
the world again. The places are the module's roles, as data (`places`); they move to
`Library/Queue/View.lean` with VS-3. Everything else is folded from the run:

1. **The marking.** Each frame's cell (`CellSheet.frames`, the Queue's own step terms evaluated)
   read into its places: the messages held, the offers waiting with what they carry, the takers
   waiting.
2. **The flows of a step.** The keyed join of the marking before and after: a message is keyed by
   itself, and it moves from the place it stood in to the place it stands in, or out to the world
   when the step answers it. It crosses every channel between the two, so the flux of a channel in
   a beat is the number of messages that crossed it.
3. **The channels' life.** Each channel's conductivity is the Physarum fold of its fluxes
   (`Living.Physarum`): it thickens with use and withers when idle. Its width follows the
   conductivity's fourth root, since a tube's conductivity is `π r⁴ / 8η` (Hagen–Poiseuille, in
   Tero et al.'s equation 1).
4. **The body.** The vessel, the channels and the units that wait are sources of one soft field
   (`Living.Soft`): the membrane is the band between two of its levels, so channels meet the
   vessel in organic collars, the vessel swells with what it holds, and the inlet swells where
   offers press.

On the body stand the units: a droplet for each message (filled: kept), a hollow ring for each
slot of room (promised), a parked request's hollow box for each offer and each taker that waits,
and a fine arc for each message that moved in the beat.
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

/-! ## The body -/

/-- The picture's room, its axis, and where the places stand. -/
def W : Int := 640
def H : Int := 140
def CY : Int := 70
def PITCH : Int := 40
def vx0 : Int := 250
def vx1 (cap : Nat) : Int := vx0 + PITCH * cap + 24
def inletX : Int := vx0 - 80
def outletX (cap : Nat) : Int := vx1 cap + 80

/-- A slot's centre, the front first, nearest the outlet. -/
def slotX (cap k : Nat) : Int := vx1 cap - 32 - PITCH * k

/-- The fourth root, in thousandths, of a conductivity in thousandths. -/
def root4 (d : Nat) : Nat := Grow.isqrt (Grow.isqrt (d * 1000000000))

/-- **A channel's radius of influence** from its conductivity: its visible half-width grows from
two pixels with the fourth root of the conductivity (Hagen–Poiseuille), and the field's level
stands at about 0.63 of the radius. -/
def channelR (d : Nat) : Nat := (2000 + 8 * root4 d) * 1600 / 1000000

/-- The ends of each channel. -/
def channelEnds (cap : Nat) : List ((Int × Int) × (Int × Int)) :=
  [((0, CY), (inletX, CY)), ((inletX, CY), (vx0 + 16, CY)),
   ((vx1 cap - 16, CY), (outletX cap, CY)), ((outletX cap, CY), (W, CY))]

/-- Where the `j`-th offer and the `j`-th taker wait, the front nearest the vessel. -/
def offerX (j : Nat) : Int := inletX + 18 - 46 * j
def takerX (cap j : Nat) : Int := outletX cap - 18 + 46 * j

/-- **The sources of the body's field**: the vessel, the channels at their conductivities, a
swelling for each message held, and one for each request that waits. -/
def sources (m : Marking) (ds : List Nat) : List Soft.Source :=
  let cap := m.capacity
  [Soft.Source.segment (vx0 + 30) CY (vx1 cap - 30) CY 46] ++
  ((channelEnds cap).zip ds).map (fun (((ax, ay), (bx, by_)), d) =>
    Soft.Source.segment ax ay bx by_ (max 6 (channelR d))) ++
  [Soft.Source.point inletX CY 22 450, Soft.Source.point (outletX cap) CY 22 450] ++
  (List.range m.held.length).map (fun k => Soft.Source.point (slotX cap k) CY 26 450) ++
  (List.range m.offers.length).map (fun j => Soft.Source.point (offerX j) CY 30 900) ++
  (List.range m.takers.length).map (fun j => Soft.Source.point (takerX cap j) CY 30 900)

/-- The grid of the body: two pixels a sample, reaching `MARGIN` past each side of the picture,
beyond any channel's reach, so the field is zero on its border. -/
def STEP : Nat := 2
def MARGIN : Int := 48

/-- The body's level, in thousandths of the field: its membrane. A low level lets the sources'
fields blend widely, so the necks between them are soft. -/
def OUTER : Int := 220

/-- The lamellae's levels inside the membrane, each a fainter line. -/
def LAMELLAE : List Int := [430, 640]

/-- The width of the membrane and of a lamella, in thousandths of a pixel. -/
def MEMBRANE_W : Int := 1400
def LAMELLA_W : Int := 900

/-- **The body of a field**: a faint fill inside the membrane, the membrane as one line, and the
lamellae inside it, all contours of the one field. -/
def body (g : Soft.Grid) : List (Keyed Call) :=
  [⟨"body", .shape .ink 45 (g.paths OUTER 4)⟩, ⟨"membrane", .shape .ink 560 (g.lines OUTER MEMBRANE_W 4)⟩] ++
  LAMELLAE.zipIdx.map fun (lv, i) => ⟨s!"lamella/{i}", .shape .ink (200 - 70 * i) (g.lines lv LAMELLA_W 4)⟩

/-! ## The units -/

/-- The width of every unit's outline, in thousandths of a pixel: one material with the body. -/
def UNIT_W : Int := 1200

/-- A disc of radius `r` about a point, as one closed path in thousandths. -/
def disc (x y r : Int) : List Cubic := Grow.roundRect (1000 * (x - r)) (1000 * (y - r)) (2000 * r) (2000 * r) (1000 * r)

/-- A numeral centred on a point, in the data face. -/
def numeral (key : Key) (x y : Int) (s : String) : Keyed Call :=
  ⟨key, .cells (x - CELL * s.length / 2) (y + 5) s.length s⟩

/-- **A message held**: a filled droplet with its value. -/
def droplet (key : Key) (x y : Int) (v : Nat) : List (Keyed Call) :=
  [⟨key, .shape .ink 330 [disc x y 13]⟩, numeral key x y (toString v)]

/-- **Room**: a hollow ring in the rule's tone. -/
def room (key : Key) (x y : Int) : List (Keyed Call) :=
  [⟨key, .shape .ink 300 (Grow.ring (1000 * (x - 13)) (1000 * (y - 13)) 26000 26000 13000 UNIT_W)⟩]

/-- **A request that waits**: the parked request's hollow box, its numeral above it. -/
def parked (key : Key) (x y : Int) (n : Nat) : List (Keyed Call) :=
  [⟨key, .shape .ink 700 (Grow.ring (1000 * (x - 17)) (1000 * (y - 17)) 34000 34000 12000 UNIT_W)⟩,
   ⟨key, .cells (x - 17) (y - 22) (toString n).length (toString n)⟩]

/-- **What moved in the beat**: a fine arc from where a message stood to where it stands. -/
def arc (key : Key) (a b : Int × Int) (lift : Int) : Keyed Call :=
  let mid := ((a.1 + b.1) / 2, (a.2 + b.2) / 2 + lift)
  ⟨key, .curve .ink ⟨a, ((a.1 + mid.1) / 2, mid.2), ((b.1 + mid.1) / 2, mid.2), b⟩ 1⟩

/-- Where a message stands in a marking, as a point of the picture. -/
def Marking.pointOf (m : Marking) (msg : Nat) : Option (Int × Int) :=
  match m.held.idxOf? msg with
  | some k => some (slotX m.capacity k, CY)
  | none =>
    match m.offers.findIdx? (·.2.contains msg) with
    | some j => some (offerX j, CY)
    | none => if m.answered == some msg then some (W - 30, CY) else none

/-- **The units of a marking**, and the arcs of the beat that led to it. -/
def units (before : Option Marking) (m : Marking) : List (Keyed Call) :=
  let cap := m.capacity
  let slots := (List.range cap).flatMap fun k =>
    match m.held[k]? with
    | some v => droplet s!"held/{v}" (slotX cap k) CY v
    | none => room s!"room/{k}" (slotX cap k) CY
  let offers := m.offers.zipIdx.flatMap fun ((i, rest), j) =>
    parked s!"offer/{i}" (offerX j) CY i ++ (rest.take 1).flatMap fun v => droplet s!"held/{v}" (offerX j) CY v
  let takers := m.takers.zipIdx.flatMap fun (i, j) =>
    parked s!"taker/{i}" (takerX cap j) CY i ++
      (if m.woken.contains i then [⟨s!"taker/{i}", .shape .ink 1000 [disc (takerX cap j) CY 4]⟩] else [])
  let out := m.answered.toList.flatMap fun v => droplet s!"held/{v}" (W - 30) CY v
  let arcs := match before with
    | none => []
    | some b => m.messages.filterMap fun msg =>
      match b.pointOf msg, m.pointOf msg with
      | some p, some q => if p == q then none else some (arc s!"moved/{msg}" (p.1, p.2 - 15) (q.1, q.2 - 15) (-26))
      | none, some q => some (arc s!"moved/{msg}" (q.1 - 60, q.2 - 15) (q.1, q.2 - 15) (-18))
      | _, _ => none
  slots ++ offers ++ takers ++ out ++ arcs

/-- **One frame of the organism**: the membrane, the faint body inside it, then the units. -/
def picture (before : Option Marking) (m : Marking) (ds : List Nat) : List (Keyed Call) :=
  -- the grid reaches past the picture's sides, where the channels leave it, so every contour closes
  body (Soft.Grid.of (-MARGIN) 0 STEP (((W + 2 * MARGIN) / STEP).toNat + 1) ((H / STEP).toNat + 1) (sources m ds)) ++
    units before m

/-- **Every frame of the scene**: its words, its marking and its picture. -/
def scene : Except String (List (String × Marking × List (Keyed Call))) := do
  let fs ← frames
  let ms := fs.map marking
  let ds := conductivities ms
  return (fs.zip (ms.zip ds)).zipIdx.map fun ((f, m, d), i) =>
    (f.words, m, picture (if i == 0 then none else ms[i - 1]?) m d)

end Tools.View.Living.Organism
