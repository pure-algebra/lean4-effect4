import Tools.View.Living.Organism

/-!
# Tools.View.Living.Beat — one beat of the organism, sampled

A step of the run, drawn at a share of its beat: the join of the marking before and after, keyed
by identity (a message by itself, a request by its numeral), each part at its place between.

* A message travels from where it stood to where it stands inside the body, along its channels'
  axis, at the settling ease (`Ease.settle`: a critically damped spring, so it has weight and does
  not overshoot). Outside the vessel and its offer's room it distends the channel around it, single
  file, as a bolus does. One ease for all keeps the queue's order: no droplet passes another.
* The vessel's pressure moves from before to after, so it distends as messages arrive and draws in
  as they leave under the suction of waiting takers (`Organism.Body.vesselR`).
* A request that waits on through the beat stays; one that ends dissolves, its room's weight and
  its box's tone going to nothing, its numeral gone from the half; one that begins condenses from
  nothing. A taker has no room: it holds nothing.
* Each channel's core shows the beat's flux through the beat; its sheath moves from its
  conductivity before to after.
* Each channel's radius moves from its conductivity before to its conductivity after.

The end of the beat is the organism of the frame after (`Organism.picture`, at the share one),
so a reader who prefers reduced motion sees that frame. Each sample is a whole field and its
contours, so the studio's player plays the same frames.
-/

namespace Tools.View.Living.Beat
open Tools.View Tools.View.Living Tools.View.Living.Organism

/-- A value `t` per mille of the way from `a` to `b`. -/
def mix (a b t : Int) : Int := a + (b - a) * t / 1000

/-- A point `t` per mille along a shallow arc from `a` to `b`, lifted at its middle. -/
def along (a b : Int × Int) (lift t : Int) : Int × Int :=
  (mix a.1 b.1 t, mix a.2 b.2 t + lift * 4 * t * (1000 - t) / 1000000)

/-- Where a message stands before a beat, or enters from: the world on the left. -/
def startOf (before : Marking) (msg : Nat) : Int × Int := (before.pointOf msg).getD (8, CY)

/-- Where a message stands after a beat, or leaves to: the world on the right. -/
def endOf (after : Marking) (msg : Nat) : Int × Int := (after.pointOf msg).getD (W - 8, CY)

/-- The messages of a beat: every message of the marking before and after, once. -/
def messages (before after : Marking) : List Nat :=
  (before.messages ++ after.messages).foldl (fun out m => if out.contains m then out else out ++ [m]) []

/-- A request's presence at the share `e` of a beat, per mille: one through, rising if it
begins, falling if it ends. -/
def presence (was is_ : Bool) (e : Int) : Int :=
  match was, is_ with
  | true, true => 1000 | false, true => e | true, false => 1000 - e | false, false => 0

/-- **The organism at the share `p` per mille of the beat from `before` to `after`.** -/
def at_ (before after : Marking) (dsB dsA : List Nat) (p : Nat) : List (Keyed Call) :=
  let e := Ease.settle.at p
  let cap := after.capacity
  let msgs := messages before after
  -- a message travels inside the body, along its channels' axis: FIFO keeps the droplets apart
  let posOf (m : Nat) : Int × Int := along (startOf before m) (endOf after m) 0 e
  let offerIds := (before.offers.map (·.1) ++ after.offers.map (·.1)).eraseDups
  let takerIds := (before.takers ++ after.takers).eraseDups
  let offerAt (i : Nat) : Int × Int :=
    let j := ((after.offers.findIdx? (·.1 == i)).orElse fun _ => before.offers.findIdx? (·.1 == i)).getD 0
    (offerX j, CY)
  let takerAt (i : Nat) : Int × Int :=
    let j := ((after.takers.idxOf? i).orElse fun _ => before.takers.idxOf? i).getD 0
    (takerX cap j, CY)
  let offerP (i : Nat) := presence (before.offers.any (·.1 == i)) (after.offers.any (·.1 == i)) e
  let takerP (i : Nat) := presence (before.takers.contains i) (after.takers.contains i) e
  let offersNow := offerIds.filterMap fun i => if offerP i > 0 then some (offerAt i, offerP i) else none
  -- a message is in transit where it is neither in the vessel nor resting in an offer's room
  let inVessel (x : Int) := vx0 + 10 < x && x < vx1 cap - 10
  let resting (q : Int × Int) := offersNow.any fun (o, _) => (q.1 - o.1).natAbs < 18
  let pB := (before.body dsB).pressure
  let pA := (after.body dsA).pressure
  let ds : List Nat := (dsB.zip dsA).map fun (x, y) => (mix x y e).toNat
  let transit : List (Int × Int) := msgs.filterMap fun m =>
    let q := posOf m
    if inVessel q.1 || resting q then none else some q
  let b : Body := ⟨cap, ds, mix pB pA e, offersNow, transit⟩
  let room := (List.range cap).flatMap fun k => Organism.room s!"room/{k}" (slotX cap k) CY
  let requests := offerIds.flatMap (fun i => parked s!"offer/{i}" (offerAt i).1 CY i (700 * (offerP i).toNat / 1000)) ++
    takerIds.flatMap (fun i => parked s!"taker/{i}" (takerAt i).1 CY i (700 * (takerP i).toNat / 1000))
  let droplets := msgs.flatMap fun m => let (x, y) := posOf m; droplet s!"held/{m}" x y m
  body b.grid ++ cores cap (flux before after) ++ room ++ requests ++ droplets

/-- **A beat sampled**: the organism at `n + 1` evenly spaced shares, the first at the start and
the last at the end. -/
def samples (before after : Marking) (dsB dsA : List Nat) (n : Nat) : List (Nat × List (Keyed Call)) :=
  (List.range (n + 1)).map fun k => let p := 1000 * k / n; (p, at_ before after dsB dsA p)

end Tools.View.Living.Beat
