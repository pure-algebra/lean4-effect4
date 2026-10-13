import Tools.View.Living.Organism

/-!
# Tools.View.Living.Beat — one beat of the organism, sampled

A step of the run, drawn at a share of its beat: the join of the marking before and after, keyed
by identity (a message by itself, a request by its numeral), each part at its place between.

* A message travels from where it stood to where it stands inside the body, along its channels'
  axis, at the settling ease (`Ease.settle`: a critically damped spring, so it has weight and does
  not overshoot). Its swelling of the field travels with it, so a channel swells around a message
  passing through it, as a vessel does around a bolus, and the vessel bulges where a message
  arrives and relaxes where one leaves. One ease for all keeps the queue's order: no droplet
  passes another.
* A request that waits on through the beat stays; one that ends dissolves, its source's weight
  and its box's tone going to nothing, its numeral gone from the half; one that begins condenses
  from nothing.
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
  -- the requests that wait, keyed by their numerals, with their place and presence
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
  let ds := (dsB.zip dsA).map fun (a, b) => (mix a b e).toNat
  let srcs : List Soft.Source :=
    [Soft.Source.segment (vx0 + 30) CY (vx1 cap - 30) CY 46] ++
    ((channelEnds cap).zip ds).map (fun (((ax, ay), (bx, by_)), d) =>
      Soft.Source.segment ax ay bx by_ (max 6 (channelR d))) ++
    [Soft.Source.point inletX CY 22 450, Soft.Source.point (outletX cap) CY 22 450] ++
    msgs.map (fun m => let (x, y) := posOf m; Soft.Source.point x y 26 450) ++
    offerIds.map (fun i => let (x, y) := offerAt i; Soft.Source.point x y 30 (900 * (offerP i).toNat / 1000)) ++
    takerIds.map (fun i => let (x, y) := takerAt i; Soft.Source.point x y 30 (900 * (takerP i).toNat / 1000))
  let g := Soft.Grid.of (-MARGIN) 0 STEP (((W + 2 * MARGIN) / STEP).toNat + 1) ((H / STEP).toNat + 1) srcs
  let room := (List.range cap).flatMap fun k => Organism.room s!"room/{k}" (slotX cap k) CY
  let boxes (key : String) (at_ : Int × Int) (n : Nat) (pres : Int) : List (Keyed Call) :=
    if pres ≤ 0 then [] else
    [⟨key, .shape .ink (700 * pres.toNat / 1000)
        (Grow.ring (1000 * (at_.1 - 17)) (1000 * (at_.2 - 17)) 34000 34000 12000 UNIT_W)⟩,
     ⟨key, .cells (at_.1 - 17) (at_.2 - 22) (toString n).length (toString n)⟩].filter fun c =>
      match c.call with | .cells .. => pres ≥ 500 | _ => true
  let requests := offerIds.flatMap (fun i => boxes s!"offer/{i}" (offerAt i) i (offerP i)) ++
    takerIds.flatMap (fun i => boxes s!"taker/{i}" (takerAt i) i (takerP i))
  let droplets := msgs.flatMap fun m => let (x, y) := posOf m; droplet s!"held/{m}" x y m
  body g ++ room ++ requests ++ droplets

/-- **A beat sampled**: the organism at `n + 1` evenly spaced shares, the first at the start and
the last at the end. -/
def samples (before after : Marking) (dsB dsA : List Nat) (n : Nat) : List (Nat × List (Keyed Call)) :=
  (List.range (n + 1)).map fun k => let p := 1000 * k / n; (p, at_ before after dsB dsA p)

end Tools.View.Living.Beat
