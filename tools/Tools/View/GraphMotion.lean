import Tools.View.Graph

/-!
# Prepared graph transitions

Preparation retains ordered occurrences, first-key matches, exit selections, and entry transitions.
Sampling reads these data without rebuilding graph joins or target levels.
The reference is the sampler at `d6285ddf8`.
The tool compatibility law serves concept 7 and R14 navigation.
Placement: `docs/research/2026-10-13-graph-motion-plan.md`, rows 334 (3) and 336 (8).
No runtime execution or speed bound follows from that law.
-/

namespace Tools.View

/-- **The update and the enter of a placed item**: a kept item moves `moved` per mille of the way
from its old place; a new one grows as far as `grow` says. -/
def placedAt (a : Laid) (moved : Int) (grow : Placed → Nat) (p : Placed) : Placed :=
  match a.find p.key with
  | some q => { p with x := lerp q.x p.x moved, y := lerp q.y p.y moved }
  | none => { p with grow := grow p }

/-- **The update and the enter of a route**: a kept route is drawn whole, and a new one as far as
`reveal` says. -/
def routeAt (a : Laid) (reveal : Route → Nat) (r : Route) : Route :=
  if a.routes.toList.any (·.key == r.key) then r else r.withReveal (reveal r)

namespace GraphMotion

/-- The first occurrence of each route key, retained as lookup data. -/
def routeIndex (rs : List Route) : KeyMap Key Route :=
  rs.foldr (fun r m => m.insert r.key r) {}

/-- Route lookup retains the reference's first-occurrence answer.
Helper of `prepare_sample_eq_reference`, consumed by preparation. -/
theorem routeIndex_find (rs : List Route) (k : Key) :
    (routeIndex rs).get? k = rs.find? (fun r => r.key == k) := by
  induction rs with
  | nil => exact KeyMap.get?_empty k
  | cons r rs ih =>
    rw [routeIndex, List.foldr_cons, KeyMap.get?_insert]
    change (if r.key = k then some r else (routeIndex rs).get? k) = _
    rw [ih, List.find?_cons]
    by_cases h : r.key = k
    · rw [if_pos h, show (r.key == k) = true from decide_eq_true h]
    · rw [if_neg h, show (r.key == k) = false from decide_eq_false h]

/-- Lookup presence answers the reference's membership test.
Helper of `prepare_sample_eq_reference`, consumed by preparation. -/
theorem routeIndex_has (rs : List Route) (k : Key) :
    ((routeIndex rs).get? k).isSome = rs.any (fun r => r.key == k) := by
  rw [routeIndex_find]
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    cases h : r.key == k with
    | false => simp only [List.find?_cons, List.any_cons, h, Bool.false_or, ih]
    | true => simp only [List.find?_cons, List.any_cons, h, Option.isSome_some, Bool.true_or]

/-- A target occurrence, its first old match, and its entry transition. -/
structure PlaceEntry where
  next : Placed
  old : Option Placed
  expand : Transition

/-- A target route occurrence, its old-key membership, and its entry transition. -/
structure RouteEntry where
  next : Route
  kept : Bool
  draw : Transition

/-- Retained analysis of one graph transition.
Arbitrary records carry no agreement guarantee; `prepare` supplies the named law. -/
structure Prepared where
  places : List PlaceEntry
  routes : List RouteEntry
  gone : List Placed
  retracting : List Route
  move : Transition
  leave : Transition
  target : Laid
  width : Int
  height : Int

/-- Sample one retained target placement. -/
def PlaceEntry.sample (entry : PlaceEntry) (moved : Int) (t : Nat) : Placed :=
  match entry.old with
  | some old => { entry.next with
      x := lerp old.x entry.next.x moved, y := lerp old.y entry.next.y moved }
  | none => { entry.next with grow := (entry.expand.at t).toNat }

/-- Sample one retained target route. -/
def RouteEntry.sample (entry : RouteEntry) (t : Nat) : Route :=
  if entry.kept then entry.next else entry.next.withReveal (entry.draw.at t).toNat

/-- Read the target height through an explicit prepared placement index. -/
def targetY (ix : Laid.Ix) : Route → Int
  | .down _ ks _ _ => ((ks.getLast?.bind ix.find).map (·.y)).getD 0
  | .back _ _ d _ _ => ((ix.find d).map (·.y)).getD 0
  | .loop _ k _ => ((ix.find k).map (·.y)).getD 0

/-- Indexed target heights answer the frozen endpoint lookup.
Helper of `prepare_sample_eq_reference`, consumed by entry-phase preparation. -/
theorem targetY_of (b : Laid) : targetY (Laid.Ix.of b) = (fun
    | .down _ ks _ _ => ((ks.getLast?.bind b.find).map (·.y)).getD 0
    | .back _ _ d _ _ => ((b.find d).map (·.y)).getD 0
    | .loop _ k _ => ((b.find k).map (·.y)).getD 0) := by
  have lookup : (Laid.Ix.of b).find = b.find := funext (Laid.Ix.find_of b)
  funext r
  cases r <;> simp only [targetY, lookup]

/-- Prepare all key matches and entry phases once, retaining source and target occurrence order.
The choreography is the exact sampler input; callers normalize it when required. -/
def prepare (c : Choreography) (a b : Laid) : Prepared :=
  let old := Laid.Ix.of a
  let next := Laid.Ix.of b
  let oldRoutes := routeIndex a.routes.toList
  let nextRoutes := routeIndex b.routes.toList
  let newBoxes := b.placed.toList.filter fun p => (old.find p.key).isNone
  let newRoutes := b.routes.toList.filter fun r => !((oldRoutes.get? r.key).isSome)
  let levels := ((newBoxes.map (·.y)) ++ (newRoutes.map (targetY next))).eraseDups.mergeSort (· ≤ ·)
  let slot := if levels.isEmpty then 0 else (1000 - c.enterFrom) / levels.length
  let start (y : Int) : Nat := c.enterFrom + levels.findIdx (· == y) * slot
  let drawAt (y : Int) : Transition :=
    ({ c.draw with duration := min c.draw.duration (slot * 45 / 100) } : Transition).after (start y)
  let expandAt (y : Int) : Transition :=
    ({ c.expand with duration := min c.expand.duration (slot * 60 / 100) } : Transition).after
      (start y + slot * 40 / 100)
  { places := b.placed.toList.map fun p => ⟨p, old.find p.key, expandAt p.y⟩
    routes := b.routes.toList.map fun r =>
      ⟨r, (oldRoutes.get? r.key).isSome, drawAt (targetY next r)⟩
    gone := a.placed.toList.filter fun p => (next.find p.key).isNone
    retracting := a.routes.toList.filter fun r => !((nextRoutes.get? r.key).isSome)
    move := c.move.within, leave := c.leave.within, target := b
    width := max a.width b.width, height := max a.height b.height }

/-- Sample retained data without rebuilding key membership or entry levels. -/
def Prepared.sample (prepared : Prepared) (t : Nat) : Laid :=
  let left := prepared.leave.at t
  let placed := prepared.places.map fun p => p.sample (prepared.move.at t) t
  let routes := prepared.routes.map fun r => r.sample t
  let gone := if 1000 ≤ t then [] else
    prepared.gone.map fun p => { p with grow := (1000 - left).toNat }
  let retracting := if 1000 ≤ t then [] else
    prepared.retracting.map fun r => r.withReveal (1000 - left).toNat
  { placed := (gone ++ placed).toArray, routes := (retracting ++ routes).toArray,
    width := if 1000 ≤ t then prepared.target.width else prepared.width,
    height := if 1000 ≤ t then prepared.target.height else prepared.height,
    regions := prepared.target.regions, marks := prepared.target.marks }

/-- The layout at the moment `t` of the step from `a` to `b`: the kept items move; level by level
from the top, each new edge draws and then the boxes at its end expand; the old items shrink and
retract. -/
def reference (c : Choreography) (a b : Laid) (t : Nat) : Laid :=
  let left := c.leave.within.at t
  let newBoxes := b.placed.toList.filter fun p => (a.find p.key).isNone
  let newRoutes := b.routes.toList.filter fun r => !(a.routes.toList.any (·.key == r.key))
  let targetY : Route → Int
    | .down _ ks _ _ => ((ks.getLast?.bind b.find).map (·.y)).getD 0
    | .back _ _ d _ _ => ((b.find d).map (·.y)).getD 0
    | .loop _ k _ => ((b.find k).map (·.y)).getD 0
  let levels := ((newBoxes.map (·.y)) ++ (newRoutes.map targetY)).eraseDups.mergeSort (· ≤ ·)
  let slot := if levels.isEmpty then 0 else (1000 - c.enterFrom) / levels.length
  let start (y : Int) : Nat := c.enterFrom + levels.findIdx (· == y) * slot
  let drawAt (y : Int) : Transition :=
    ({ c.draw with duration := min c.draw.duration (slot * 45 / 100) } : Transition).after (start y)
  let expandAt (y : Int) : Transition :=
    ({ c.expand with duration := min c.expand.duration (slot * 60 / 100) } : Transition).after
      (start y + slot * 40 / 100)
  let placed := b.placed.toList.map (placedAt a (c.move.within.at t) fun p => ((expandAt p.y).at t).toNat)
  let routes := b.routes.toList.map (routeAt a fun r => ((drawAt (targetY r)).at t).toNat)
  let gone := if 1000 ≤ t then [] else
    (a.placed.toList.filter fun p => (b.find p.key).isNone).map fun p => { p with grow := (1000 - left).toNat }
  let retracting := if 1000 ≤ t then [] else
    (a.routes.toList.filter fun r => !(b.routes.toList.any (·.key == r.key))).map fun r =>
      r.withReveal (1000 - left).toNat
  { placed := (gone ++ placed).toArray, routes := (retracting ++ routes).toArray,
    width := if 1000 ≤ t then b.width else max a.width b.width,
    height := if 1000 ≤ t then b.height else max a.height b.height, regions := b.regions,
    marks := b.marks }


/-- Retained graph sampling answers the frozen sampler on every finite input.
The observation includes duplicate keys, occurrence order, and out-of-range sample times.
Tool compatibility for R14; the frame exporter consumes this law. -/
theorem prepare_sample_eq_reference (c : Choreography) (a b : Laid) (t : Nat) :
    (prepare c a b).sample t = reference c a b t := by
  simp only [prepare, Prepared.sample, reference, Laid.Ix.find_of, routeIndex_has,
    List.map_map, targetY_of]
  rfl

end GraphMotion
end Tools.View
