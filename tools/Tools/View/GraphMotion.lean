import Tools.View.Graph
import Tools.View.GraphAttachmentMotion
import Tools.View.GraphSeparation

/-!
# Prepared graph transitions

Preparation retains ordered occurrences, first-key matches, exit selections, and entry transitions.
Sampling reads these data without rebuilding graph joins or target levels.
The legacy observation extends the sampler at `d6285ddf8` with explicit metadata.
Production motion couples explicit attachments and chooses a complete scene family when travel is refused.
The named tool laws serve concept 7 and R14 navigation.
Placement: `docs/research/2026-10-13-graph-attachment-motion-plan.md`, rows 334 (3) and 336 (8).
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
  KeyMap.firstBy Route.key rs

/-- Route lookup retains the reference's first-occurrence answer.
Helper of `prepare_legacySample_eq_legacyReference`, consumed by preparation. -/
theorem routeIndex_find (rs : List Route) (k : Key) :
    (routeIndex rs).get? k = rs.find? (fun r => r.key == k) := by
  exact KeyMap.get?_firstBy _ _ _

/-- Lookup presence answers the reference's membership test.
Helper of `prepare_legacySample_eq_legacyReference`, consumed by preparation. -/
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

/-- Why direct node-family travel uses the explicit endpoint fallback. -/
inductive FallbackReason where
  | changedNodeFamily
  | overshootingMovement
  | sweptBoxes (first second : Nat)
  deriving DecidableEq, Repr

/-- The inspected graph movement policy. -/
inductive Policy where
  | direct
  | endpointFamilies (reason : FallbackReason)
  deriving DecidableEq, Repr

/-- Full allocated node room, independent of instantaneous growth. -/
def allocatedBox (p : Placed) : Whatwg.Svg.Scene.IBox :=
  ⟨p.x, p.y, p.x + p.w, p.y + ROWH * BOXROWS⟩

/-- Node occurrences in their existing order. -/
def nodePlaces (l : Laid) : List Placed := l.placed.toList.filter (·.node.isSome)

/-- Conservative travel policy for node families.
A single endpoint family can grow at its fixed places under clipped growth. -/
def choosePolicy (c : Choreography) (a b : Laid) : Policy :=
  let old := nodePlaces a
  let next := nodePlaces b
  if old.isEmpty || next.isEmpty then .direct else
  let oldIx := Laid.Ix.of a
  let nextIx := Laid.Ix.of b
  let changed := old.any (fun p => !(nextIx.find p.key).any (·.node.isSome)) ||
    next.any (fun p => !(oldIx.find p.key).any (·.node.isSome))
  if changed then .endpointFamilies .changedNodeFamily else
  if c.move.ease == .spring || c.move.ease == .outBack then
    .endpointFamilies .overshootingMovement
  else
    let moves := old.filterMap fun p =>
      (nextIx.find p.key).map fun q => (allocatedBox p, allocatedBox q)
    match GraphSeparation.firstSweptOverlap moves with
    | none => .direct
    | some pair => .endpointFamilies (.sweptBoxes pair.first pair.second)

/-- Retained analysis of one graph transition.
Arbitrary records carry no agreement guarantee; `prepare` supplies the named law. -/
structure Prepared where
  places : List PlaceEntry
  routes : List RouteEntry
  gone : List Placed
  retracting : List Route
  move : Transition
  leave : Transition
  source : Laid
  target : Laid
  coherence : GraphAttachmentMotion.Prepared
  policy : Policy
  routingWidth : Int
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
Helper of `prepare_legacySample_eq_legacyReference`, consumed by entry-phase preparation. -/
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
    move := c.move.within, leave := c.leave.within, source := a, target := b
    coherence := GraphAttachmentMotion.prepare a b, policy := choosePolicy c a b
    routingWidth := max a.routeWidth b.routeWidth
    width := max a.width b.width, height := max a.height b.height }

/-- Sample the legacy display policy with explicit attachment and routing-span metadata. -/
def Prepared.legacySample (prepared : Prepared) (t : Nat) : Laid :=
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
    regions := prepared.target.regions, marks := prepared.target.marks
    attachments := prepared.target.attachments
    routingWidth := if 1000 ≤ t then prepared.target.routingWidth else some prepared.routingWidth }

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


/-- The frozen display observation extended with target incidence and a separate lane span. -/
def legacyReference (c : Choreography) (a b : Laid) (t : Nat) : Laid :=
  { reference c a b t with
    attachments := b.attachments
    routingWidth := if 1000 ≤ t then b.routingWidth else some (max a.routeWidth b.routeWidth) }

/-- Retained legacy sampling agrees with its explicitly extended reference.
This law does not describe the production attachment or separation policy. -/
theorem prepare_legacySample_eq_legacyReference (c : Choreography) (a b : Laid) (t : Nat) :
    (prepare c a b).legacySample t = legacyReference c a b t := by
  simp only [prepare, Prepared.legacySample, legacyReference, reference,
    Laid.Ix.find_of, routeIndex_has, List.map_map, targetY_of]
  rfl

/-- Clip any growth or reveal to the selected endpoint envelope. -/
def familyGrowth (value factor : Nat) : Nat := min 1000 (value * factor / 1000)

/-- Production growth stays inside its full endpoint allocation. -/
theorem family_growth_le (value factor : Nat) : familyGrowth value factor ≤ 1000 :=
  Nat.min_le_left _ _

/-- The painted node box, in the kit's integer box carrier. -/
def paintedBox (p : Placed) : Whatwg.Svg.Scene.IBox :=
  let box := Laid.boxBounds p
  ⟨box.x0, box.y0, box.x1, box.y1⟩

/-- A clipped nonnegative length stays within its allocated endpoint length.
Helper of `family_boxes_inside`, consumed by endpoint-family sampling. -/
private theorem scaledLength (length : Int) (growth : Nat) (hl : 0 ≤ length)
    (hg : growth ≤ 1000) :
    0 ≤ length * (growth : Int) / 1000 ∧ length * (growth : Int) / 1000 ≤ length := by
  have nonnegative : 0 ≤ (growth : Int) := Int.natCast_nonneg _
  have bounded : (growth : Int) ≤ 1000 := by omega
  exact ⟨Int.ediv_nonneg (Int.mul_nonneg hl nonnegative) (by decide),
    Int.ediv_le_of_le_mul (by decide) (Int.mul_le_mul_of_nonneg_left bounded hl)⟩

/-- Each scaled endpoint node box stays inside its allocated endpoint envelope.
Nonnegative width is a premise; route, mark, region, and text ink are outside the observation. -/
theorem family_boxes_inside (p : Placed) (factor : Nat) (width : 0 ≤ p.w) :
    (paintedBox { p with grow := familyGrowth p.grow factor }).Inside (allocatedBox p) := by
  have hw := scaledLength p.w (familyGrowth p.grow factor) width (family_growth_le _ _)
  have hh := scaledLength (ROWH * BOXROWS) (familyGrowth p.grow factor)
    (by decide) (family_growth_le _ _)
  simp only [paintedBox, Laid.boxBounds, allocatedBox, Whatwg.Svg.Scene.IBox.Inside]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Scale one complete scene family at its fixed endpoint places. -/
def family (l : Laid) (factor : Nat) : Laid :=
  { l with
    placed := l.placed.map fun p => { p with grow := familyGrowth p.grow factor }
    routes := l.routes.map fun r => r.withReveal (familyGrowth r.reveal factor) }

/-- Apply the inspected fallback to complete endpoint data, with an empty relocation phase. -/
def Prepared.fallbackSample (prepared : Prepared) (t : Nat) : Laid :=
  let l := match GraphSeparation.fallback t with
    | .old growth => { family prepared.source growth with
        routingWidth := some prepared.source.routeWidth }
    | .hidden => ({} : Laid)
    | .new growth => { family prepared.target growth with
        routingWidth := some prepared.target.routeWidth }
  { l with width := prepared.width, height := prepared.height }

/-- Sample coherent marks and ports while retaining the legacy route-reveal arithmetic. -/
def Prepared.directSample (prepared : Prepared) (t : Nat) : Laid :=
  let legacy := prepared.legacySample t
  let moved := GraphAttachmentMotion.progress (prepared.move.at t)
  let marks := prepared.coherence.marks.map fun mark => mark.sample moved
  let markTable := GraphAttachment.markTable marks
  let placed := legacy.placed.map fun point =>
    let point := GraphAttachmentMotion.applyDock prepared.coherence.docks markTable point
    { point with grow := familyGrowth point.grow 1000 }
  { legacy with
    placed := placed
    marks := marks.toArray
    regions := (prepared.coherence.regions.map fun region => region.sample moved).toArray
    attachments := prepared.coherence.attachments.toArray }

/-- Production sampling keeps complete scene families and returns the exact target at the endpoint. -/
def Prepared.sample (prepared : Prepared) (t : Nat) : Laid :=
  if 1000 ≤ t then prepared.target else
    match prepared.policy with
    | .direct => prepared.directSample t
    | .endpointFamilies _ => prepared.fallbackSample t

/-- The production endpoint is exact, independently of metadata validity or rest hypotheses. -/
theorem Prepared.sample_end (prepared : Prepared) : prepared.sample 1000 = prepared.target := by
  simp only [Prepared.sample, Nat.le_refl, if_true]

end GraphMotion
end Tools.View
