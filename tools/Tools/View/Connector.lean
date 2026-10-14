import Tools.View.Organic

/-!
# One perimeter for an organic connector

`Connector.body` reserves vertical necks before sampling the body.
The paired sides include the flares, with shared integer neck handles.
`Connector.stroke` writes one perimeter, with two transverse caps.

Placement: concept `initial-algebras-folds`, R14 live authoring.
These tool helpers serve `Laid.organicCalls` after its caller migration.
The placement brief is `docs/research/2026-10-13-connector-plan.md`.
The observation is integer cubic controls, not scheduler meaning.
No law here establishes global absence of intersections or exact circles.
-/

namespace Tools.View.Connector

open Tools.View

/-- A vertical surface, relative to the route endpoint, in thousandths. -/
structure Dock where
  offset : Int
  radius : Int
  deriving DecidableEq, BEq, Hashable, Repr, Inhabited

/-- Two open sides in the same forward direction, including any flares. -/
structure Body where
  edges : List (Cubic × Cubic) := []
  deriving DecidableEq, Repr, Inhabited

/-- The forward left side. Cardinality agrees with the right side by construction. -/
def Body.left (b : Body) : List Cubic := b.edges.map Prod.fst

/-- The forward right side. -/
def Body.right (b : Body) : List Cubic := b.edges.map Prod.snd

/-- A reserved neck: its surface point and effective radius. -/
structure Neck where
  surface : Grow.P
  radius : Int
  deriving DecidableEq, Repr, Inhabited

/-- The integer quarter-arc handle. Tiny radii become zero before this step. -/
def handle (r : Int) : Int := r * Grow.KAPPA / 1000

/-- The first nonzero endpoint control gives the terminal vertical room.
Duplicate straight-line controls fall through to the chord. -/
def startReach (c : Cubic) : Int :=
  let q := if c.p1 == c.p0 then (if c.p2 == c.p0 then c.p3 else c.p2) else c.p1
  max 0 (q.2 - c.p0.2)

/-- The terminal room at the other endpoint, with the same chord fallback. -/
def endReach (c : Cubic) : Int :=
  let q := if c.p2 == c.p3 then (if c.p1 == c.p3 then c.p0 else c.p1) else c.p2
  max 0 (c.p3.2 - q.2)

/-- Bound the radius by terminal room and the available surface drop. -/
def radius (requested room drop : Int) : Int :=
  let r := max 0 (min requested (min room (drop / 4)))
  if r < 2 then 0 else r

/-- Reserve the neck on the first endpoint's vertical axis. -/
def reserveStart (n : Neck) (c : Cubic) : Cubic :=
  let p := (n.surface.1, n.surface.2 + n.radius)
  { c with p0 := p, p1 := (p.1, max p.2 c.p1.2) }

/-- Reserve the last neck on the last endpoint's vertical axis. -/
def reserveEnd (n : Neck) (c : Cubic) : Cubic :=
  let p := (n.surface.1, n.surface.2 - n.radius)
  { c with p3 := p, p2 := (p.1, min p.2 c.p2.2) }

/-- Change only the first and last elements. A singleton receives both changes. -/
def ends {α : Type} (first last : α → α) (xs : List α) : List α :=
  xs.mapIdx fun i x =>
    let x := if i = 0 then first x else x
    if i + 1 = xs.length then last x else x

/-- Sample already-scaled cubics without another grid conversion. -/
def samples (cs : List Cubic) : List (Grow.P × Grow.P) :=
  match cs with
  | [] => []
  | c :: rest => Grow.sampleAlong 8 c true ++ rest.flatMap fun c => Grow.sampleAlong 8 c false

/-- Leave room for the exact neck handle before the nearest interior sample. -/
def shoulder (source target : Option Neck) (p : Grow.P) : Bool :=
  (match source with
    | some n => n.surface.2 + n.radius + 3 * handle n.radius < p.2
    | none => true) &&
  (match target with
    | some n => p.2 < n.surface.2 - n.radius - 3 * handle n.radius
    | none => true)

/-- Keep both endpoints and samples outside the reserved shoulders. -/
def bodySamples (cs : List Cubic) (source target : Option Neck) : List (Grow.P × Grow.P) :=
  let ss := samples cs
  match ss.head?, ss.getLast? with
  | some a, some z =>
    let a := if source.isSome then (a.1, (0, 1)) else a
    let z := if target.isSome then (z.1, (0, 1)) else z
    a :: ((ss.drop 1).dropLast.filter fun x => shoulder source target x.1) ++ [z]
  | _, _ => []

/-- Fix a docked side's neck width independently of noise and endpoint normals. -/
def neckPoint (sign hw : Int) (down : Bool) (n : Neck) : Grow.P :=
  (n.surface.1 - sign * hw, n.surface.2 + (if down then n.radius else -n.radius))

/-- An open side retains the original noise and tip calculations away from docks. -/
def pairedPoints (seed : Nat) (o : Organic) (w : Int) (tip : Bool)
    (ss : List (Grow.P × Grow.P)) (source target : Option Neck) : List (Grow.P × Grow.P) :=
  let lens := Grow.runningLengths ss
  let S := lens.getLast?.getD 0
  let qs := (ss.zip lens).map fun x =>
    (Grow.sidePoint seed o (w / 2) S tip 0 1 x, Grow.sidePoint seed o (w / 2) S tip 7 (-1) x)
  let neck (down : Bool) (n : Neck) :=
    (neckPoint 1 (w / 2) down n, neckPoint (-1) (w / 2) down n)
  ends (fun p => source.map (neck true) |>.getD p)
    (fun p => target.map (neck false) |>.getD p) qs

/-- Interpolate both sides from one list of paired samples. -/
def throughFrom : (Grow.P × Grow.P) → List (Grow.P × Grow.P) → List (Cubic × Cubic)
  | a, b :: c :: rest =>
    let d := rest.head?.getD c
    (Grow.segmentThrough a.1 b.1 c.1 d.1, Grow.segmentThrough a.2 b.2 c.2 d.2) ::
      throughFrom b (c :: rest)
  | _, _ => []

/-- Paired open Catmull–Rom chains. -/
def through (qs : List (Grow.P × Grow.P)) : List (Cubic × Cubic) :=
  match qs with
  | [] => []
  | a :: _ => throughFrom a qs

/-- Pin the first side handle to the source flare's outgoing handle. -/
def pinStart (n : Neck) (c : Cubic) : Cubic :=
  if n.radius = 0 then c else { c with p1 := (c.p0.1, c.p0.2 + handle n.radius) }

/-- Pin the last side handle to the target flare's incoming handle. -/
def pinEnd (n : Neck) (c : Cubic) : Cubic :=
  if n.radius = 0 then c else { c with p2 := (c.p3.1, c.p3.2 - handle n.radius) }

/-- The source flare is an open side, from its surface lip to its neck. -/
def startArc (sign hw : Int) (n : Neck) : Cubic :=
  let neck := neckPoint sign hw true n
  let lip := (neck.1 - sign * n.radius, n.surface.2)
  ⟨lip, (lip.1 + sign * handle n.radius, lip.2),
    (neck.1, neck.2 - handle n.radius), neck⟩

/-- The target flare runs from its neck to its surface lip. -/
def endArc (sign hw : Int) (n : Neck) : Cubic :=
  let neck := neckPoint sign hw false n
  let lip := (neck.1 - sign * n.radius, n.surface.2)
  ⟨neck, (neck.1, neck.2 + handle n.radius),
    (lip.1 + sign * handle n.radius, lip.2), lip⟩

/-- A paired flare has one segment on each side. Zero radius adds no segment. -/
def flare (arc : Int → Int → Neck → Cubic) (hw : Int) (n : Neck) : List (Cubic × Cubic) :=
  if n.radius = 0 then [] else [(arc 1 hw n, arc (-1) hw n)]

/-- A side joins its reserved flares without an overlaid contour. -/
def paired (seed : Nat) (o : Organic) (w : Int) (tip : Bool)
    (ss : List (Grow.P × Grow.P)) (source target : Option Neck) : Body :=
  let curves := through (pairedPoints seed o w tip ss source target)
  let curves := ends
    (fun c => source.map (fun n => (pinStart n c.1, pinStart n c.2)) |>.getD c)
    (fun c => target.map (fun n => (pinEnd n c.1, pinEnd n c.2)) |>.getD c) curves
  ⟨(source.map (flare startArc (w / 2)) |>.getD []) ++ curves ++
    (target.map (flare endArc (w / 2)) |>.getD [])⟩

/-- Construct paired sides. An empty, zero-width, or non-descending request draws no body.
A partial request ignores the target dock. -/
def body (seed : Nat) (o : Organic) (w : Int) (cs : List Cubic) (tip : Bool)
    (source target : Option Dock) : Body :=
  let cs := cs.map (Cubic.scale 1000)
  let target := if tip then none else target
  match cs.head?, cs.getLast? with
  | some a, some z =>
    let sy := a.p0.2 + (source.map (·.offset) |>.getD 0)
    let ty := z.p3.2 + (target.map (·.offset) |>.getD 0)
    let drop := ty - sy
    if w ≤ 0 || drop ≤ 0 then {} else
      let source := source.map fun d =>
        Neck.mk (a.p0.1, sy) (radius d.radius (startReach a - d.offset) drop)
      let target := target.map fun d =>
        Neck.mk (z.p3.1, ty) (radius d.radius (endReach z + d.offset) drop)
      let cs := ends (fun c => source.map (fun n => reserveStart n c) |>.getD c)
        (fun c => target.map (fun n => reserveEnd n c) |>.getD c) cs
      let ss := bodySamples cs source target
      paired seed o w tip ss source target
  | _, _ => {}

/-- Reverse a side segment by swapping its existing integer controls. -/
def reverse (c : Cubic) : Cubic := ⟨c.p3, c.p2, c.p1, c.p0⟩

/-- One closed perimeter. Reversal swaps controls instead of resampling a side. -/
def Body.outline (b : Body) : List Cubic :=
  match b.edges.head?, b.edges.getLast? with
  | some a, some z => b.right ++ [Grow.line z.2.p3 z.1.p3] ++
    b.left.reverse.map reverse ++ [Grow.line a.1.p0 a.2.p0]
  | _, _ => []

/-- The two deliberate transverse caps, indexed in the emitted perimeter. -/
def capSegments (cs : List Cubic) : List Nat :=
  if cs.length < 4 then [] else
    let n := (cs.length - 2) / 2
    [n, 2 * n + 1]

/-- All intended side joins, indexed after the preceding cubic.
This list never filters according to a tangent test. -/
def smoothJoins (cs : List Cubic) : List Nat :=
  if cs.length < 4 then [] else
    let n := (cs.length - 2) / 2
    List.range (n - 1) ++ (List.range (n - 1)).map (n + 1 + ·)

/-- One solid connector perimeter, in thousandths. Docks are relative to route endpoints. -/
def stroke (seed : Nat) (o : Organic) (w : Int) (cs : List Cubic) (tip : Bool)
    (source target : Option Dock) : List Cubic :=
  (body seed o w cs tip source target).outline

/-! The following local laws serve the shared-handle observation in the placement brief.
Finite controls check their composition in the actual emitted perimeter. -/

/-- Adjacent forward Catmull–Rom segments have exactly equal integer tangent handles. -/
theorem catmull_shared (a b c d e : Grow.P) :
    (Grow.segmentThrough a b c d).p3.1 - (Grow.segmentThrough a b c d).p2.1 =
      (Grow.segmentThrough b c d e).p1.1 - (Grow.segmentThrough b c d e).p0.1 ∧
    (Grow.segmentThrough a b c d).p3.2 - (Grow.segmentThrough a b c d).p2.2 =
      (Grow.segmentThrough b c d e).p1.2 - (Grow.segmentThrough b c d e).p0.2 := by
  simp only [Grow.segmentThrough]
  constructor <;> omega

/-- A nonzero source flare and its pinned body use the same vertical handle. -/
theorem pinStart_handle (n : Neck) (c : Cubic) (h : n.radius ≠ 0) :
    (pinStart n c).p1.1 - c.p0.1 = 0 ∧
    (pinStart n c).p1.2 - c.p0.2 = handle n.radius := by
  simp only [pinStart, h, if_false]
  constructor <;> omega

/-- A nonzero target flare and its pinned body use the same vertical handle. -/
theorem pinEnd_handle (n : Neck) (c : Cubic) (h : n.radius ≠ 0) :
    c.p3.1 - (pinEnd n c).p2.1 = 0 ∧
    c.p3.2 - (pinEnd n c).p2.2 = handle n.radius := by
  simp only [pinEnd, h, if_false]
  constructor <;> omega

end Tools.View.Connector
