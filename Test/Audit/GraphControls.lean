import Tools.View.GraphSeparation
import Tools.View.GraphLayout
import Tools.View.GraphMotion
import Tools.View.GraphRegions

/-!
# Controls of the graph layout's laws (from the retired probes, 2026-10-18)

The graph probes of `tools/view/` were built by nothing and named by no command, and the view's
cleanup removed them. Where a probe held the only control of a law of `tools/Tools/View/`, that
control stands here as one line (decisions row 301): a red case that shows why a premise stands,
or where the law stops. Each line names its law and the probe it comes from, at the base of the
cleanup (`git:4a81cc034:tools/view/<probe>.lean`). The probes' readers, their finite evaluations
and their timings went with them.
-/

namespace Test.Audit.GraphControls

open Tools.View Whatwg.Svg.Scene

/-! ## `GraphSeparation` (`git:4a81cc034:tools/view/GraphSeparationProbe.lean`) -/

-- control: `movingEnvelope_contains` needs the origin between the two endpoint origins. An
-- origin that overshoots both lies outside the envelope.
#guard ¬(⟨30, 0, 40, 10⟩ : IBox).Inside (GraphSeparation.movingEnvelope ⟨0, 0, 10, 10⟩ ⟨20, 0, 30, 10⟩)

-- control: `firstFrameOverlap_none_iff` speaks of the sampled frames only. Two boxes that swap
-- places are apart in both endpoint frames, and their swept envelopes collide between them.
#guard (GraphSeparation.firstFrameOverlap [[⟨0, 0, 10, 10⟩, ⟨100, 0, 110, 10⟩],
    [⟨100, 0, 110, 10⟩, ⟨0, 0, 10, 10⟩]]).isNone &&
  (GraphSeparation.firstSweptOverlap
    [(⟨0, 0, 10, 10⟩, ⟨100, 0, 110, 10⟩), (⟨100, 0, 110, 10⟩, ⟨0, 0, 10, 10⟩)]).isSome

/-! ## `GraphCheck` and `PaintBounds` (`git:4a81cc034:tools/view/GraphLibraryProbe.lean`) -/

/-- A node keyed as the layout keys a long edge's point at rank 1 (`Graph.pointKey`). -/
def collision : Graph :=
  { nodes := #[⟨"a", "A", "", false⟩, ⟨"long@1", "B", "", false⟩, ⟨"c", "C", "", false⟩],
    edges := #[⟨"ab", 0, 1⟩, ⟨"bc", 1, 2⟩, ⟨"long", 0, 2⟩] }

-- control: `input_iff` admits the input, and `laid_iff` refuses its layout. The point that the
-- long edge passes through takes the key of a node, so input admission is no allocation admission.
#guard (GraphCheck.input collision).isOk &&
  match GraphLayout.checked collision with
  | .error r => r.site == .placed && r.field == .key && r.reason == .duplicateKey
  | .ok _ => false

/-- One node with an edge to itself. -/
def selfLoop : Graph := { nodes := #[⟨"a", "A", "", false⟩], edges := #[⟨"loop", 0, 0⟩] }

-- control: the routing width alone cuts a self-loop. The loop's control hull passes the routing
-- width, and the canvas that `reserveCanvas` widens (`reserveCanvas_notShrink`) holds it.
#guard match selfLoop.layout.placed[0]? with
  | some p => selfLoop.layout.routeWidth < p.x + p.w + 2 * LOOP_REACH &&
      p.x + p.w + 2 * LOOP_REACH ≤ selfLoop.layout.width
  | none => false

/-! ## `GraphMotion` (`git:4a81cc034:tools/view/GraphTransitionProbe.lean`) -/

/-- Linear motion: a move and a leave of one second, entries after the move. -/
def linear : Choreography :=
  { move := { duration := 1000, ease := .linear },
    leave := { duration := 1000, ease := .linear }, enterFrom := 1700,
    draw := { delay := 1300, duration := 0 }, expand := { delay := 10, duration := 0 } }

/-- A box of a node at `x` on the first rank. -/
def box (key : Key) (x : Int) : Placed :=
  { key, x, y := 0, w := 32, node := some { key, line1 := key } }

/-- Two points that become the two boxes of `swapped`, in each other's places. -/
def points : Laid :=
  { placed := #[{ key := "left", x := 0, y := 0, w := 16 }, { key := "right", x := 80, y := 0, w := 16 }],
    marks := #[.bar "source-mark" 0 32 0],
    regions := #[{ key := "source-region", name := "source", x := 0, y := 0, w := 32, h := 48 }],
    width := 140, height := 80, routingWidth := some 120 }

/-- Two boxes, each where the other point stood. -/
def swapped : Laid :=
  { placed := #[box "left" 80, box "right" 0], marks := #[.bar "target-mark" 80 112 0],
    regions := #[{ key := "target-region", name := "target", x := 80, y := 0, w := 32, h := 48 }],
    width := 160, height := 80, routingWidth := some 130 }

-- control: `prepare_legacySample_eq_legacyReference` keeps the legacy picture, and that picture
-- draws two boxes over each other halfway; the production sample keeps them apart.
#guard !((GraphMotion.prepare linear points swapped).legacySample 500).boxesApart &&
  ((GraphMotion.prepare linear points swapped).sample 500).boxesApart

/-! ## `GraphRegions` (`git:4a81cc034:tools/view/GraphRegionsProbe.lean`) -/

/-- An edge with its own identity. -/
structure Edge where
  id : Nat
  src : Nat
  dst : Nat

/-- One region whose two members no edge joins: `1` and `2` of the vertices `0` to `3`. -/
def apart : GraphRegions.Membership :=
  { regions := #[⟨"group", none⟩], owner := #[none, some 0, some 0, none] }

/-- An edge into the region's first member, and one out of its second. -/
def cutEdges : Array Edge := #[⟨0, 0, 1⟩, ⟨1, 2, 3⟩]

-- control: `project_provenance` keeps each edge's origin, and no more. Collapsed, the region joins
-- a displayed path from `0` to `3` (shown at index 2) that no original path matches.
#guard !(cutEdges.any fun a => a.src == 0 && cutEdges.any fun b => a.dst == b.src && b.dst == 3) &&
  match (GraphRegions.prepare apart #[true]).toOption.bind
      (fun p => (GraphRegions.project p cutEdges Edge.src Edge.dst).toOption) with
  | some shown => shown.any fun a => a.source == 0 && shown.any fun b => a.target == b.source && b.target == 2
  | none => false

end Test.Audit.GraphControls
