import Tools.View.SceneBridge
import Whatwg.Svg.Scene.Extent

/-!
Geometry envelopes of resolved calls, with text metrics reported as unmeasured.
The kit owns integer control hulls and their aggregation.
The envelope ignores clipping intersections and states no font or rasterization theorem.
Placement: `docs/research/2026-10-13-graph-bounds-plan.md`.
-/

namespace Tools.View.PaintBounds
open Whatwg.Svg.Scene

/-- A geometry envelope in logical pixels, with a separate text-metric observation. -/
structure Report where
  geometry : Option IBox := none
  unmeasuredText : Bool := false
deriving DecidableEq, Repr

/-- The kit's hull of a cubic's four integer controls, without a curve sampling claim. -/
def controlHull (c : Cubic) : IBox := Boxed.box (SceneBridge.cubic c)

/-- The existing self-loop's four controls, shared by routing and canvas allocation. -/
def loopSegment (right centre half reach : Int) : Cubic :=
  ⟨(right, centre - half), (right + 2 * reach, centre - 2 * half),
    (right + 2 * reach, centre + 2 * half), (right, centre + half)⟩

/-- Extend a canvas's far sides for stored envelopes without changing its routing coordinates. -/
def reserveCanvas (width height : Int) (envelopes : List IBox) : Int × Int :=
  match IBox.hullAll envelopes with
  | none => (width, height)
  | some b => (max width b.x1, max height b.y1)

/-- Reserving loop envelopes retains both allocated far sides.
The graph and flow producers consume this tool law for concept 7 and R14 under row 334 (3). -/
theorem reserveCanvas_notShrink (width height : Int) (envelopes : List IBox) :
    width ≤ (reserveCanvas width height envelopes).1 ∧
    height ≤ (reserveCanvas width height envelopes).2 := by
  unfold reserveCanvas
  split
  · exact ⟨Int.le_refl _, Int.le_refl _⟩
  · exact ⟨Int.le_max_left _ _, Int.le_max_left _ _⟩

/-- Convert a milli-unit envelope to logical pixels, rounding each side outward. -/
def roundOut (b : IBox) : IBox :=
  ⟨b.x0 / 1000, b.y0 / 1000, -((-b.x1) / 1000), -((-b.y1) / 1000)⟩

/-- The outward conversion contains each stored side in its original milli-unit scale.
The shape envelope consumes this observation under decisions row 334 (3), concept 7 and R14. -/
theorem roundOut_covers (b : IBox) :
    1000 * (roundOut b).x0 ≤ b.x0 ∧ b.x1 ≤ 1000 * (roundOut b).x1 ∧
    1000 * (roundOut b).y0 ≤ b.y0 ∧ b.y1 ≤ 1000 * (roundOut b).y1 := by
  simp only [roundOut]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- A rectangle at zoom one, including the lowering's minimum span. -/
def rectangle (x y w h : Int) : IBox := ⟨x, y, x + max 1 w, y + max 1 h⟩

/-- A curve's symmetric margin covers half its snapped stroke weight, rounded upward. -/
def strokeMargin (weight : Nat) : Int := (max 1 (weight : Int) + 1) / 2

/-- Text ink requires host font metrics; every text call records that missing observation. -/
def textUnmeasured : Call → Bool
  | .cells .. | .text .. => true
  | _ => false

/-- Observe text calls without scanning geometry or text content. -/
def textUnmeasuredAll (cs : List (Keyed Call)) : Bool := cs.any fun c => textUnmeasured c.call

/-- One call's envelope. Text, clips and hit regions remain separate from painted geometry. -/
def call : Call → Report
  | .fill _ _ x y w h | .frame _ x y w h _ => ⟨some (rectangle x y w h), false⟩
  | .curve _ c weight =>
    let m := strokeMargin weight
    ⟨some ((controlHull c).grow m m m m), false⟩
  | .shape _ _ paths => ⟨(IBox.hullAll (paths.flatten.map controlHull)).map roundOut, false⟩
  | .cells .. | .text .. => ⟨none, true⟩
  | .cut .. | .uncut | .hit .. => {}

/-- Collect geometry envelopes without resolving or drawing a call again. -/
def calls (cs : List (Keyed Call)) : Report :=
  { geometry := IBox.hullAll (cs.filterMap fun c => (call c.call).geometry),
    unmeasuredText := textUnmeasuredAll cs }

/-- Each reported call envelope lies inside the aggregate geometry envelope.
The viewport consumes this tool law for concept 7 and R14 under decisions row 334 (3).
The observation concerns stored envelopes, without a text or rasterization claim. -/
theorem call_inside {cs : List (Keyed Call)} {c : Keyed Call} {b h : IBox}
    (hc : c ∈ cs) (hb : (call c.call).geometry = some b) (hh : (calls cs).geometry = some h) :
    b.Inside h :=
  IBox.inside_hullAll (List.mem_filterMap.mpr ⟨c, hc, hb⟩) hh

/-- Keep the allocated canvas and add a nonnegative margin around the geometry envelope. -/
def fit (allocated : IBox) (report : Report) (halo : Nat := 0) : IBox :=
  match report.geometry with
  | none => allocated
  | some b => allocated.hull (b.grow halo halo halo halo)

/-- Viewport fitting retains the allocated canvas. Its consumer is the graph viewport.
This tool law serves concept 7 and R14 under decisions row 334 (3). -/
theorem allocated_inside_fit (allocated : IBox) (report : Report) (halo : Nat) :
    allocated.Inside (fit allocated report halo) := by
  unfold fit
  split
  · exact IBox.Inside.refl allocated
  · exact IBox.inside_hull_left _ _

/-- Viewport fitting contains each reported envelope, including an optional halo.
The graph viewport consumes this tool law under decisions row 334 (3), concept 7 and R14. -/
theorem geometry_inside_fit {allocated b : IBox} {report : Report}
    (hb : report.geometry = some b) (halo : Nat) : b.Inside (fit allocated report halo) := by
  have grown : b.Inside (b.grow halo halo halo halo) := by
    simp only [IBox.Inside, IBox.grow]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  rw [fit, hb]
  exact grown.trans (IBox.inside_hull_right _ _)

end Tools.View.PaintBounds
