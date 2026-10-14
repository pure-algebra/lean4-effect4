import Tools.View.Glyph
import Tools.View.Tube.Motion
import Tools.View.Tube.PegGlyphs
import Tools.View.Tube.PegRender
import Whatwg.Svg.Scene.Join.Laws

/-!
# Tools.View.Tube.Glyphs — every mark of the vocabulary as a figure of tubes

Each of the 37 marks of `Tools.View.Glyph.Shape` is drawn here as tubes, with the tube pen
(`Tools.View.Tube.Draw`): tubes, the units they carry, and their fittings, in a cell of 96 px at
one pixel to the pixel. No circle, rectangle, arrowhead or text stands in a figure. The note is
`docs/research/2026-10-13-tube-language/glyphs.md`.

* **One family per kind** (`Kind`, decisions row 368 (4)): each kind is one plumbing element, and
  its builder (`bodyFigure`, `vesselFigure`, …) draws its marks as variations of that element. Each
  builder's docstring says what the element is and what its contents mean.
* **Joins carry meaning** (the owner's ruling of 2026-10-13, relayed by the coordinator). Two tubes
  that share fluid are joined solidly, a conserving tee or wye: the branch leaves its parent on the
  parent's centreline, tangent to it, and turns away, and a figure names the pair
  (`Figure.joins`) for the pen's fillet. A pipe that enters a vessel end to end is a reducer
  (`Figure.reducers`). Two tubes where nothing passes stand `AIRGAP` apart, an air gap: a
  broadcast's taps, a crossing, a cadence's strut and a force's stop. A strut, structure that
  carries nothing, is named too (`Figure.struts`), so the pen may draw it with no inside.
* **Every end round.** Inside a figure every end is round, closed. A tube that meets the world
  runs past the cell's edge, so the edge cuts it (`port`).
* **Keys by role.** A figure's tubes are `main` and `b` to `f` (so `main:wall`), its units `u` to
  `u4`, the inside of a promised unit `h`, its collars `k` and `k2`, a surge `s`. A key names
  one role in every figure (a guard holds it). The kit's join matches the parts two figures
  share, and the rest enter or leave from their root (`Picture.step`), so any mark turns into any
  other.
* **One radius.** Every bend is 24 px, the least radius of the solid-tube pen (`BEND` there); a
  guard holds every piece to that law already.

**The laws.** Every tube of every figure keeps the bend law (`figure_ok`), and every moment of the
step from any figure to any other keeps it too (`morph_ok`), from `Tube.mix_ok`, `pad_ok` and
`Piece.zero_ok` through `step_ok`. The guards hold that no two marks are drawn alike and how far
apart the marks one sort tells apart are (`distance`, `near`).
-/

namespace Tools.View.Tube.Glyphs
open Tools.View Tools.View.Tube
open Tools.View.Glyph (Shape Kind sorts table shapeNames)

/-- The still figure on the slot grid. Films keep the tube motion carrier below. -/
def pegFigure (s : Shape) : PegFigure := PegGlyphs.draw s

/-- The peg renderer reports a body index if its tour has no tangent. -/
def pegStill (s : Shape) : Except Nat Whatwg.Html.SvgNode := (pegFigure s).still 96 96

/-! ## To move into Form -/

/-- **A tube drawn from its other end keeps the bend law**: its pieces are the tube's, in the
other order, each turning the other way, and a turn is as large either way. A mark drawn
`fromEnd` is written reversed (`smil`), so `morph_ok` covers what is drawn. -/
theorem reverse_ok {t : Tube} (h : t.ok) : t.reverse.ok := by
  intro p hp
  have hp' : p ∈ t.pieces.reverse.map (fun q => (⟨q.len, -q.turn⟩ : Piece)) := hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
  have hq' := h q (List.mem_reverse.mp hq)
  show (-q.turn).natAbs ≤ HALF_TURN ∧ (-q.turn).natAbs * BEND ≤ q.len * 1000000
  rw [Int.natAbs_neg]
  exact hq'

/-! ## To move into Draw -/

/-- **The air gap**, in thousandths of a pixel: two bodies this far apart touch nowhere, so
nothing passes between them. The solid-tube pen names it `GAP` in `Tools.View.Tube.Draw`; this
one stands in until the merge. -/
def AIRGAP : Nat := 4000

/-- Half a tube's body, in thousandths of a pixel. -/
def half (bore : Nat) : Nat := body bore / 2

/-- The distance between the centrelines of two tubes whose bodies stand an air gap apart. -/
def apart (b₁ b₂ : Nat) : Nat := half b₁ + AIRGAP + half b₂

/-- **A surge standing on a tube**: its body swollen by `SWELL` on each side over `len` from `s`,
as a pressure wave swells a pipe (Joukowsky): a stretch of the body, a shoulder at each end.
A surge of no length is spent, and draws nothing. -/
def surgeOf (key : String) (t : Tube) (s : Int) (len : Nat) : List Mark :=
  let w := body t.bore
  [stretchOf (key ++ ":wall") t s len w w (if len = 0 then w else w + 2 * SWELL)]

/-- **A unit centred at `mid`** along a tube: the pen's pill, its slot's front half a slot ahead. -/
def unitAt (key : String) (t : Tube) (mid : Int) : Mark :=
  unitOf key t (mid + (unitLen t.bore / 2 : Nat))

/-- **A promised unit centred at `mid`**: the pen's hollow, its rim keyed as the unit, so a
promise kept turns into the unit in place, and its inside, the mark narrower than the bore,
keyed `inside`, which leaves when the promise is kept. (A test of the width, not of the key's
text: `String.endsWith` reaches `Classical.choice`.) -/
def hollowAt (rim inside : String) (t : Tube) (mid : Int) : List Mark :=
  (hollowOf rim t (mid + (unitLen t.bore / 2 : Nat))).map fun m =>
    { m with key := if m.width < contents t.bore then inside else rim }

/-! ## To move into Motion -/

/-- **A lawful track**: every pose it takes on its way is a tube that keeps the bend law. -/
def Lawful (tr : Track) : Prop := ∀ (t : Nat) (u : Tube), tr.at t = .path u → u.ok

/-- A progress held for the morph is at most the whole. -/
theorem clamp_le (e : Int) : clamp e ≤ 1000 := Nat.min_le_right _ _

/-- **Every pose of a bend keeps the bend law** when its two tubes and the pose it passes through
do: each pose is a mix of lawful tubes (`Tube.mix_ok`). A step of `tracksOf_ok`. -/
theorem bend_ok {a b : Tube} {v : Option Tube} (ha : a.ok) (hb : b.ok)
    (hv : ∀ w, v = some w → w.ok) (k : String) (tm : Timing) : Lawful ⟨k, .bend a b v, tm⟩ := by
  intro t u h
  change Stroke.at (.bend a b v) (tm.at t) = .path u at h
  cases v with
  | none =>
    simp only [Stroke.at, Pose.path.injEq] at h
    rw [← h]
    exact Tube.mix_ok (clamp_le _) ha hb
  | some w =>
    simp only [Stroke.at] at h
    split at h
    · simp only [Pose.path.injEq] at h
      rw [← h]
      exact Tube.mix_ok (clamp_le _) ha (hv w rfl)
    · simp only [Pose.path.injEq] at h
      rw [← h]
      exact Tube.mix_ok (clamp_le _) (hv w rfl) hb

/-- A change of width takes no path. A step of `tracksOf_ok`. -/
theorem width_ok (x y : Int) (k : String) (tm : Timing) : Lawful ⟨k, .width x y, tm⟩ := by
  intro t u h
  change Stroke.at (.width x y) (tm.at t) = .path u at h
  simp only [Stroke.at, reduceCtorEq] at h

/-- A window along a stroke takes no path. A step of `tracksOf_ok`. -/
theorem window_ok (x y : Int × Int) (v : Option (Int × Int)) (k : String) (tm : Timing) :
    Lawful ⟨k, .window x y v, tm⟩ := by
  intro t u h
  change Stroke.at (.window x y v) (tm.at t) = .path u at h
  cases v with
  | none => simp only [Stroke.at, reduceCtorEq] at h
  | some w =>
    simp only [Stroke.at] at h
    split at h <;> simp only [reduceCtorEq] at h

/-- The pose a mark passes through keeps the bend law when the mark it is taken from does. A
step of `tracksOf_ok`. -/
theorem viaTube_ok {via : Option Mark} {b : Mark} (hv : ∀ v, via = some v → v.tube.ok) :
    ∀ w, (via.bind fun v => if v.tube != b.tube then some v.tube else none) = some w → w.ok := by
  intro w hw
  cases via with
  | none => simp only [Option.bind, reduceCtorEq] at hw
  | some v =>
    simp only [Option.bind] at hw
    split at hw
    · simp only [Option.some.injEq] at hw
      rw [← hw]
      exact hv v rfl
    · simp only [reduceCtorEq] at hw

/-- **The tracks of a mark are lawful** when the mark's two poses and the pose it passes through
keep the bend law. A step of `step_ok`. -/
theorem tracksOf_ok {a b : Mark} {via : Option Mark} (ha : a.tube.ok) (hb : b.tube.ok)
    (hv : ∀ v, via = some v → v.tube.ok) : ∀ tr ∈ tracksOf a b via, Lawful tr := by
  intro tr htr t u h
  unfold tracksOf at htr
  simp only [List.mem_append] at htr
  rcases htr with (h1 | h2) | h3
  · split at h1
    · rw [List.mem_singleton] at h1
      subst h1
      exact bend_ok ha hb (viaTube_ok hv) _ _ t u h
    · exact absurd h1 (List.not_mem_nil)
  · split at h2
    · rw [List.mem_singleton] at h2
      subst h2
      exact width_ok _ _ _ _ t u h
    · exact absurd h2 (List.not_mem_nil)
  · split at h3
    · split at h3
      · rw [List.mem_singleton] at h3
        subst h3
        exact window_ok _ _ _ _ _ t u h
      · exact absurd h3 (List.not_mem_nil)
    · exact absurd h3 (List.not_mem_nil)

/-- **A mark shrunk to nothing keeps the bend law**: a dash keeps its tube, and a tube goes to its
root, whose pieces have no length (`Piece.zero_ok`). A step of `step_ok`. -/
theorem gone_ok {m : Mark} (h : m.tube.ok) : m.gone.tube.ok := by
  unfold Mark.gone
  split
  · exact h
  · intro p hp
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp
    exact Piece.zero_ok

/-- **Every moment of a step keeps the bend law**: the kit's join of two pictures whose marks keep
it, and whose poses passed through keep it, yields lawful tracks only. What enters grows from its
root and what leaves shrinks to it (`gone_ok`); what is kept morphs (`Tube.mix_ok`). -/
theorem step_ok {A B : Picture} (hA : ∀ m ∈ A.marks, m.tube.ok) (hB : ∀ m ∈ B.marks, m.tube.ok)
    (hV : ∀ m ∈ B.via, m.tube.ok) : ∀ tr ∈ A.step B, Lawful tr := by
  intro tr htr
  unfold Picture.step at htr
  simp only [List.mem_append, List.mem_flatMap] at htr
  rcases htr with (⟨⟨a, b⟩, hab, ht⟩ | ⟨b, hb, ht⟩) | ⟨a, ha, ht⟩
  · obtain ⟨ha, hb, -⟩ := Whatwg.Svg.Scene.mem_update _ _ _ hab
    exact tracksOf_ok (hA a ha) (hB b hb) (fun v hv => hV v (List.mem_of_find?_eq_some hv)) tr ht
  · have hb' := ((Whatwg.Svg.Scene.mem_enter _ _ _).mp hb).1
    exact tracksOf_ok (gone_ok (hB b hb')) (hB b hb') (by intro _ hv; cases hv) tr ht
  · have ha' := ((Whatwg.Svg.Scene.mem_exit _ _ _).mp ha).1
    exact tracksOf_ok (hA a ha') (gone_ok (hA a ha')) (by intro _ hv; cases hv) tr ht

/-! ## The cell -/

/-- **The side of the cell** a figure stands in: 96 px, at one pixel to the pixel. (Named apart
from the view grid's `Tools.View.CELL`.) -/
def SIDE : Nat := 96

/-- The bores of the figures, in thousandths of a pixel, one for each body of the ladder
(`WIDTHS`: 10, 14, 20, 28 px): a pipe that carries, a vessel, a thin tube (a strut, a staff, a
tap), a fine tube (an enclosure, a bead), and each pipe a merge joins, a fine tube, so two of them
hold as much as the pipe they join (`widths_double`). -/
def PIPE : Nat := 10000
def VESSEL : Nat := 18000
def THIN : Nat := 0
def FINE : Nat := 4000
def SPLIT : Nat := FINE
/-- A vessel's room at each end, in thousandths of a pixel. -/
def HEADROOM : Nat := 6000
/-- **The radius of every bend**, in pixels: the solid-tube pen's least radius. -/
def RADIUS : Nat := 24

/-- A position, in pixels, in thousandths. -/
def px (n : Int) : Int := n * 1000
/-- A straight run of `n` pixels. -/
def run (n : Nat) : Piece := ⟨n * 1000, 0⟩
/-- **An arc** of radius `r` pixels turning `θ`: its length rounded up, so it keeps the bend law
exactly for every radius of `BEND` or more. -/
def arcR (r : Nat) (θ : Int) : Piece := ⟨(r * θ.natAbs + 999) / 1000, θ⟩
/-- An arc at the one radius. -/
def arc (θ : Int) : Piece := arcR RADIUS θ

/-- The headings: east, south, west, north, in millionths of a radian, positive clockwise on the
page. -/
def E : Int := 0
def S : Int := HALF_PI
def W : Int := PI
def N : Int := -HALF_PI
/-- A sixth and an eighth of a turn, in millionths of a radian. -/
def SIXTH : Int := 1047198
def EIGHTH : Int := 785398
/-- A length times the cosine of an eighth of a turn: the run across or down of a diagonal. -/
def diag (n : Nat) : Int := (n * 707107 / 1000000 : Nat)

/-- A tube from a point (thousandths of a pixel) along a heading. -/
def tube (x y head : Int) (bore : Nat) (ps : List Piece) : Tube := ⟨x, y, head, bore, ps⟩

/-- A tube's middle, along it. -/
def middle (t : Tube) : Int := (t.length / 2 : Nat)

/-! ## Figures -/

/-- **A figure**: its marks, its solid joins as pairs of tube keys (the parent, then the branch
that leaves it tangentially), its reducers (a pipe, then the vessel it enters end to end), and its
struts (the tubes that are structure, not channels: they carry nothing, and the pen may draw them
with no inside). A solid join and a reducer share fluid; the pen rounds the crotch of the one and
smooths the step of the other. Two tubes named in neither that stand `AIRGAP` apart meet across an
air gap: nothing passes between them. -/
structure Figure where
  marks : List Mark
  joins : List (String × String) := []
  reducers : List (String × String) := []
  struts : List String := []
deriving Inhabited

/-- **Body: a closed piece of line, and its payload.** A body is a short pipe closed at both
ends, lying along the reading, as a spool of pipe is: a thing with an identity that moves. Its
payload is its contents, a unit of fluid where the body is a value; a literal is the unit alone.
A collar round it is a name: one on a handle, one at each end of a call. A tap above it, across an
air gap, reads it and takes nothing. A fiber's entry is its unit set on a closed ring, its loop.
A failure is a fitting through which nothing flows: a crossing whose under pipe stops an air gap
short of the over pipe (a typed failure, `×`), or a pipe broken and sheared, its ends an air gap
apart (a defect). A cause is its reasons, each a bead, in order on one line and parted by air
gaps. -/
def bodyFigure : Shape → Figure
  | .box => { marks := bodyOf "main" piece }
  | .value => { marks := bodyOf "main" piece ++ [unitOf "u" piece piece.length] }
  | .atom =>
    let u := unitLen PIPE
    let drop := tube (px 48 - (u / 2 : Nat)) (px 48) E PIPE [⟨u, 0⟩]
    { marks := [unitAt "u" drop (middle drop)] }
  | .call => { marks := bodyOf "main" piece ++
      [collarOf "k" piece (px 3) 12000, collarOf "k2" piece (px 39) 12000] }
  | .tag =>
    let token := tube (px 33) (px 48) E PIPE [run 30]
    { marks := bodyOf "main" token ++ [collarOf "k" token (px 9) 12000] }
  | .probe =>
    let top := px 9
    let tap := tube (px 48) top S THIN [⟨(px 48 - (apart PIPE THIN : Nat) - top).toNat, 0⟩]
    { marks := bodyOf "main" piece ++ bodyOf "b" tap }
  | .enter =>
    let ring := tube (px 39) (px 24) E PIPE [run 18, arc W, run 18, arc W]
    { marks := bodyOf "main" ring ++ [unitAt "u" ring (px 9)] }
  | .cross =>
    let L : Nat := 84000
    let d := diag (L / 2)
    let over := tube (px 48 - d) (px 48 - d) EIGHTH FINE [⟨L, 0⟩]
    let a := apart FINE FINE
    let stub := L / 2 - a
    { marks := bodyOf "main" over ++
        bodyOf "b" (tube (px 48 - d) (px 48 + d) (-EIGHTH) FINE [⟨stub, 0⟩]) ++
        bodyOf "c" (tube (px 48 + diag a) (px 48 - diag a) (-EIGHTH) FINE [⟨stub, 0⟩]) }
  | .hash =>
    { marks := bodyOf "main" (tube (px 12) (px 42) E PIPE [run 24]) ++
        bodyOf "b" (tube (px 36 + SHEAR) (px 54) E PIPE [⟨(px 84 - px 36 - SHEAR).toNat, 0⟩]) }
  | .reasons =>
    let a := apart FINE FINE
    let L := (72000 - 2 * a) / 3
    let bead (i : Nat) := tube (px 12 + (i * (L + a) : Nat)) (px 48) E FINE [⟨L, 0⟩]
    { marks := bodyOf "main" (bead 0) ++ bodyOf "b" (bead 1) ++ bodyOf "c" (bead 2) }
  | _ => { marks := [] }
where
  /-- The piece of line a body is. -/
  piece : Tube := tube (px 21) (px 48) E PIPE [run 54]
  /-- How far along the second half of a sheared pipe starts past the first's end, so that their
  round ends, 12 px apart across the pipe, stand an air gap apart: `√(26² − 12²)` px, rounded up. -/
  SHEAR : Int := 23066

/-- **Vessel: a short closed vessel of one unit**, its unit hollow while it is promised and filled
once it is kept (decisions row 354 (2)). The vessel is as long as one unit's slot and its room,
so its length is its capacity. A sealed vessel is a promise kept within the run (a finalizer, a
deferred); a vessel that a pipe enters, a reducer, waits on what comes down the pipe (a park, a
task). An empty vessel on its pipe is a place a result returns to (a frame's hole). A tray, a low
bend that holds a unit or stands empty, is an option. -/
def vesselFigure : Shape → Figure
  | .hollowDot => { marks := bodyOf "main" sealed ++ hollowAt "u" "h" sealed (middle sealed) }
  | .filledDot => { marks := bodyOf "main" sealed ++ [unitAt "u" sealed (middle sealed)] }
  | .hollowBox => { marks := bodyOf "main" fed ++ bodyOf "b" inlet ++
                      hollowAt "u" "h" fed (middle fed)
                    reducers := [("b", "main")] }
  | .filledBox => { marks := bodyOf "main" fed ++ bodyOf "b" inlet ++ [unitAt "u" fed (middle fed)]
                    reducers := [("b", "main")] }
  | .hole => { marks := bodyOf "main" fed ++ bodyOf "b" inlet, reducers := [("b", "main")] }
  | .slot =>
    let tray := tube (px 18) (px 33) S VESSEL [arc (-HALF_PI), run 12, arc (-HALF_PI)]
    { marks := bodyOf "main" tray ++ [unitAt "u" tray (middle tray)] }
  | _ => { marks := [] }
where
  /-- A vessel's length: one unit's slot and its room at each end. -/
  L : Nat := unitLen VESSEL + 2 * HEADROOM
  /-- A sealed vessel, centred. -/
  sealed : Tube := tube (px 48 - (L / 2 : Nat)) (px 48) E VESSEL [⟨L, 0⟩]
  /-- A vessel a pipe enters, ending at 75 px, and its pipe from 12 px. -/
  fed : Tube := tube (px 75 - L) (px 48) E VESSEL [⟨L, 0⟩]
  inlet : Tube := tube (px 12) (px 48) E PIPE [⟨(px 75 - L - px 12).toNat, 0⟩]

/-- **Container: a tube that encloses**, open where a close is owed. A scope is a pair of hooks
round its span, and an open scope its first hook alone, the close owed; a region is two opposite
corners, `⌜ ⌟`, that frame what it provides; an uninterruptible span is a double rail; a block is
its statements, one closed run each, read top to bottom; a library its named definitions, each
with a collar, a name, then its body; a record its rows, each a muted name, thin and short, and
its field an air gap after it, so the names stand once in a column; a list a lane of units, read
from its front. The containers' tubes are fine: what they enclose is the figure. -/
def containerFigure : Shape → Figure
  | .openBracket => { marks := bodyOf "main" left }
  | .bracket => { marks := bodyOf "main" left ++ bodyOf "b" right }
  | .region =>
    { marks := bodyOf "main" (tube (px 12) (px 66) N FINE [run 30, arc HALF_PI, run 30]) ++
        bodyOf "b" (tube (px 84) (px 30) S FINE [run 30, arc HALF_PI, run 30]) }
  | .rail =>
    { marks := bodyOf "main" (tube (px 12) (px 36) E FINE [run 72]) ++
        bodyOf "b" (tube (px 12) (px 60) E FINE [run 72]) }
  | .block =>
    { marks := bodyOf "main" (row 24 66) ++ bodyOf "b" (row 48 66) ++ bodyOf "c" (row 72 45) }
  | .library =>
    { marks := bodyOf "main" (row 21 66) ++ bodyOf "b" (row 48 66) ++ bodyOf "c" (row 75 66) ++
        [collarOf "k" (row 21 66) (px 3) 12000, collarOf "k2" (row 48 66) (px 3) 12000] }
  | .panel =>
    -- each row a muted name, thin and short, and its field, an air gap after it
    let x₁ : Int := px 21 + (apart THIN FINE : Nat)
    let name (y : Nat) := tube (px 12) (px y) E THIN [run 9]
    let field (y : Nat) := tube x₁ (px y) E FINE [⟨(px 84 - x₁).toNat, 0⟩]
    { marks := bodyOf "main" (field 24) ++ bodyOf "b" (field 48) ++ bodyOf "c" (field 72) ++
        bodyOf "d" (name 24) ++ bodyOf "e" (name 48) ++ bodyOf "f" (name 72) }
  | .cells =>
    let u := unitLen VESSEL
    let L := 2 * u + 2 * HEADROOM
    let lane := tube (px 48 - (L / 2 : Nat)) (px 48) E VESSEL [⟨L, 0⟩]
    { marks := bodyOf "main" lane ++
        [unitAt "u" lane (HEADROOM + u / 2 : Nat), unitAt "u2" lane (HEADROOM + u + u / 2 : Nat)] }
  | _ => { marks := [] }
where
  /-- A scope's first hook, `(`, and its second, `)`. -/
  left : Tube := tube (px 36) (px 18) W FINE [arc (-HALF_PI), run 12, arc (-HALF_PI)]
  right : Tube := tube (px 60) (px 18) E FINE [arc HALF_PI, run 12, arc HALF_PI]
  /-- A closed run at a height, from 15 px. -/
  row (y n : Nat) : Tube := tube (px 15) (px y) E FINE [run n]

/-- **Wire: a pipe that carries.** A wire is a pipe of the carrying bore, long along the reading.
A sequence steps from one part into the next and carries the value across; a merge joins two
pipes solidly into one as wide as both, a conserving wye, so the counts add; an alternative
leaves its pipe by a solid wye into two arms, each as wide as the pipe, since the whole flow
takes one; a loop leaves its line by a solid join, turns back below it and rejoins it; a rest
parts the pipe by an air gap, a valve closed for a turn. Every solid branch leaves its parent on
its centreline and tangent to it, so the merge is given from its joint outward. -/
def wireFigure : Shape → Figure
  | .series =>
    let t := tube (px 15) (px 36) E PIPE [run 12, arc SIXTH, arc (-SIXTH), run 12]
    { marks := bodyOf "main" t ++ [unitAt "u" t (middle t)] }
  | .parallel =>
    -- the joint stands where the arms, 41.569 px of S and 9 px of run, reach back to 12 px; the
    -- trunk arrives there and stops, as the kit's fork has it, so its blends are the outline's
    let joint : Int := 62569
    { marks := bodyOf "main" (tube (px 84) (px 48) W PIPE [⟨(px 84 - joint).toNat, 0⟩]) ++
        bodyOf "b" (tube joint (px 48) W SPLIT [arc SIXTH, arc (-SIXTH), run 9]) ++
        bodyOf "c" (tube joint (px 48) W SPLIT [arc (-SIXTH), arc SIXTH, run 9])
      joins := [("main", "b"), ("main", "c")] }
  | .alternative =>
    -- the trunk arrives where the arms leave, and stops there (the kit's fork)
    { marks := bodyOf "main" (tube (px 12) (px 48) E PIPE [run 15]) ++
        bodyOf "b" (tube (px 27) (px 48) E PIPE [arc (-SIXTH), arc SIXTH, run 15]) ++
        bodyOf "c" (tube (px 27) (px 48) E PIPE [arc SIXTH, arc (-SIXTH), run 15])
      joins := [("main", "b"), ("main", "c")] }
  | .loop =>
    -- the line is two halves from its middle, so each half of the return leaves one of them
    -- there, tangentially, and turns a half turn down and back; the two halves of the return
    -- meet below, end to end, a ring hung from the line; the return is fine, as a recirculation
    -- line is narrower than its main
    { marks := bodyOf "main" (tube (px 48) (px 24) E PIPE [run 36]) ++
        bodyOf "d" (tube (px 48) (px 24) W PIPE [run 36]) ++
        bodyOf "b" (tube (px 48) (px 24) E FINE [arc W]) ++
        bodyOf "c" (tube (px 48) (px 24) W FINE [arc (-W)])
      joins := [("main", "b"), ("d", "c")] }
  | .rest =>
    let a := apart PIPE PIPE
    let L := (72000 - a) / 2
    { marks := bodyOf "main" (tube (px 12) (px 48) E PIPE [⟨L, 0⟩]) ++
        bodyOf "b" (tube (px 12 + (L + a : Nat)) (px 48) E PIPE [⟨L, 0⟩]) }
  | _ => { marks := [] }

/-- **Bond: a relation between lanes, by a fitting or by none.** A fork's child lane starts beside
the parent's, an air gap below it, runs down and forward and on: the child shares none of the
parent's fluid. A completion is a broadcast: its header carries the one exit, and every waiter's
tap hangs an air gap below it holding its own copy, so the counts do not add, unlike a tee. A
port is a loop to the world: the request leaves on one leg, and the answer, owed, comes back on
the other. -/
def bondFigure : Shape → Figure
  | .arrow =>
    let y₀ := px 24 + (apart PIPE PIPE : Nat)
    -- the diagonal's length, so the child's run lies on a whole pixel:
    -- `(72 − y₀ − r (1 − cos 45°)) √2`
    let drop : Int := (RADIUS * 292893 / 1000 : Nat)
    let down := ((px 72 - y₀ - drop) * 1414214 / 1000000).toNat
    { marks := bodyOf "main" (tube (px 12) (px 24) E PIPE [run 72]) ++
        bodyOf "b" (tube (px 21) y₀ EIGHTH PIPE [⟨down, 0⟩, arc (-EIGHTH), run 30]) }
  | .spider =>
    let y₀ := px 18 + (apart PIPE PIPE : Nat)
    let tap (x : Nat) := tube (px x) y₀ S PIPE [run 24]
    let header := tube (px 15) (px 18) E PIPE [run 66]
    { marks := bodyOf "main" header ++ bodyOf "b" (tap 22) ++ bodyOf "c" (tap 48) ++
        bodyOf "d" (tap 74) ++
        [unitAt "u" header (px 15), unitAt "u2" (tap 22) (px 12), unitAt "u3" (tap 48) (px 12),
         unitAt "u4" (tap 74) (px 12)] }
  | .port =>
    let pin := tube (px 99) (px 24) W PIPE [run 51, arc (-W), run 51]
    { marks := bodyOf "main" pin ++ [unitAt "u" pin (px 15)] ++
        hollowAt "u2" "h" pin ((pin.length : Int) - px 15) }
  | _ => { marks := [] }

/-- **Force: a surge that a stop holds.** A force travels along a pipe as a surge, the pipe
swollen round it, and ends at a stop set across its way, an air gap short of it: the blocked
arrow `⊣`, an interrupt. What holds it is outside it: a rail over a span, or the lane it lands
on. -/
def forceFigure : Shape → Figure
  | .blockedArrow =>
    let stop := px 75 - (apart PIPE THIN : Nat)
    let line := tube (px 12) (px 48) E PIPE [⟨(stop - px 12).toNat, 0⟩]
    { marks := bodyOf "main" line ++ surgeOf "s" line (px 9) 18000 ++
        bodyOf "b" (tube (px 75) (px 24) S THIN [run 48])
      struts := ["b"] }
  | _ => { marks := [] }

/-- **Cadence: a strut across the staff.** A cadence is a closed, thin strut that stands across
the staff, the lane of time, and carries nothing; the staff stops an air gap short of it, so no
unit passes. A bar line is one strut, the staff on both sides; an exit is a thin strut and a
heavy one, the staff ending before them; a fermata is an arch held over the staff, its feet an
air gap above it, over a dot; a caesura is two slanted struts, the staff gone. -/
def cadenceFigure : Shape → Figure
  | .barLine =>
    { marks := bodyOf "main" (bar (px 48) THIN) ++ bodyOf "b" (staff (px 9) (px 48 - a)) ++
        bodyOf "c" (staff (px 48 + a) (px 87))
      struts := ["main"] }
  | .exitBar =>
    { marks := bodyOf "main" (bar (px 42) THIN) ++ bodyOf "b" (staff (px 9) (px 42 - a)) ++
        bodyOf "c" (bar (px 42 + (apart THIN PIPE : Nat)) PIPE)
      struts := ["main", "c"] }
  | .fermata =>
    { marks := bodyOf "main" (tube (px 18) (px 66 - a) N THIN [arcR 30 W]) ++
        bodyOf "b" (tube (px 9) (px 66) E THIN [run 78]) ++
        bodyOf "c" (tube (px 48) (px 42) S THIN [run 3])
      struts := ["main", "c"] }
  | .caesura =>
    let dx : Int := (apart THIN THIN * 1154701 / 1000000 : Nat)
    let slash (x : Int) := tube x (px 66) (-SIXTH) THIN [run 42]
    { marks := bodyOf "main" (slash (px 27)) ++ bodyOf "b" (slash (px 27 + dx))
      struts := ["main", "b"] }
  | _ => { marks := [] }
where
  /-- An air gap between two thin tubes' centrelines. -/
  a : Int := (apart THIN THIN : Nat)
  /-- The staff from one point to another, at 48 px. -/
  staff (x₀ x₁ : Int) : Tube := tube x₀ (px 48) E THIN [⟨(x₁ - x₀).toNat, 0⟩]
  /-- A strut down the cell. -/
  bar (x : Int) (bore : Nat) : Tube := tube x (px 12) S bore [run 72]

/-- **A mark's figure, with its joins, reducers and struts**, by its kind's family. -/
def draw (s : Shape) : Figure :=
  match s.kind with
  | .body => bodyFigure s
  | .vessel => vesselFigure s
  | .container => containerFigure s
  | .wire => wireFigure s
  | .bond => bondFigure s
  | .force => forceFigure s
  | .cadence => cadenceFigure s

/-- **A mark's figure**: its marks. -/
def figure (s : Shape) : List Mark := (draw s).marks

/-! ## As the pen draws it -/

/-- The mark of a figure's tube, by the tube's key. -/
def wall (k : String) : String := k ++ ":wall"

/-- **A figure as the pen draws it** (the merge of the glyph seat, decisions row 370): its struts
all ink, which carry nothing; each reducer's pipe run `INTO` its vessel and cut square there, the
vessel eased to the pipe's width where the pipe meets it and closed round at its other end; its
solid joins rounded, and two arms that leave one point of one parent a fork. The tubes are the
figure's own, but a pipe run into its vessel gains one straight piece, which keeps the bend law. -/
def Figure.picture (f : Figure) : Picture :=
  let find (k : String) : Option Mark := f.marks.find? (·.key == wall k)
  let ends (t : Tube) : (Int × Int) × (Int × Int) := ((t.x, t.y), (t.at t.length).1)
  let marks := f.marks.map fun m =>
    if f.struts.any (wall · == m.key) then { m with fill := .ink } else
    match f.reducers.find? (fun r => wall r.2 == m.key), f.reducers.find? (fun r => wall r.1 == m.key) with
    | some (pk, _), _ =>
      match find pk with
      | some pipe =>
        let (vs, ve) := ends m.tube
        let (ps, pe) := ends pipe.tube
        let atStart := min (dist ps vs) (dist pe vs) ≤ min (dist ps ve) (dist pe ve)
        let bw := body pipe.tube.bore
        let st := if atStart then stretchOf m.key m.tube 0 m.tube.length bw m.width m.width
          else stretchOf m.key m.tube 0 m.tube.length m.width bw m.width
        { st with roundStart := some !atStart, round := atStart, level := m.level, move := m.move,
                  shape := m.shape, fromEnd := m.fromEnd }
      | none => m
    | none, some (_, vk) =>
      match find vk with
      | some v =>
        let (vs, ve) := ends v.tube
        let (ps, pe) := ends m.tube
        let endMeets := min (dist pe vs) (dist pe ve) ≤ min (dist ps vs) (dist ps ve)
        if endMeets then { m with tube := into m.tube true, roundStart := some m.round, round := false }
        else { m with tube := into m.tube false, roundStart := some false }
      | none => m
    | none, none => m
  -- two joins of one parent whose branches start at one point are a fork
  let start (k : String) : Option (Int × Int) := (find k).map fun m => (m.tube.x, m.tube.y)
  let joins := f.joins.foldl (fun (acc : List Join) (pk, bk) =>
    if acc.any fun j => j.sibling == some (wall bk) then acc else
    match f.joins.find? (fun (pk', bk') => pk' == pk && bk' != bk && start bk' == start bk) with
    | some (_, ck) => acc ++ [{ key := pk ++ "<" ++ bk ++ ck, parent := wall pk, branch := wall bk,
                                sibling := some (wall ck) }]
    | none => acc ++ [{ key := pk ++ "<" ++ bk, parent := wall pk, branch := wall bk }]) []
  { marks, joins }

/-! ## The laws -/

/-- **Every tube of every figure keeps the bend law.** -/
theorem figure_ok (s : Shape) : ∀ m ∈ figure s, m.tube.ok := by
  cases s <;> decide

/-- **Any mark turns into any other lawfully**: every track of the step from one figure to
another is lawful at every moment of its beat. -/
theorem morph_ok (s s' : Shape) :
    ∀ tr ∈ Picture.step { marks := figure s } { marks := figure s' }, Lawful tr :=
  step_ok (figure_ok s) (figure_ok s') (fun _ h => absurd h List.not_mem_nil)

/-! ## The guards -/

/-- Every shape, in the order of its constructors. -/
def shapes : List Shape :=
  [.box, .value, .series, .parallel, .block, .alternative, .loop, .region, .bracket, .openBracket,
   .rail, .arrow, .blockedArrow, .spider, .rest, .hollowBox, .filledBox, .hollowDot, .filledDot,
   .port, .probe, .call, .library, .cross, .hash, .reasons, .exitBar, .hole, .enter, .barLine,
   .fermata, .caesura, .panel, .cells, .slot, .tag, .atom]

-- `shapes` lists every shape once, in the order of its constructors
#guard shapes.map (·.ctorIdx) == List.range shapeNames.length

/-- The solid-tube pen's least radius of a bend, `BEND` there, in thousandths of a pixel. -/
def LONG_BEND : Nat := 24000

-- every piece keeps the solid-tube pen's bend law too: no bend tighter than 24 px
#guard shapes.all fun s => (figure s).all fun m => m.tube.pieces.all fun p =>
  p.turn.natAbs * LONG_BEND ≤ p.len * 1000000

/-- Every mark of every figure. -/
def allMarks : List Mark := shapes.flatMap figure

-- a key names one role in every figure: one layer, one tone, one cap and one way along
#guard allMarks.all fun m => allMarks.all fun m' =>
  m.key != m'.key ||
    (m.layer == m'.layer && m.tone == m'.tone && m.round == m'.round && m.fromEnd == m'.fromEnd)

/-- **A mark stands in its cell**: every control point of the cubics of what it draws (its whole
centreline, or the part its dash covers), widened by half its stroke, lies in the cell. A cubic
lies in the hull of its control points, and a round end reaches half the stroke past its point,
so what is drawn lies in the cell too. -/
def inCell (m : Mark) : Bool :=
  let w : Int := (m.width / 2 : Nat)
  let t := match m.dash with
    | some (s, l) => m.drawn.cut s.toNat (s + l).toNat
    | none => m.drawn
  t.cubics.all fun c => [c.p0, c.p1, c.p2, c.p3].all fun (x, y) =>
    0 ≤ x - w && x + w ≤ px SIDE && 0 ≤ y - w && y + w ≤ px SIDE
-- every figure stands in its cell, but where it meets the world: a port runs off the edge
#guard shapes.all fun s => s == .port || (figure s).all inCell

/-- A coordinate in thousandths of a pixel within ten of a whole pixel. -/
def onPixel (v : Int) : Bool := v % 1000 ≤ 10 || v % 1000 ≥ 990

/-- **A mark's straight runs lie on whole pixels**: every cubic of its centreline that runs across
(its ends at one height, within ten thousandths) lies at a whole pixel's height, and every one
that runs down lies at a whole pixel's abscissa. With every width even, a run's edges fall on
pixel edges. -/
def crisp (m : Mark) : Bool :=
  m.drawn.cubics.all fun c =>
    ((c.p0.2 - c.p3.2).natAbs > 10 || onPixel c.p0.2) &&
      ((c.p0.1 - c.p3.1).natAbs > 10 || onPixel c.p0.1)

-- every straight run across or down of every figure lies on a whole pixel
#guard shapes.all fun s => (figure s).all crisp

-- red controls: a run half a pixel off its pixel is not crisp; a tube past the cell's right edge
-- is not in the cell; a bend of 16 px breaks the solid-tube pen's law, and one of 24 px keeps it
#guard !crisp ((bodyOf "x" (tube 0 (px 48 + 500) E PIPE [run 10])).headD default)
#guard !inCell ((bodyOf "x" (tube (px 90) (px 48) E PIPE [run 10])).headD default)
#guard !((arcR 16 HALF_PI).turn.natAbs * LONG_BEND ≤ (arcR 16 HALF_PI).len * 1000000)
#guard (arc HALF_PI).turn.natAbs * LONG_BEND ≤ (arc HALF_PI).len * 1000000

-- the halves of a sheared pipe stand an air gap apart: `SHEAR² + 12² ≥ (26 px)²`
#guard bodyFigure.SHEAR * bodyFigure.SHEAR + 12000 * 12000 ≥
  (apart PIPE PIPE * apart PIPE PIPE : Nat)

-- every join and reducer names two tubes of its figure
#guard shapes.all fun s =>
  let ks := (figure s).map (·.key)
  ((draw s).joins ++ (draw s).reducers).all fun (p, q) =>
    ks.contains (p ++ ":wall") && ks.contains (q ++ ":wall")

-- every strut names a tube of its figure, and nothing rides on it: no other mark shares its tube
#guard shapes.all fun s => (draw s).struts.all fun k =>
  match (figure s).find? (·.key == k ++ ":wall") with
  | some w => (figure s).all fun m =>
    m.key == k ++ ":wall" || m.key == k ++ ":lumen" || m.tube != w.tube
  | none => false

/-- The tubes' keys, by role. -/
def TUBES : List String := ["main", "b", "c", "d", "e", "f", "s"]

/-- The part a key names: a tube's, for each of its marks (`main:wall` and `main:lumen` are part
of `main`), else the key itself. (A test of equality, not a split of the text: `String.splitOn`
reaches `Classical.choice`.) -/
def part (k : String) : String :=
  match TUBES.find? fun p => k == p ++ ":wall" || k == p ++ ":lumen" with
  | some p => p
  | none => k

/-- A figure's parts: the first mark of each part, in order. -/
def parts (ms : List Mark) : List Mark :=
  ms.foldl (fun acc m => if acc.any (part ·.key == part m.key) then acc else acc ++ [m]) []

/-- **How far apart two figures are**, in parts: the parts of one that the other lacks, and for
each part both have, the pieces of its tube that differ (padded to one count), a change of its
tube's start or heading, of its width, and of its dash. -/
def distance (A B : List Mark) : Nat :=
  let A' := parts A
  let B' := parts B
  let only (X Y : List Mark) := (X.filter fun m => !(Y.any (part ·.key == part m.key))).length
  let shared := A'.filterMap fun a => (B'.find? (part ·.key == part a.key)).map (a, ·)
  only A' B' + only B' A' + shared.foldl (fun n (a, b) =>
    let k := max a.tube.pieces.length b.tube.pieces.length
    let pieces := (List.zip (pad k a.tube.pieces) (pad k b.tube.pieces)).filter fun (p, q) => p != q
    let moved := a.tube.x != b.tube.x || a.tube.y != b.tube.y || a.tube.head != b.tube.head
    n + pieces.length + (if moved then 1 else 0) + (if a.width != b.width then 1 else 0) +
      (if a.dash != b.dash then 1 else 0)) 0

/-- The pairs of distinct shapes that one sort's constructors use. -/
def sortPairs : List (Shape × Shape) :=
  sorts.flatMap fun srt =>
    let used := (srt.ctors.filterMap fun c => (table.find? (·.ctor == c)).map (·.shape)).eraseDups
    used.zipIdx.flatMap fun (s, i) => (used.drop (i + 1)).map (s, ·)

/-- **The pairs that one sort tells apart by one part only**, each for a reason. A run turns the
first three into one another in place, so their morph is short: a promise and its keeping, a
place and the result that fills it, a scope and its close. The last two are the plain body and
the body with one thing more: its payload, its tap. Every part is a whole tube or unit, at least
14 px across, so one part is a visible difference. -/
def near : List (Shape × Shape) :=
  [(.hollowBox, .filledBox), (.hole, .filledBox), (.openBracket, .bracket), (.value, .box),
   (.box, .probe)]

-- no two marks are drawn alike
#guard shapes.all fun s => shapes.all fun s' => s == s' || figure s != figure s'
-- the marks one sort tells apart differ by a whole part, and by two at least exactly but for the
-- pairs of `near`
#guard sortPairs.all fun (s, t) => distance (figure s) (figure t) ≥ 1
#guard sortPairs.all fun (s, t) =>
  (distance (figure s) (figure t) < 2) == (near.contains (s, t) || near.contains (t, s))
-- the morphs a run makes are short: a promise kept changes one part, its inside; a scope closed
-- adds its second hook; a hole filled adds its unit
#guard distance (figure .hollowDot) (figure .filledDot) == 1
#guard distance (figure .hollowBox) (figure .filledBox) == 1
#guard distance (figure .openBracket) (figure .bracket) == 1
#guard distance (figure .hole) (figure .filledBox) == 1
-- controls: a figure is no part from itself, and a body's marks are one part
#guard distance (figure .box) (figure .box) == 0
#guard part "main:wall" == "main" && part "u" == "u"

end Tools.View.Tube.Glyphs
