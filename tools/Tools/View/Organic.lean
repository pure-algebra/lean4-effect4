import Tools.View.Picture
import Tools.View.Look

/-!
# Organic strokes: growth rules for the view's lines

The owner's request of 2026-10-09: lines that join boxes and one another as branches do, wider
where they join, their width loosely the strength of what they connect; natural noise, inside a
limited, relative width; growth rules; rounder corners. The design and its sources are in
`docs/research/2026-10-09-organic-strokes.md`. This module computes the geometry, in thousandths of
a logical pixel (a shape's points, `Call.shape`), with integer arithmetic only, so every frame and
every run draws the same.

- **da Vinci's rule** (`split`): where work runs in `n` parallel parts, each part's line is
  `1/√n` as wide, so the squares of the parts' widths sum to the whole's: "all the branches of a
  tree at every stage of its height when put together are equal in thickness to the trunk below
  them" (Prusinkiewicz and Lindenmayer, *The Algorithmic Beauty of Plants*, pp. 57–58).
- **Noise** (`noise`): smooth value noise in two octaves, each cell's value a hash of a seed and
  the cell, after the owner's `drawing_learning` noise. The seed is the line's key, so a line is
  drawn the same in every frame: variation changes a line's detail, never the structure (*The
  Algorithmic Beauty of Plants*, §1.7). Its value lies in `[-1000, 1000]` (`noise_band`).
- **The band** (`halfWidth`): the noise moves each edge of a line by at most `noise` per mille of
  its half-width, and not at all at its ends (`halfWidth_band`).
- **A collar** (`collar`): where a line meets a box or a bar it widens by a quarter circle on each
  side, as a branch widens into its trunk.
- **A growing tip** (`stroke` with `tip`): a line still being drawn narrows to its tip, as a shoot
  does; a growth function that is continuous in its age (§6.2).
- **The move law** (`stroke_move`): the stroke of a moved line is the stroke, moved. A cache of
  strokes kept at the origin rests on it (`Laid.cachedStroke_eq`, `tools/Tools/View/Graph.lean`).
-/

namespace Tools.View.Grow

open Tools.View

/-! ## Integers -/

/-- The integer square root by Newton's steps from `2 ^ (log₂ n / 2 + 1)`, which lies above `√n`:
the greatest `s` with `s * s ≤ n` (`#guard`s below). Every start above `⌊√n⌋` falls to `⌊√n⌋`, and a
start below it stops at once (the controls below). This start takes about five steps on a squared
distance in thousandths, where a start from `n` takes about twenty. -/
def isqrt (n : Nat) : Nat :=
  if n < 2 then n else
  let rec go : Nat → Nat → Nat
    | 0, x => x
    | fuel + 1, x => let y := (x + n / x) / 2; if y < x then go fuel y else x
  go 128 (1 <<< (n.log2 / 2 + 1))

/-- **da Vinci's split**: the share of each of `n` parallel parts, in millionths: `1/√n`. -/
def split (n : Nat) : Nat := if n ≤ 1 then 1000000 else isqrt (1000000000000 / n)

/-! ## Noise -/

/-- A 32-bit mix of a seed and a cell, after the hash of the owner's `drawing_learning` noise. -/
def mix (seed cell : Nat) : Nat :=
  let m := 4294967296
  let h := ((cell + 374761393) * 668265263 % m) ^^^ ((seed + 1442695041) * 2246822519 % m)
  let h := ((h ^^^ (h >>> 13)) * 1274126177) % m
  h ^^^ (h >>> 16)

/-- A cell's value, in `[-1000, 1000]`. -/
def cellValue (seed cell : Nat) : Int := ((mix seed cell % 2001 : Nat) : Int) - 1000

/-- Smoothstep per mille: `t² (3 - 2t)` for `t` in `[0, 1000]`, kept in `[0, 1000]`, which the
polynomial never leaves there. -/
def smooth (t : Int) : Int := max 0 (min 1000 (t * t * (3000 - 2 * t) / 1000000))

/-- **Value noise** at `s` along a line, with cells `wave` long: between the values of the cells
around `s`, smoothly. -/
def valueNoise (seed : Nat) (wave : Nat) (s : Nat) : Int :=
  let wave := max 1 wave
  let cell := s / wave
  let u := smooth ((s % wave * 1000 / wave : Nat) : Int)
  let a := cellValue seed cell
  let b := cellValue seed (cell + 1)
  a + (b - a) * u / 1000

/-- **The noise** at `s`: two octaves, the second at half the wavelength and half the weight. -/
def noise (seed : Nat) (wave : Nat) (s : Nat) : Int :=
  (2 * valueNoise seed wave s + valueNoise (seed + 1) (wave / 2) s) / 3

/-- A key's seed: FNV-1a over its characters' codes. -/
def seedOf (key : String) : Nat :=
  key.foldl (fun h c => ((h ^^^ c.toNat) * 16777619) % 4294967296) 2166136261

/-! ## The width of a line -/

/-- The envelope of the noise at `s` along a line `S` long: no noise at either end, full beyond
`ramp` from both, per mille. -/
def envelope (ramp S s : Nat) : Nat :=
  if ramp = 0 then 1000 else min 1000 (min (s * 1000 / ramp) ((S - s) * 1000 / ramp))

/-- **A half-width** at `s` along a line: `hw`, moved by the noise `v` at most `amp` per mille, and
by the envelope `env`. -/
def halfWidth (hw : Int) (amp env : Nat) (v : Int) : Int :=
  hw + hw * (amp : Int) / 1000 * (env : Int) / 1000 * v / 1000

/-! ## Points and paths -/

/-- A point in thousandths. -/
abbrev P := Int × Int

/-- A straight segment from `a` to `b`. -/
def line (a b : P) : Cubic := ⟨a, a, b, b⟩

/-- The circle constant of a quarter arc by one cubic, per mille: `4 (√2 - 1) / 3`. -/
def KAPPA : Int := 552

/-- **A rectangle with round corners**, in thousandths, clockwise from the top left: four sides
and four quarter arcs of radius `r`, at most half the shorter side. -/
def roundRect (x y w h r : Int) : List Cubic :=
  let r := max 0 (min r (min (w / 2) (h / 2)))
  let k := r * KAPPA / 1000
  [ line (x + r, y) (x + w - r, y),
    ⟨(x + w - r, y), (x + w - r + k, y), (x + w, y + r - k), (x + w, y + r)⟩,
    line (x + w, y + r) (x + w, y + h - r),
    ⟨(x + w, y + h - r), (x + w, y + h - r + k), (x + w - r + k, y + h), (x + w - r, y + h)⟩,
    line (x + w - r, y + h) (x + r, y + h),
    ⟨(x + r, y + h), (x + r - k, y + h), (x, y + h - r + k), (x, y + h - r)⟩,
    line (x, y + h - r) (x, y + r),
    ⟨(x, y + r), (x, y + r - k), (x + r - k, y), (x + r, y)⟩ ]

/-- **A ring with round corners**: the rectangle, less the rectangle `wt` inside it; filled by the
even-odd rule, a frame `wt` thick inside the box. -/
def ring (x y w h r wt : Int) : List (List Cubic) :=
  [roundRect x y w h r, roundRect (x + wt) (y + wt) (w - 2 * wt) (h - 2 * wt) (r - wt)]

/-- The point `t` per mille along a cubic, in its own units (de Casteljau). -/
def at_ (c : Cubic) (t : Int) : P := (c.upTo t).p3

/-- The direction of a cubic at `t` per mille: its derivative, up to a factor of three; where the
derivative vanishes (a straight segment's ends), the chord. -/
def dir (c : Cubic) (t : Int) : P :=
  let s := 1000 - t
  let d1 := (c.p1.1 - c.p0.1, c.p1.2 - c.p0.2)
  let d2 := (c.p2.1 - c.p1.1, c.p2.2 - c.p1.2)
  let d3 := (c.p3.1 - c.p2.1, c.p3.2 - c.p2.2)
  let x := (d1.1 * s * s + 2 * d2.1 * s * t + d3.1 * t * t) / 1000000
  let y := (d1.2 * s * s + 2 * d2.2 * s * t + d3.2 * t * t) / 1000000
  if x = 0 ∧ y = 0 then (c.p3.1 - c.p0.1, c.p3.2 - c.p0.2) else (x, y)

/-- A direction's unit normal to its left, per mille. -/
def normal (d : P) : P :=
  let len : Int := isqrt (d.1.natAbs * d.1.natAbs + d.2.natAbs * d.2.natAbs)
  if len = 0 then (1000, 0) else (-d.2 * 1000 / len, d.1 * 1000 / len)

/-- The Euclidean distance between two points, rounded down. -/
def dist (a b : P) : Nat := isqrt ((a.1 - b.1).natAbs ^ 2 + (a.2 - b.2).natAbs ^ 2)

/-- The segment from `p1` to `p2` of a smooth path through `p0, p1, p2, p3` (Catmull-Rom's
spline): its controls a sixth of the way along its neighbours' chord. -/
def segmentThrough (p0 p1 p2 p3 : P) : Cubic :=
  ⟨p1, (p1.1 + (p2.1 - p0.1) / 6, p1.2 + (p2.2 - p0.2) / 6),
    (p2.1 - (p3.1 - p1.1) / 6, p2.2 - (p3.2 - p1.2) / 6), p2⟩

/-- The segments of a smooth path through `p1 :: rest`, the point before `p1` being `p0`, and past
the last point the last point again. -/
def throughFrom : P → List P → List Cubic
  | p0, p1 :: p2 :: rest => segmentThrough p0 p1 p2 (rest.head?.getD p2) :: throughFrom p1 (p2 :: rest)
  | _, _ => []

/-- **A smooth path through points** (Catmull-Rom's spline, as cubic segments): each segment's
controls a sixth of the way along its neighbours' chord. Before the first point stands the first
point, and past the last point the last. -/
def through (qs : List P) : List Cubic :=
  match qs with
  | [] => []
  | q :: _ => throughFrom q qs

/-- The samples along one cubic, in its own units, at `n` steps: each point and its direction. A
line's first cubic keeps its start; each later cubic drops it, the end of the one before. -/
def sampleAlong (n : Nat) (c : Cubic) (first : Bool) : List (P × P) :=
  ((List.range (n + 1)).drop (if first then 0 else 1)).map fun (k : Nat) =>
    let t : Int := k * 1000 / n
    (at_ c t, dir c t)

/-- The samples of a centre line, in thousandths: each cubic of logical pixels at `n` steps, its
point and its direction. -/
def samples (n : Nat) (cs : List Cubic) : List (P × P) :=
  match cs with
  | [] => []
  | c :: rest =>
    sampleAlong n (c.scale 1000) true ++ rest.flatMap fun c => sampleAlong n (c.scale 1000) false

/-- **A collar** where a line `w` wide meets a surface at `(x, y)`: a quarter arc of radius `R` on
each side, from the line `R` away from the surface out along the surface. `down` when the line
leaves the surface downward. In thousandths. -/
def collar (x y w R : Int) (down : Bool) : List Cubic :=
  let s : Int := if down then 1 else -1
  let hw := w / 2
  let k := R * KAPPA / 1000
  let l0 : P := (x - hw, y + s * R)
  let l3 : P := (x - hw - R, y)
  let r0 : P := (x + hw + R, y)
  let r3 : P := (x + hw, y + s * R)
  [ ⟨l0, (x - hw, y + s * (R - k)), (x - hw - R + k, y), l3⟩,
    line l3 r0,
    ⟨r0, (x + hw + R - k, y), (x + hw, y + s * (R - k)), r3⟩,
    line r3 l0 ]

/-- The distance from each sample of a centre line to the next. -/
def steps (ss : List (P × P)) : List Nat := (ss.zip (ss.drop 1)).map fun x => dist x.1.1 x.2.1

/-- The running lengths along a centre line's samples, from `0`: each is the one before plus the
step to the next sample. They are built newest first and turned once, so `m` samples take `m`
steps, where appending each length to the end took `m²` (the check below). -/
def runningLengths (ss : List (P × P)) : List Nat :=
  ((steps ss).foldl (fun (acc : List Nat × Nat) d => ((acc.2 + d) :: acc.1, acc.2 + d)) ([0], 0)).1.reverse

/-- One point of a stroke's side: the sample's point `x.1.1`, moved along the normal of its
direction `x.1.2` by the half-width at its running length `x.2`, of a line `S` long. `sd` seeds
the side's noise, and `sign` picks the side. -/
def sidePoint (seed : Nat) (o : Organic) (hw : Int) (S : Nat) (tip : Bool) (sd : Nat) (sign : Int)
    (x : (P × P) × Nat) : P :=
  let s := x.2
  let h := halfWidth hw o.noise (envelope (o.wave / 2) S s) (noise (seed + sd) o.wave s)
  let h := if tip && S > 0 then h * (min 1000 ((S - s) * 3000 / max 1 S + 200) : Nat) / 1000 else h
  let n := normal x.1.2
  (x.1.1.1 + sign * n.1 * h / 1000, x.1.1.2 + sign * n.2 * h / 1000)

/-- **A stroke's closed outline** from its two sides, the right one turned: the left side's path,
a line across the end, the right side's path, and a line back across the start. An empty side
has no outline. -/
def outline (left right : List P) : List Cubic :=
  match left.getLast?, right.head?, right.getLast?, left.head? with
  | some le, some rh, some rl, some lh => through left ++ [line le rh] ++ through right ++ [line rl lh]
  | _, _, _, _ => []

/-- **An organic stroke** along a centre line of logical pixels: a closed outline, in thousandths,
whose half-width is `w / 2` moved by the noise inside its band, the noise faded out at the ends.
With `tip`, the line narrows to its last point, as a growing shoot does. An empty line has no
sample, so no side and no outline. -/
def stroke (seed : Nat) (o : Organic) (w : Int) (cs : List Cubic) (tip : Bool) : List Cubic :=
  let ss := samples 8 cs
  let lens := runningLengths ss
  let S := lens.getLast?.getD 0
  let side (sd : Nat) (sign : Int) : List P := (ss.zip lens).map (sidePoint seed o (w / 2) S tip sd sign)
  outline (side 0 1) (side 7 (-1)).reverse

/-! ## The laws of the band -/

theorem cellValue_band (seed cell : Nat) : -1000 ≤ cellValue seed cell ∧ cellValue seed cell ≤ 1000 := by
  unfold cellValue
  have := Nat.mod_lt (mix seed cell) (show 2001 > 0 by decide)
  refine ⟨by omega, by omega⟩

theorem smooth_band (t : Int) : 0 ≤ smooth t ∧ smooth t ≤ 1000 := by
  unfold smooth
  exact ⟨Int.le_max_left _ _, Int.max_le.mpr ⟨by decide, Int.min_le_left _ _⟩⟩

/-- A step between two values `a` and `b` stays between them. -/
theorem step_band {a b u : Int} (hu0 : 0 ≤ u) (hu1 : u ≤ 1000) :
    min a b ≤ a + (b - a) * u / 1000 ∧ a + (b - a) * u / 1000 ≤ max a b := by
  by_cases hab : a ≤ b
  · have h0 : 0 ≤ (b - a) * u := Int.mul_nonneg (by omega) hu0
    have h1 : (b - a) * u ≤ (b - a) * 1000 := Int.mul_le_mul_of_nonneg_left hu1 (by omega)
    have e0 := Int.ediv_nonneg h0 (show (0 : Int) ≤ 1000 by decide)
    have e1 := Int.ediv_le_ediv (show (0 : Int) < 1000 by decide) h1
    rw [Int.mul_ediv_cancel _ (show (1000 : Int) ≠ 0 by decide)] at e1
    generalize (b - a) * u / 1000 = m at e0 e1
    exact ⟨Int.le_trans (Int.min_le_left _ _) (by omega), Int.le_trans (by omega) (Int.le_max_right _ _)⟩
  · have h0 : (b - a) * u ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) hu0
    have h1 : (b - a) * 1000 ≤ (b - a) * u := Int.mul_le_mul_of_nonpos_left (by omega) hu1
    have e0 := Int.ediv_le_ediv (show (0 : Int) < 1000 by decide) h0
    have e1 := Int.ediv_le_ediv (show (0 : Int) < 1000 by decide) h1
    rw [Int.mul_ediv_cancel _ (show (1000 : Int) ≠ 0 by decide)] at e1
    rw [Int.zero_ediv] at e0
    generalize (b - a) * u / 1000 = m at e0 e1
    exact ⟨Int.le_trans (Int.min_le_right _ _) (by omega), Int.le_trans (by omega) (Int.le_max_left _ _)⟩

theorem valueNoise_band (seed wave s : Nat) : -1000 ≤ valueNoise seed wave s ∧ valueNoise seed wave s ≤ 1000 := by
  dsimp only [valueNoise]
  have ha := cellValue_band seed (s / max 1 wave)
  have hb := cellValue_band seed (s / max 1 wave + 1)
  have hu := smooth_band ((s % max 1 wave * 1000 / max 1 wave : Nat) : Int)
  have := step_band (a := cellValue seed (s / max 1 wave)) (b := cellValue seed (s / max 1 wave + 1)) hu.1 hu.2
  generalize cellValue seed (s / max 1 wave) = a at ha this
  generalize cellValue seed (s / max 1 wave + 1) = b at hb this
  generalize a + (b - a) * smooth ((s % max 1 wave * 1000 / max 1 wave : Nat) : Int) / 1000 = v at this
  have h1 : -1000 ≤ min a b := Int.le_min.mpr ⟨ha.1, hb.1⟩
  have h2 : max a b ≤ 1000 := Int.max_le.mpr ⟨ha.2, hb.2⟩
  exact ⟨Int.le_trans h1 this.1, Int.le_trans this.2 h2⟩

/-- **The noise stays in its band**: `[-1000, 1000]`. -/
theorem noise_band (seed wave s : Nat) : -1000 ≤ noise seed wave s ∧ noise seed wave s ≤ 1000 := by
  unfold noise
  have h1 := valueNoise_band seed wave s
  have h2 := valueNoise_band (seed + 1) (wave / 2) s
  generalize valueNoise seed wave s = x at h1
  generalize valueNoise (seed + 1) (wave / 2) s = y at h2
  have lo := Int.ediv_le_ediv (show (0 : Int) < 3 by decide) (show (-3000 : Int) ≤ 2 * x + y by omega)
  have hi := Int.ediv_le_ediv (show (0 : Int) < 3 by decide) (show 2 * x + y ≤ (3000 : Int) by omega)
  have e1 : (-3000 : Int) / 3 = -1000 := by decide
  have e2 : (3000 : Int) / 3 = 1000 := by decide
  rw [e1] at lo; rw [e2] at hi
  exact ⟨lo, hi⟩

/-- A product, divided by a thousand, of a value no less than zero and a factor in `[0, 1000]`
stays between zero and the value. -/
theorem scale_band {a f : Int} (ha : 0 ≤ a) (hf0 : 0 ≤ f) (hf1 : f ≤ 1000) : 0 ≤ a * f / 1000 ∧ a * f / 1000 ≤ a := by
  have h1 : a * f ≤ a * 1000 := Int.mul_le_mul_of_nonneg_left hf1 ha
  have e1 := Int.ediv_le_ediv (show (0 : Int) < 1000 by decide) h1
  rw [Int.mul_ediv_cancel _ (show (1000 : Int) ≠ 0 by decide)] at e1
  exact ⟨Int.ediv_nonneg (Int.mul_nonneg ha hf0) (by decide), e1⟩

/-- **The half-width stays in its band**: for a half-width `hw ≥ 0`, an amplitude and an envelope
per mille, and a noise in its band, the moved half-width differs from `hw` by at most `hw` times
the amplitude per mille. "A limited, relative width": a tool's named law, whose consumer is the
drawing of every organic stroke. -/
theorem halfWidth_band {hw : Int} {amp env : Nat} {v : Int} (hw0 : 0 ≤ hw) (hamp : amp ≤ 1000) (henv : env ≤ 1000)
    (hv : -1000 ≤ v ∧ v ≤ 1000) :
    hw - hw * (amp : Int) / 1000 ≤ halfWidth hw amp env v ∧ halfWidth hw amp env v ≤ hw + hw * (amp : Int) / 1000 := by
  unfold halfWidth
  have a := scale_band hw0 (Int.natCast_nonneg amp) (by omega)
  generalize hw * (amp : Int) / 1000 = A at a ⊢
  have b := scale_band a.1 (Int.natCast_nonneg env) (by omega)
  generalize A * (env : Int) / 1000 = B at b ⊢
  -- B * v / 1000 lies in [-B, B]
  have h1 : B * v ≤ B * 1000 := Int.mul_le_mul_of_nonneg_left hv.2 b.1
  have h2 : B * (-1000) ≤ B * v := Int.mul_le_mul_of_nonneg_left hv.1 b.1
  have e1 := Int.ediv_le_ediv (show (0 : Int) < 1000 by decide) h1
  have e2 := Int.ediv_le_ediv (show (0 : Int) < 1000 by decide) h2
  rw [Int.mul_ediv_cancel _ (show (1000 : Int) ≠ 0 by decide)] at e1
  rw [show B * (-1000) = -B * 1000 by rw [Int.mul_neg, Int.neg_mul], Int.mul_ediv_cancel _ (show (1000 : Int) ≠ 0 by decide)] at e2
  generalize B * v / 1000 = C at e1 e2
  exact ⟨by omega, by omega⟩

/-! ## The move law of a stroke

A stroke reads its centre line through its samples. A move of the line by whole logical pixels
moves each sample's point by a thousand times as much, in thousandths, and keeps its direction
(`samples_move`). Every later step reads a difference of two points (`dist`, `dir`) or adds an
offset to a point (`sidePoint`, `segmentThrough`, `line`). So the stroke of a moved line is the
stroke, moved (`stroke_move`).

The laws are a tool's, not registry claims (decisions row 334, point 3). They serve concept
`initial-algebras-folds` and R14's live authoring. Their consumer is the stroke cache
(`Laid.cachedStroke_eq`, `tools/Tools/View/Graph.lean`), which keeps a stroke at the origin and
serves it moved. -/

/-- A point moved by `d`. -/
def shift (d : P) (p : P) : P := (p.1 + d.1, p.2 + d.2)

/-- A sample moved by `d`: its point moved, its direction kept. -/
def shiftSample (d : P) (x : P × P) : P × P := (shift d x.1, x.2)

/-- A step between two moved values is the step, moved. A step of `stroke_move`. -/
theorem lerp_shift (u v e d : Int) : lerp (u + d) (v + d) e = lerp u v e + d := by
  simp only [lerp, Int.add_sub_add_right]
  exact Int.add_right_comm v d _

/-- A moved cubic's part up to `t` is the part, moved. A step of `stroke_move`. -/
theorem upTo_move (t dx dy : Int) (c : Cubic) : (c.move dx dy).upTo t = (c.upTo t).move dx dy := by
  simp only [Cubic.upTo, Cubic.move, lerpPt, lerp_shift]

/-- A moved cubic's point at `t` is the point, moved. A step of `stroke_move`. -/
theorem at_move (t dx dy : Int) (c : Cubic) : at_ (c.move dx dy) t = shift (dx, dy) (at_ c t) := by
  show ((c.move dx dy).upTo t).p3 = _
  rw [upTo_move]
  rfl

/-- A moved cubic's direction at `t` is the direction. A step of `stroke_move`. -/
theorem dir_move (t dx dy : Int) (c : Cubic) : dir (c.move dx dy) t = dir c t := by
  simp only [dir, Cubic.move, Int.add_sub_add_right]

/-- A moved cubic's samples are the samples, moved. A step of `stroke_move`. -/
theorem sampleAlong_move (n : Nat) (c : Cubic) (first : Bool) (dx dy : Int) :
    sampleAlong n (c.move dx dy) first = (sampleAlong n c first).map (shiftSample (dx, dy)) := by
  simp only [sampleAlong, List.map_map]
  apply List.map_congr_left
  intro k _
  simp only [Function.comp, at_move, dir_move, shiftSample]

/-- **A moved line's samples are the samples, moved** a thousand times as far, in thousandths. A
step of `stroke_move`. -/
theorem samples_move (n : Nat) (cs : List Cubic) (dx dy : Int) :
    samples n (cs.map (Cubic.move dx dy)) = (samples n cs).map (shiftSample (1000 * dx, 1000 * dy)) := by
  cases cs with
  | nil => rfl
  | cons c rest =>
    simp only [List.map_cons, samples, Cubic.scale_move, sampleAlong_move, List.map_append,
      List.flatMap_map, List.map_flatMap]

/-- The distance between two moved points is their distance. A step of `stroke_move`. -/
theorem dist_shift (d a b : P) : dist (shift d a) (shift d b) = dist a b := by
  simp only [dist, shift, Int.add_sub_add_right]

/-- Moved samples take the same steps. A step of `stroke_move`. -/
theorem steps_shift (d : P) (ss : List (P × P)) : steps (ss.map (shiftSample d)) = steps ss := by
  simp only [steps, ← List.map_drop, List.zip_map, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp, Prod.map, shiftSample, dist_shift]

/-- Moved samples have the same running lengths. A step of `stroke_move`. -/
theorem runningLengths_shift (d : P) (ss : List (P × P)) :
    runningLengths (ss.map (shiftSample d)) = runningLengths ss := by
  simp only [runningLengths, steps_shift]

/-- A side's point at a moved sample is the point, moved. A step of `stroke_move`. -/
theorem sidePoint_shift (seed : Nat) (o : Organic) (hw : Int) (S : Nat) (tip : Bool) (sd : Nat)
    (sign : Int) (d : P) (x : (P × P) × Nat) :
    sidePoint seed o hw S tip sd sign (shiftSample d x.1, x.2) =
      shift d (sidePoint seed o hw S tip sd sign x) := by
  simp only [sidePoint, shiftSample, shift]
  rw [Int.add_right_comm x.1.1.1 d.1, Int.add_right_comm x.1.1.2 d.2]

/-- A side of moved samples is the side, moved. A step of `stroke_move`. -/
theorem side_shift (seed : Nat) (o : Organic) (hw : Int) (S : Nat) (tip : Bool) (sd : Nat)
    (sign : Int) (d : P) (l : List ((P × P) × Nat)) :
    (l.map (Prod.map (shiftSample d) id)).map (sidePoint seed o hw S tip sd sign) =
      (l.map (sidePoint seed o hw S tip sd sign)).map (shift d) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro x _
  exact sidePoint_shift seed o hw S tip sd sign d x

/-- A sum, less a term, is the difference plus the sum's second term. A step of
`segmentThrough_shift`. -/
theorem add_sub_right_comm (a b c : Int) : a + b - c = a - c + b := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.add_right_comm]

/-- A segment through moved points is the segment, moved. A step of `stroke_move`. -/
theorem segmentThrough_shift (d p0 p1 p2 p3 : P) :
    segmentThrough (shift d p0) (shift d p1) (shift d p2) (shift d p3) =
      (segmentThrough p0 p1 p2 p3).move d.1 d.2 := by
  simp only [segmentThrough, shift, Cubic.move, Int.add_sub_add_right]
  simp only [Int.add_right_comm _ d.1, Int.add_right_comm _ d.2, add_sub_right_comm _ d.1,
    add_sub_right_comm _ d.2]

/-- A path through moved points is the path, moved. A step of `stroke_move`. -/
theorem throughFrom_shift (d : P) : ∀ (p0 : P) (qs : List P),
    throughFrom (shift d p0) (qs.map (shift d)) = (throughFrom p0 qs).map (Cubic.move d.1 d.2)
  | p0, p1 :: p2 :: rest => by
    have hp3 : (rest.map (shift d)).head?.getD (shift d p2) = shift d (rest.head?.getD p2) := by
      cases rest <;> rfl
    simp only [List.map_cons, throughFrom, hp3, segmentThrough_shift]
    rw [← List.map_cons, throughFrom_shift d p1 (p2 :: rest)]
  | _, [] => rfl
  | _, [_] => rfl

/-- A smooth path through moved points is the path, moved. A step of `stroke_move`. -/
theorem through_shift (d : P) (qs : List P) :
    through (qs.map (shift d)) = (through qs).map (Cubic.move d.1 d.2) := by
  cases qs with
  | nil => rfl
  | cons q rest =>
    simp only [List.map_cons, through]
    rw [← List.map_cons]
    exact throughFrom_shift d q (q :: rest)

/-- A line between moved points is the line, moved. A step of `stroke_move`. -/
theorem line_shift (d a b : P) : line (shift d a) (shift d b) = (line a b).move d.1 d.2 := rfl

/-- An outline of moved sides is the outline, moved. A step of `stroke_move`. -/
theorem outline_shift (d : P) (left right : List P) :
    outline (left.map (shift d)) (right.map (shift d)) = (outline left right).map (Cubic.move d.1 d.2) := by
  unfold outline
  rw [List.getLast?_map, List.head?_map, List.getLast?_map, List.head?_map]
  cases left.getLast? <;> cases right.head? <;> cases right.getLast? <;> cases left.head? <;>
    simp only [Option.map_none, Option.map_some, List.map_nil, List.map_append, List.map_cons,
      through_shift, line_shift]

/-- **The move law of a stroke.** The stroke of a centre line moved by `(dx, dy)` logical pixels is
the stroke moved by `(1000 dx, 1000 dy)` thousandths. For every seed, organic settings, width,
line and tip: no step of a stroke reads where the line stands. A tool's law; its consumer is the
stroke cache (`Laid.cachedStroke_eq`). Placement: concept `initial-algebras-folds`, R14's live
authoring. -/
theorem stroke_move (seed : Nat) (o : Organic) (w : Int) (cs : List Cubic) (tip : Bool) (dx dy : Int) :
    stroke seed o w (cs.map (Cubic.move dx dy)) tip =
      (stroke seed o w cs tip).map (Cubic.move (1000 * dx) (1000 * dy)) := by
  simp only [stroke, samples_move, runningLengths_shift, List.zip_map_left, side_shift]
  rw [← List.map_reverse, outline_shift]

/-- A stroke reads its organic settings' noise and wave alone. A step of the stroke cache's law
(`Laid.cachedStroke_eq`), whose key keeps these two. -/
theorem stroke_organic (seed : Nat) {o o' : Organic} (hn : o.noise = o'.noise) (hw : o.wave = o'.wave)
    (w : Int) (cs : List Cubic) (tip : Bool) : stroke seed o w cs tip = stroke seed o' w cs tip := by
  have side : sidePoint seed o = sidePoint seed o' := by
    funext hw' S tip' sd sign x
    simp only [sidePoint, hn, hw]
  simp only [stroke, side]

-- da Vinci's split is the identity for one part; for more, each part's share squared, times the
-- count, comes within a millionth's rounding of the whole: a finite evaluation
#guard split 1 = 1000000
#guard [2, 3, 4, 5, 8, 16].all fun n => n * split n * split n ≤ 1000000000000 ∧ 1000000000000 < n * (split n + 1) * (split n + 1)

-- `isqrt` answers the greatest `s` with `s * s ≤ n`: at every value below 2^15; at the powers of two
-- to 2^60, their neighbours, their squares and the squares' neighbours; and at four large values.
-- A finite evaluation.
#guard (List.range 32768).all fun n => let s := isqrt n; s * s ≤ n && n < (s + 1) * (s + 1)
#guard (List.range 61).all fun k =>
  let p := 2 ^ k
  [p - 1, p, p + 1, p * p - 1, p * p, p * p + 1, 3 * p + 7].all fun n =>
    let s := isqrt n; s * s ≤ n && n < (s + 1) * (s + 1)
#guard [999999999999, 1000000000000, 123456789012345, 4611686018427387903].all fun n =>
  let s := isqrt n; s * s ≤ n && n < (s + 1) * (s + 1)
-- The controls: Newton's steps from a start below the root stop at the start. So the start must
-- lie above `√n`: without its `+ 1`, the start for 15 is 2, below the root 3.
#guard isqrt.go 100 128 1 == 1
#guard isqrt.go 15 128 (1 <<< (Nat.log2 15 / 2)) == 2
#guard isqrt 15 == 3

/-- Centre lines for the checks of the running lengths: none, a straight drop, a bump and a
straight run, and a back arc. -/
def lengthSpecimens : List (List Cubic) :=
  [[], [line (0, 0) (0, 30)], [⟨(0, 0), (0, 12), (40, 18), (40, 30)⟩, line (40, 30) (40, 60)],
    [⟨(120, 40), (171, 40), (171, 230), (120, 230)⟩]]

-- The running lengths built newest first are the lengths built by appending each to the end, on
-- each specimen's samples. The control: unturned, they stand newest first.
#guard lengthSpecimens.all fun cs =>
  let ss := samples 8 cs
  runningLengths ss == (ss.zip (ss.drop 1)).foldl (fun (acc : List Nat) ((a, _), (b, _)) =>
    acc ++ [acc.getLast?.getD 0 + dist a b]) [0]
#guard let ss := samples 8 [line (0, 0) (0, 30)]
  ((steps ss).foldl (fun (acc : List Nat × Nat) d => ((acc.2 + d) :: acc.1, acc.2 + d)) ([0], 0)).1 !=
    runningLengths ss

end Tools.View.Grow
