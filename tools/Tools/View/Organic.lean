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
-/

namespace Tools.View.Grow

open Tools.View

/-! ## Integers -/

/-- The integer square root by Newton's steps from `n`: the greatest `s` with `s * s ≤ n`, when
the steps settle within the fuel (`#guard`s below). -/
def isqrt (n : Nat) : Nat :=
  if n < 2 then n else
  let rec go : Nat → Nat → Nat
    | 0, x => x
    | fuel + 1, x => let y := (x + n / x) / 2; if y < x then go fuel y else x
  go 128 n

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

/-- **A smooth path through points** (Catmull-Rom's spline, as cubic segments): each segment's
controls a sixth of the way along its neighbours' chord. -/
def through (qs : List P) : List Cubic :=
  let a := qs.toArray
  let n := a.size
  let get (i : Int) : P := a[(max 0 (min i ((n : Int) - 1))).toNat]!
  (List.range (n - 1)).map fun (i : Nat) =>
    let i : Int := i
    let p0 := get (i - 1)
    let p1 := get i
    let p2 := get (i + 1)
    let p3 := get (i + 2)
    ⟨p1, (p1.1 + (p2.1 - p0.1) / 6, p1.2 + (p2.2 - p0.2) / 6),
      (p2.1 - (p3.1 - p1.1) / 6, p2.2 - (p3.2 - p1.2) / 6), p2⟩

/-- The samples of a centre line, in thousandths: each cubic of logical pixels at `n` steps, its
point and its direction. -/
def samples (n : Nat) (cs : List Cubic) : List (P × P) :=
  let scaled := cs.map (Cubic.scale 1000)
  let one (c : Cubic) (first : Bool) : List (P × P) :=
    ((List.range (n + 1)).drop (if first then 0 else 1)).map fun (k : Nat) =>
      let t : Int := k * 1000 / n
      (at_ c t, dir c t)
  (scaled.zipIdx.map fun (c, i) => one c (i == 0)).flatten

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

/-- **An organic stroke** along a centre line of logical pixels: a closed outline, in thousandths,
whose half-width is `w / 2` moved by the noise inside its band, the noise faded out at the ends.
With `tip`, the line narrows to its last point, as a growing shoot does. -/
def stroke (seed : Nat) (o : Organic) (w : Int) (cs : List Cubic) (tip : Bool) : List Cubic :=
  let ss := samples 8 cs
  match ss with
  | [] => []
  | _ =>
    -- the length along the line at each sample
    let lens := (ss.zip (ss.drop 1)).foldl (fun (acc : List Nat) ((a, _), (b, _)) =>
      acc ++ [acc.getLast?.getD 0 + dist a b]) [0]
    let S := lens.getLast?.getD 0
    let ramp := o.wave / 2
    let hw := w / 2
    let side (sd : Nat) (sign : Int) : List P :=
      (ss.zip lens).map fun ((p, d), s) =>
        let h := halfWidth hw o.noise (envelope ramp S s) (noise (seed + sd) o.wave s)
        let h := if tip && S > 0 then h * (min 1000 ((S - s) * 3000 / max 1 S + 200) : Nat) / 1000 else h
        let n := normal d
        (p.1 + sign * n.1 * h / 1000, p.2 + sign * n.2 * h / 1000)
    let left := side 0 1
    let right := (side 7 (-1)).reverse
    match left.getLast?, right.head?, right.getLast?, left.head? with
    | some le, some rh, some rl, some lh =>
      through left ++ [line le rh] ++ through right ++ [line rl lh]
    | _, _, _, _ => []

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

-- da Vinci's split is the identity for one part; for more, each part's share squared, times the
-- count, comes within a millionth's rounding of the whole: a finite evaluation
#guard split 1 = 1000000
#guard [2, 3, 4, 5, 8, 16].all fun n => n * split n * split n ≤ 1000000000000 ∧ 1000000000000 < n * (split n + 1) * (split n + 1)

end Tools.View.Grow
