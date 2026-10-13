/-!
# Tools.View.Tube.Trig — sines and cosines in whole numbers

A tube turns by angles (`Tools.View.Tube.Form`), so drawing one needs the sine and the cosine of
an angle, and two ratios that stay finite where the angle vanishes: `sin x / x` and `tan x / x`.
Each is its Taylor series, summed in whole numbers at a scale of `10¹²` and rounded to `10⁹`.

* An angle is in millionths of a radian; `PI` is π to that precision.
* `sinCos` brings an angle into `[−π/2, π/2]` by `sin(π − x) = sin x` and `cos(π − x) = −cos x`,
  where fourteen terms leave an error below `10⁻⁹`.
* `sinc x = sin x / x` and `tanc x = tan x / x` are the series without the division, so a
  straight piece (no turn) needs no case of its own.
-/

namespace Tools.View.Tube

/-- π, in millionths of a radian. -/
def PI : Int := 3141593
/-- π / 2, in millionths of a radian. -/
def HALF_PI : Int := 1570796
/-- 2π, in millionths of a radian. -/
def TWO_PI : Int := 6283185

/-- The scale of a result: one is `10⁹`. -/
def ONE : Int := 1000000000
/-- The scale of a series' argument and terms: one is `10¹²`. -/
def X : Int := 1000000000000

/-- An angle brought into `(−π, π]`. -/
def reduce (a : Int) : Int :=
  let r := a % TWO_PI
  if r > PI then r - TWO_PI else r

/-- The series `Σ (−1)ᵏ x²ᵏ / ((e+1)(e+2)…(2k+e))`, starting from `first`, at the scale `X`:
the sine's terms for `e = 1`, the cosine's for `e = 0`. Fourteen terms. -/
def series (x first : Int) (e : Nat) : Int :=
  let x2 := x * x / X
  ((List.range 14).foldl (fun (acc : Int × Int) (k : Nat) =>
    let d : Int := ((2 * k + 1 + e) * (2 * k + 2 + e) : Nat)
    let t := -acc.1 * x2 / X / d
    (t, acc.2 + t)) (first, first)).2

/-- **The sine and cosine of an angle** in millionths of a radian, at the scale `ONE`. -/
def sinCos (a : Int) : Int × Int :=
  let r := reduce a
  let (r', back) :=
    if r > HALF_PI then (PI - r, true) else if r < -HALF_PI then (-PI - r, true) else (r, false)
  let x := r' * 1000000
  let s := series x x 1 / 1000
  let c := series x X 0 / 1000
  (s, if back then -c else c)

/-- **`sin x / x`**, at the scale `ONE`, for `x` in millionths of a radian; one at zero. -/
def sinc (a : Int) : Int := series (a * 1000000) X 1 / 1000

/-- **`tan x / x`**, at the scale `ONE`, for `|x| < π/2`; one at zero. -/
def tanc (a : Int) : Int := sinc a * ONE / (sinCos a).2

-- the sine of π/6 is a half, of π/2 one; the cosine of π is minus one; each within 10⁻⁶
#guard ((sinCos 523599).1 - 500000000).natAbs < 1000
#guard ((sinCos HALF_PI).1 - ONE).natAbs < 1000
#guard ((sinCos PI).2 + ONE).natAbs < 1000
#guard ((sinCos (-2 * PI / 3)).2 + 500000000).natAbs < 1000
-- a full turn is no turn
#guard ((sinCos (TWO_PI + 523599)).1 - 500000000).natAbs < 1000
-- sin(π/2)/(π/2) = 2/π, and tan(π/4)/(π/4) = 4/π
#guard (sinc HALF_PI - 636619772).natAbs < 1000
#guard (tanc 785398 - 1273239545).natAbs < 2000
#guard sinc 0 == ONE && tanc 0 == ONE

end Tools.View.Tube
