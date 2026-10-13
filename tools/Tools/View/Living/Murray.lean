import Tools.View.Organic

/-!
# Tools.View.Living.Murray — where a vessel splits: radii by the cube law, angles by the force triangle

Murray's principle of minimum work ("The physiological principle of minimum work", *PNAS* 12,
1926, and its sequel on the angles of branching) sets two things where a vessel splits.

**The radii.** At the optimum a vessel's flow goes as the cube of its radius, so where a parent of
radius `r₀` splits into `r₁` and `r₂`, `r₀³ = r₁³ + r₂³`: the flows add. Here a radius is the cube
root of its flow (`radius`), so the cubes add exactly as the flows do (`flows_add`).

**The angles.** The optimum balances three vectors along the three vessels whose lengths go as the
squares of their radii, so `r₀²`, `r₁²` and `r₂²` close a triangle, and its angles are the
branches' angles to the parent's axis. By the law of cosines,
`cos θ₁ = (r₀⁴ + r₁⁴ − r₂⁴) / (2 r₀² r₁²)` and the same with the daughters exchanged. A split into
two equal daughters leaves each at about 37.5° to the axis (`cos θ = 2^(−1/3)`), the 75° that Hess
measured and Murray explained (arXiv adap-org/9909003 surveys it; the formula is reconstructed from
the force triangle and recalled as Murray's, not checked against the 1926 text). The thinner
daughter bends further, toward a right angle as it vanishes.

No trigonometry is computed: the cosine is a ratio of whole numbers, the sine its complement's
root, and a direction turns by the two.

**Where the law is drawn, and where the share is.** A vessel's sheath follows the cube law: its
form and its angles are natural. The quantity it carries is its core, drawn as wide as its share
of the flow, so the cores of a split add exactly as the flows do (`Organism.cores`): the reader
reads quantity from the core and life from the sheath.
-/

namespace Tools.View.Living.Murray
open Tools.View

/-- **The cube root**, rounded down, by Newton's method from above. -/
def icbrt (n : Nat) : Nat :=
  if n < 2 then n else
  let rec go : Nat → Nat → Nat
    | 0, x => x
    | fuel + 1, x =>
      let y := (2 * x + n / (x * x)) / 3
      if y < x then go fuel y else x
  go 200 (1 <<< (n.log2 / 3 + 1))

#guard icbrt 27 == 3
#guard icbrt 26 == 2
#guard icbrt 1000000000 == 1000

/-- **A vessel's radius from its flow**, in thousandths: the cube root of the flow. -/
def radius (q : Nat) : Nat := icbrt (q * 1000000000)

/-- The flows of a split add: what the law of the radii says of the cubes. A split's parent
carries its daughters' flows. -/
theorem flows_add (q₁ q₂ : Nat) : (q₁ + q₂) * 1000000000 = q₁ * 1000000000 + q₂ * 1000000000 :=
  Nat.add_mul q₁ q₂ 1000000000

/-- **The cosine of a daughter's angle to the parent's axis**, in thousandths, from the three
radii in thousandths: the law of cosines in the triangle of their squares. -/
def cosAngle (r₀ r₁ r₂ : Nat) : Int :=
  let a : Int := r₀ * r₀
  let b : Int := r₁ * r₁
  let c : Int := r₂ * r₂
  if a == 0 || b == 0 then 0 else
  max (-1000) (min 1000 ((a * a + b * b - c * c) * 1000 / (2 * a * b)))

/-- The sine from the cosine, in thousandths. -/
def sinOf (cos : Int) : Int := (Grow.isqrt (1000000 - cos * cos).toNat : Int)

/-- **The angles of a split by its flows**: the cosine and sine of each daughter's angle to the
parent's axis, the first daughter's first. -/
def split (q₁ q₂ : Nat) : (Int × Int) × (Int × Int) :=
  let r₀ := radius (q₁ + q₂)
  let r₁ := radius q₁
  let r₂ := radius q₂
  let c₁ := cosAngle r₀ r₁ r₂
  let c₂ := cosAngle r₀ r₂ r₁
  ((c₁, sinOf c₁), (c₂, sinOf c₂))

/-- A direction turned by an angle given by its cosine and sine in thousandths, the direction in
thousandths too. -/
def turn (d : Int × Int) (cs : Int × Int) : Int × Int :=
  ((d.1 * cs.1 - d.2 * cs.2) / 1000, (d.1 * cs.2 + d.2 * cs.1) / 1000)

-- an even split: each daughter at about 37.5° (cos 0.794)
#guard (split 1 1).1.1 ≥ 790 && (split 1 1).1.1 ≤ 798
-- three to one: the thick daughter stays near the axis, the thin one bends further
#guard (split 3 1).1.1 > (split 3 1).2.1
-- by hand: r₀ = 4^⅓ ≈ 1.587, r₁ = 3^⅓ ≈ 1.442, r₂ = 1, so cos θ₁ = (6.35 + 4.33 − 1) / (2 · 2.52 · 2.08) ≈ 0.923
#guard (split 3 1).1.1 ≥ 918 && (split 3 1).1.1 ≤ 926

end Tools.View.Living.Murray
