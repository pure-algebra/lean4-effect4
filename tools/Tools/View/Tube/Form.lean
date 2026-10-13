import Tools.View.Picture
import Tools.View.Tube.Trig

/-!
# Tools.View.Tube.Form — one body for every glyph, and the morph between any two

Every glyph of the tube language is drawn as tubes: a centreline swept by a disc of one width, as
a pipe, a vessel, a valve's plug or a unit of contents is. A tube is given **intrinsically**: where
it starts, its heading there, its width, and its pieces, each a length along the centreline and the
angle it turns by over that length (an arc, or a straight run where the angle is zero).

**The bend law.** No piece bends tighter than one radius, `BEND` (24 px), whatever the tube: a transit map
draws every corner at one radius, and a long-radius pipe elbow bends at one and a half times its
size (ASME B16.9). For a piece of length `ℓ` turning `θ` the law is `BEND · |θ| ≤ ℓ`, and a piece
turns at most half a turn, so each half of it is drawn as one cubic of at most a quarter turn
(`Piece.ok`).

**The morph.** The law is linear in `(ℓ, θ)` and holds at zero, so the pieces that keep it form a
convex cone. A morph mixes two tubes piece by piece, `(1000 − t)` thousandths of the one and `t` of
the other, so every moment of a morph between two tubes that keep the law keeps it too
(`Piece.mix_ok`, `Tube.mix_ok`), and a morph starts and ends at its two tubes (`Piece.mix_zero`,
`Piece.mix_full`). Mixing what a shape *is* (its lengths and turns) and not where its points stand
is Sederberg, Gao, Wang and Mu's intrinsic blending ("2-D shape blending: an intrinsic solution to
the vertex path problem", SIGGRAPH 1993): a turning shape does not shrink on the way, and no kink
appears that neither end has. A tube of fewer pieces is padded with pieces of no length, which
keep the law and draw nothing, so any two tubes morph; and a tube grows from nothing by a morph
from its pieces at no length.

The rounding keeps the law exactly: a length is rounded up and a turn toward zero.
-/

namespace Tools.View.Tube
open Tools.View

/-- The most a piece turns: half a turn, in millionths of a radian. -/
def HALF_TURN : Nat := 3141593
/-- **The least radius of a bend**, in thousandths of a pixel: one for every tube. It is a long
radius, about one and a half times a pipe's body, as a long-radius elbow's is (ASME B16.9), so the
inside of a bend of a solid body is round too (decisions row 370). -/
def BEND : Nat := 24000

/-- **A piece of a centreline**: its length in thousandths of a pixel, and the angle it turns by
over that length in millionths of a radian, positive clockwise on the page. -/
structure Piece where
  len : Nat
  turn : Int
deriving Repr, DecidableEq, Inhabited

/-- **The bend law**: at most half a turn, and no tighter than `BEND`. -/
def Piece.ok (p : Piece) : Prop :=
  p.turn.natAbs ≤ HALF_TURN ∧ p.turn.natAbs * BEND ≤ p.len * 1000000

instance : DecidablePred Piece.ok := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- A piece of no length: it draws nothing. -/
def Piece.zero : Piece := ⟨0, 0⟩

theorem Piece.zero_ok : Piece.zero.ok := by
  simp only [Piece.ok, Piece.zero, HALF_TURN, BEND]
  decide

/-- A whole number's thousandth, rounded toward zero. -/
def tdiv (s : Int) : Int :=
  if 0 ≤ s then ((s.natAbs / 1000 : Nat) : Int) else -((s.natAbs / 1000 : Nat) : Int)

theorem natAbs_tdiv (s : Int) : (tdiv s).natAbs = s.natAbs / 1000 := by
  unfold tdiv
  split <;> omega

theorem tdiv_mul (x : Int) : tdiv (1000 * x) = x := by
  unfold tdiv
  split <;> omega

/-- `t` thousandths of the way from `a` to `b`, rounded toward zero. -/
def mixInt (a b : Int) (t : Nat) : Int := tdiv (((1000 - t : Nat) : Int) * a + (t : Int) * b)

/-- **Two pieces mixed**: `t` thousandths of the way from `p` to `q`, the length rounded up and
the turn toward zero. -/
def Piece.mix (p q : Piece) (t : Nat) : Piece :=
  ⟨((1000 - t) * p.len + t * q.len + 999) / 1000, mixInt p.turn q.turn t⟩

/-- A thousandth rounded down, times the bend, is at most the bend's share of the whole. A step
of `Piece.mix_ok`. -/
theorem div_bend (A : Nat) : A / 1000 * BEND ≤ A * 24 := by
  simp only [BEND]
  omega

/-- A length rounded up to whole thousandths keeps what it rounds. A step of `Piece.mix_ok`. -/
theorem up_mul (Y : Nat) : Y * 1000 ≤ (Y + 999) / 1000 * 1000000 := by
  have h := Nat.mul_le_mul_right 1000 (show Y ≤ (Y + 999) / 1000 * 1000 by omega)
  rwa [Nat.mul_assoc] at h

/-- The bend law survives the rounding of a mix: a turn rounded toward zero, a length up. A step
of `Piece.mix_ok`. -/
theorem round_bend (A Y : Nat) (h : A * BEND ≤ Y * 1000000) :
    A / 1000 * BEND ≤ (Y + 999) / 1000 * 1000000 := by
  have h1 : A * 24 ≤ Y * 1000 := by
    simp only [BEND] at h
    omega
  exact Nat.le_trans (div_bend A) (Nat.le_trans h1 (up_mul Y))

/-- **Every moment of a morph keeps the bend law**: the law's pieces form a convex cone. -/
theorem Piece.mix_ok {p q : Piece} {t : Nat} (ht : t ≤ 1000) (hp : p.ok) (hq : q.ok) :
    (p.mix q t).ok := by
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  simp only [Piece.ok, Piece.mix, mixInt, natAbs_tdiv] at *
  have key := Int.natAbs_add_le (((1000 - t : Nat) : Int) * p.turn) ((t : Int) * q.turn)
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at key
  have a1 := Nat.mul_le_mul_left (1000 - t) hp1
  have a2 := Nat.mul_le_mul_left t hq1
  have b1 := Nat.mul_le_mul_left (1000 - t) hp2
  have b2 := Nat.mul_le_mul_left t hq2
  rw [← Nat.mul_assoc, ← Nat.mul_assoc] at b1 b2
  -- the products are the atoms: what each tube gives the mix
  generalize (((1000 - t : Nat) : Int) * p.turn + (t : Int) * q.turn).natAbs = A at *
  generalize (1000 - t) * p.turn.natAbs = X1 at *
  generalize t * q.turn.natAbs = X2 at *
  generalize (1000 - t) * p.len = Y1 at *
  generalize t * q.len = Y2 at *
  have hw : (1000 - t) * HALF_TURN + t * HALF_TURN = 1000 * HALF_TURN := by
    rw [← Nat.add_mul]; congr 1; omega
  constructor
  · have : A ≤ 1000 * HALF_TURN := by omega
    omega
  · have hA : A * BEND ≤ (Y1 + Y2) * 1000000 := by
      have := Nat.mul_le_mul_right BEND key
      rw [Nat.add_mul] at this
      omega
    exact round_bend A (Y1 + Y2) hA

theorem mixInt_zero (a b : Int) : mixInt a b 0 = a := by
  unfold mixInt tdiv
  simp only [Nat.sub_zero, Int.natCast_zero, Int.zero_mul, Int.add_zero]
  split <;> omega

theorem mixInt_full (a b : Int) : mixInt a b 1000 = b := by
  unfold mixInt tdiv
  simp only [Nat.sub_self, Int.natCast_zero, Int.zero_mul, Int.zero_add]
  split <;> omega

/-- A morph starts at its first piece. -/
theorem Piece.mix_zero (p q : Piece) : p.mix q 0 = p := by
  cases p
  simp only [Piece.mix, mixInt_zero, Piece.mk.injEq, and_true]
  omega

/-- A morph ends at its second piece. -/
theorem Piece.mix_full (p q : Piece) : p.mix q 1000 = q := by
  cases q
  simp only [Piece.mix, mixInt_full, Piece.mk.injEq, and_true]
  omega

/-- **A tube**: where it starts and its heading there (thousandths of a pixel, millionths of a
radian), the width of its bore (thousandths of a pixel), and its pieces. -/
structure Tube where
  x : Int
  y : Int
  head : Int
  bore : Nat
  pieces : List Piece
deriving Repr, DecidableEq, Inhabited

/-- A tube keeps the bend law in every piece. -/
def Tube.ok (t : Tube) : Prop := ∀ p ∈ t.pieces, p.ok

instance : DecidablePred Tube.ok := fun t => inferInstanceAs (Decidable (∀ p ∈ t.pieces, p.ok))

/-- Pieces padded with pieces of no length up to `n`. -/
def pad (n : Nat) (ps : List Piece) : List Piece := ps ++ List.replicate (n - ps.length) Piece.zero

theorem pad_ok {n : Nat} {ps : List Piece} (h : ∀ p ∈ ps, p.ok) : ∀ p ∈ pad n ps, p.ok := by
  intro p hp
  rcases List.mem_append.mp hp with h1 | h2
  · exact h p h1
  · rw [List.eq_of_mem_replicate h2]
    exact Piece.zero_ok

theorem zipWith_mix_ok {t : Nat} (ht : t ≤ 1000) :
    ∀ (ps qs : List Piece), (∀ p ∈ ps, p.ok) → (∀ q ∈ qs, q.ok) →
      ∀ r ∈ List.zipWith (fun p q => p.mix q t) ps qs, r.ok
  | [], _, _, _, r, hr => by simp only [List.zipWith_nil_left, List.not_mem_nil] at hr
  | _ :: _, [], _, _, r, hr => by simp only [List.zipWith_nil_right, List.not_mem_nil] at hr
  | p :: ps, q :: qs, hp, hq, r, hr => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact Piece.mix_ok ht (hp p (List.mem_cons_self ..)) (hq q (List.mem_cons_self ..))
    · exact zipWith_mix_ok ht ps qs (fun x hx => hp x (List.mem_cons_of_mem _ hx))
        (fun x hx => hq x (List.mem_cons_of_mem _ hx)) r hr

/-- **Two tubes mixed**: the start, the heading and the bore `t` thousandths of the way, and the
pieces mixed one by one, the shorter list padded with pieces of no length. -/
def Tube.mix (a b : Tube) (t : Nat) : Tube :=
  let n := max a.pieces.length b.pieces.length
  { x := mixInt a.x b.x t, y := mixInt a.y b.y t, head := mixInt a.head b.head t
    bore := ((1000 - t) * a.bore + t * b.bore) / 1000
    pieces := List.zipWith (fun p q => p.mix q t) (pad n a.pieces) (pad n b.pieces) }

/-- **Every moment of a morph between two tubes is a tube**: it keeps the bend law. -/
theorem Tube.mix_ok {a b : Tube} {t : Nat} (ht : t ≤ 1000) (ha : a.ok) (hb : b.ok) :
    (a.mix b t).ok :=
  zipWith_mix_ok ht _ _ (pad_ok ha) (pad_ok hb)

/-! ## Drawing a tube -/

/-- The unit vector at an angle, at the scale `ONE`. -/
def dir (a : Int) : Int × Int := let (s, c) := sinCos a; (c, s)

/-- A point moved `len` thousandths of a pixel along the angle `a`. -/
def step (p : Int × Int) (len : Int) (a : Int) : Int × Int :=
  let (c, s) := dir a
  (p.1 + len * c / ONE, p.2 + len * s / ONE)

/-- **A piece drawn** from a point and a heading: its two halves, each an arc of a quarter of
its turn at most, as cubics (the handle `(ℓ/6) · tan(θ/8) / (θ/8)` of a circular arc, the chord
`(ℓ/2) · sin(θ/4) / (θ/4)`), and the point and heading where it ends. In thousandths of a pixel. -/
def Piece.draw (p : Piece) (at_ : Int × Int) (head : Int) : List Cubic × (Int × Int) × Int :=
  let ℓ : Int := p.len
  let θ := p.turn
  let chord := ℓ / 2 * sinc (θ / 4) / ONE
  let h := ℓ * tanc (θ / 8) / ONE / 6
  let m := step at_ chord (head + θ / 4)
  let e := step m chord (head + 3 * θ / 4)
  ([⟨at_, step at_ h head, step m (-h) (head + θ / 2), m⟩,
    ⟨m, step m h (head + θ / 2), step e (-h) (head + θ), e⟩], e, head + θ)

/-- **A tube's centreline as cubics**, two for each piece, in thousandths of a pixel. -/
def Tube.cubics (t : Tube) : List Cubic :=
  (t.pieces.foldl (fun (acc : List Cubic × (Int × Int) × Int) p =>
    let (cs, e, h) := p.draw acc.2.1 acc.2.2
    (acc.1 ++ cs, e, h)) ([], (t.x, t.y), t.head)).1

/-- A tube's length along its centreline. -/
def Tube.length (t : Tube) : Nat := t.pieces.foldl (· + ·.len) 0

/-- The first `s` of a piece: as long, turning in proportion. -/
def Piece.part (p : Piece) (s : Nat) : Piece :=
  let l := min s p.len
  ⟨l, if p.len = 0 then 0 else (p.turn * (l : Int)).tdiv (p.len : Int)⟩

/-- **Where a tube is at `s` along it**: the point and the heading. -/
def Tube.at (t : Tube) (s : Nat) : (Int × Int) × Int :=
  let r := t.pieces.foldl (fun (acc : Nat × (Int × Int) × Int) p =>
    let (left, at_, h) := acc
    if left = 0 then acc else
    let q := p.part left
    let (_, e, h') := q.draw at_ h
    (left - q.len, e, h')) (s, (t.x, t.y), t.head)
  r.2

/-- **The part of a tube from `s₀` to `s₁` along it**, with as many pieces as the tube: the
pieces outside it are of no length, so a part morphs into any other part of the tube. -/
def Tube.cut (t : Tube) (s₀ s₁ : Nat) (bore : Nat := t.bore) : Tube :=
  let (start, head) := t.at s₀
  let ps := (t.pieces.foldl (fun (acc : Nat × List Piece) p =>
    let (c, out) := acc
    let a := max c s₀
    let b := min (c + p.len) s₁
    let l := b - a
    let q : Piece := if l = 0 || p.len = 0 then Piece.zero else ⟨l, (p.turn * (l : Int)).tdiv (p.len : Int)⟩
    (c + p.len, out ++ [q])) (0, [])).2
  ⟨start.1, start.2, head, bore, ps⟩

/-- The heading where a tube ends. -/
def Tube.endHead (t : Tube) : Int := t.pieces.foldl (· + ·.turn) t.head

/-- **A tube drawn from its other end**: it starts where the tube ends, heading back, and runs
its pieces in the other order, each turning the other way. A tube is mixed from its start, so a
tube whose far end must stay put is given from that end and reversed. -/
def Tube.reverse (t : Tube) : Tube :=
  let e := (t.at t.length).1
  ⟨e.1, e.2, t.endHead + PI, t.bore, t.pieces.reverse.map fun p => ⟨p.len, -p.turn⟩⟩

/-- A straight tube from a point along a heading. -/
def straight (x y head : Int) (bore len : Nat) : Tube := ⟨x, y, head, bore, [⟨len, 0⟩]⟩

-- an elbow at the least radius (24 px) keeps the law, a tighter one does not
#guard decide (Piece.ok ⟨37700, 1570796⟩)
#guard !decide (Piece.ok ⟨37600, 1570796⟩)
#guard !decide (Piece.ok ⟨20000, 1570796⟩)
-- a quarter turn of radius 20 px ends 20 px across and 20 px down, heading down
#guard
  let (_, e, h) := (Piece.draw ⟨31416, 1570796⟩ (0, 0) 0)
  (e.1 - 20000).natAbs < 5 && (e.2 - 20000).natAbs < 5 && h == 1570796
-- a straight piece's handles stand on it, a sixth of its length from each end
#guard (Piece.draw ⟨60000, 0⟩ (0, 0) 0).1.head? == some ⟨(0, 0), (10000, 0), (20000, 0), (30000, 0)⟩
-- a part of a tube keeps its piece count, and a part of a straight tube starts where it is cut
#guard ((straight 0 0 0 8000 100000).cut 20000 50000).pieces == [⟨30000, 0⟩]
#guard ((straight 0 0 0 8000 100000).cut 20000 50000).x == 20000
-- a morph halfway between a straight run and a half turn keeps the law
#guard decide ((straight 0 0 0 8000 100000).mix ⟨0, 0, 0, 8000, [⟨100000, 3141593⟩]⟩ 500).ok
-- a tube reversed starts where it ended
#guard
  let t : Tube := ⟨0, 0, 0, 8000, [⟨31416, 1570796⟩, ⟨10000, 0⟩]⟩
  let r := t.reverse
  (r.x - 20000).natAbs < 5 && (r.y - 30000).natAbs < 5 && r.pieces == [⟨10000, 0⟩, ⟨31416, -1570796⟩]

end Tools.View.Tube
