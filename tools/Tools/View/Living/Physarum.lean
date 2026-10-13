/-!
# Tools.View.Living.Physarum — channels that thicken with use and wither when idle

The slime mould *Physarum polycephalum* builds its transport network by feedback: a tube that
carries much protoplasm widens, and a tube that carries little narrows and disappears. Tero et al.
model it ("Rules for biologically inspired adaptive network design", *Science* 327:439–442, 2010,
p. 441): the flux through a tube is `Q = D (p_i − p_j) / L` (their equation 1, after
Hagen–Poiseuille), inflow equals outflow at every inner node, and each tube's conductivity
adapts as `dD/dt = f(|Q|) − D`, with the sigmoid `f(|Q|) = |Q|^γ / (1 + |Q|^γ)`.

Here the flux needs no pressure: a step of the run says what moved (the keyed join of the cell
before and after). So a channel's conductivity is a fold over the run's fluxes, one beat per
command, in whole thousandths:

* `gain q`: the sigmoid at `γ = 2`, `q² / (1 + q²)`, with `q` in thousandths of a unit;
* `adapt rate d q`: one explicit step of `dD/dt = f(|Q|) − D` of size `rate`, so the
  conductivity moves `rate` thousandths of the way from where it is toward the gain;
* `conductivity rate fluxes`: the fold from zero.

The laws: the gain stays below one; a conductivity in `[0, 1]` stays there; an idle channel
loses the share `rate` of its conductivity at each beat. The picture reads a channel's width from
its conductivity, so the width is the channel's history of use, saturating as the mould's does.
-/

namespace Tools.View.Living.Physarum

/-- One unit, in thousandths. -/
def ONE : Nat := 1000

/-- **The sigmoid of the adaptation** at `γ = 2`: `q² / (1 + q²)` in thousandths, `q` being a
flux in thousandths of a unit. One unit gives a half; four units nearly all. -/
def gain (q : Nat) : Nat := q * q * ONE / (q * q + ONE * ONE)

/-- **One beat of the adaptation**: the conductivity `d` moves the share `rate` (in thousandths)
of the way toward the gain of the flux `q`. -/
def adapt (rate d q : Nat) : Nat := (d * (ONE - rate) + gain q * rate) / ONE

/-- **A channel's conductivity after a run of fluxes**, from zero, one beat each. -/
def conductivity (rate : Nat) (fluxes : List Nat) : Nat := fluxes.foldl (adapt rate) 0

/-- The conductivity after each beat of a run, the first after the first flux. -/
def history (rate : Nat) (fluxes : List Nat) : List Nat :=
  (fluxes.foldl (fun (d, out) q => let d' := adapt rate d q; (d', out ++ [d'])) (0, ([] : List Nat))).2

/-- The gain stays below one. -/
theorem gain_lt (q : Nat) : gain q < ONE := by
  unfold gain
  apply Nat.div_lt_of_lt_mul
  have h : q * q < q * q + ONE * ONE := Nat.lt_add_of_pos_right (by decide)
  calc q * q * ONE < (q * q + ONE * ONE) * ONE := Nat.mul_lt_mul_of_pos_right h (by decide)
    _ = (q * q + ONE * ONE) * ONE := rfl

/-- **A conductivity in `[0, 1]` stays there**, at every rate up to one. -/
theorem adapt_le (rate d q : Nat) (hr : rate ≤ ONE) (hd : d ≤ ONE) : adapt rate d q ≤ ONE := by
  unfold adapt
  apply Nat.div_le_of_le_mul
  have h1 : d * (ONE - rate) ≤ ONE * (ONE - rate) := Nat.mul_le_mul_right _ hd
  have h2 : gain q * rate ≤ ONE * rate := Nat.mul_le_mul_right _ (Nat.le_of_lt (gain_lt q))
  have h3 : ONE * (ONE - rate) + ONE * rate = ONE * ONE := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hr]
  calc d * (ONE - rate) + gain q * rate ≤ ONE * (ONE - rate) + ONE * rate := Nat.add_le_add h1 h2
    _ = ONE * ONE := h3

/-- **An idle channel withers**: with no flux, it keeps the share `1 − rate` of its conductivity. -/
theorem adapt_idle (rate d : Nat) : adapt rate d 0 = d * (ONE - rate) / ONE := by
  simp only [adapt, gain, Nat.mul_zero, Nat.zero_div, Nat.zero_mul, Nat.add_zero]

/-- **A run's conductivity stays in `[0, 1]`.** -/
theorem conductivity_le (rate : Nat) (hr : rate ≤ ONE) (fluxes : List Nat) :
    conductivity rate fluxes ≤ ONE := by
  unfold conductivity
  suffices ∀ d, d ≤ ONE → fluxes.foldl (adapt rate) d ≤ ONE from this 0 (Nat.zero_le _)
  induction fluxes with
  | nil => intro d hd; exact hd
  | cons q rest ih => intro d hd; exact ih _ (adapt_le rate d q hr hd)

end Tools.View.Living.Physarum
