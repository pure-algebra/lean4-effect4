import Effect4.Laws.Machine.Integers

/-!
# Machine.IntegerProfile — the profile's judgment of the one growing addition

The integers packet's slice 7 (`docs/research/2026-10-07-packet-integers.md`, appendix A.7;
decisions rows 108 and 321). The reference adds without a bound (`Profile.grow`). A target
refuses a sum outside the profile (DI-56). `intAddIn` is that refusal written as a judgment, with
the bound as an argument: with both arguments inside the profile it answers exactly when the
reference row answers inside it (`intAddIn_eq_some_iff`, the pointer of the claim
`profile-plus-exact`). It does not establish that the OCaml row or the TypeScript helper is this
judgment: each is a trusted row, read against its source and run by a control.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine

/-- A value inside the profile: an integer image within `±bound`. Every other value is inside. -/
def Within (bound : Nat) : Val → Bool
  | .nat n => decide (n ≤ bound)
  | .negInt n => decide (n + 1 ≤ bound)
  | _ => true

/-- The checked addition of magnitudes: the test comes before the sum, so its own lowering to a
63-bit integer never wraps. -/
def growIn (bound a b : Nat) : Option Nat :=
  if b ≤ bound ∧ a ≤ bound - b then some (a + b) else none

theorem growIn_eq_some_iff (bound a b n : Nat) :
    growIn bound a b = some n ↔ Profile.grow a b = n ∧ n ≤ bound := by
  unfold growIn Profile.grow
  constructor
  · intro h
    split at h
    · next hg => cases h; exact ⟨rfl, by omega⟩
    · exact nomatch h
  · rintro ⟨rfl, hle⟩
    rw [if_pos ⟨by omega, by omega⟩]

/-- The checked `plus`: the reference row with the checked growth. `none` is the refusal. -/
def intAddIn (bound : Nat) : Val → Val → Option Val
  | .nat a, .nat b => (growIn bound a b).map Val.nat
  | .nat a, .negInt b => some (if b < a then .nat (a - (b + 1)) else .negInt (b - a))
  | .negInt a, .nat b => some (if a < b then .nat (b - (a + 1)) else .negInt (a - b))
  | .negInt a, .negInt b => (growIn bound (a + 1) (b + 1)).map fun m => .negInt (m - 1)
  | _, _ => none

/-- **The checked row answers exactly when the reference row answers inside the profile.**
Premise: both arguments are inside it. -/
theorem intAddIn_eq_some_iff (bound : Nat) (x y v : Val)
    (hx : Within bound x = true) (hy : Within bound y = true) :
    intAddIn bound x y = some v ↔ intAdd x y = some v ∧ Within bound v = true := by
  cases x with
  | nat a =>
    cases y with
    | nat b =>
      show (growIn bound a b).map Val.nat = some v ↔
        some (Val.nat (Profile.grow a b)) = some v ∧ Within bound v = true
      constructor
      · intro h
        obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hg, hle⟩ := (growIn_eq_some_iff bound a b n).mp hn
        exact ⟨by rw [hg], decide_eq_true hle⟩
      · rintro ⟨h, hw⟩
        cases h
        rw [(growIn_eq_some_iff bound a b _).mpr ⟨rfl, of_decide_eq_true hw⟩]
        rfl
    | negInt b =>
      have ha : a ≤ bound := of_decide_eq_true hx
      have hb : b + 1 ≤ bound := of_decide_eq_true hy
      show some _ = some v ↔ some _ = some v ∧ Within bound v = true
      constructor
      · intro h
        refine ⟨h, ?_⟩
        cases h
        split
        · exact decide_eq_true (by omega)
        · exact decide_eq_true (by omega)
      · exact fun h => h.1
    | _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩
  | negInt a =>
    cases y with
    | nat b =>
      have ha : a + 1 ≤ bound := of_decide_eq_true hx
      have hb : b ≤ bound := of_decide_eq_true hy
      show some _ = some v ↔ some _ = some v ∧ Within bound v = true
      constructor
      · intro h
        refine ⟨h, ?_⟩
        cases h
        split
        · exact decide_eq_true (by omega)
        · exact decide_eq_true (by omega)
      · exact fun h => h.1
    | negInt b =>
      show (growIn bound (a + 1) (b + 1)).map (fun m => Store.Val.negInt (m - 1)) = some v ↔
        some (Store.Val.negInt (Profile.grow (a + 1) (b + 1) - 1)) = some v ∧ Within bound v = true
      constructor
      · intro h
        obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hg, hle⟩ := (growIn_eq_some_iff bound (a + 1) (b + 1) n).mp hn
        refine ⟨by rw [hg], decide_eq_true ?_⟩
        unfold Profile.grow at hg
        omega
      · rintro ⟨h, hw⟩
        cases h
        have hle : Profile.grow (a + 1) (b + 1) ≤ bound := by
          have := of_decide_eq_true hw
          unfold Profile.grow at this ⊢
          omega
        rw [(growIn_eq_some_iff bound (a + 1) (b + 1) _).mpr ⟨rfl, hle⟩]
        rfl
    | _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩
  | _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩

end Effect4.Program
