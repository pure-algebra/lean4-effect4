import Effect4.Laws.Machine.Integers
import Effect4.Program.Profile

/-!
# Machine.IntegerProfile — the profile's judgment of the one growing addition

The integers packet's slice 7 (`docs/research/2026-10-07-packet-integers.md`, appendix A.7;
decisions rows 108 and 321). The reference adds without a bound (`Profile.grow`). A target
refuses a sum outside the profile (DI-56). `intAddIn` is that refusal written as a judgment of a
profile, whose bound has one owner (`ProfileData.natBound`, read through `admitsNat`): with both
arguments inside the profile it answers exactly when the reference row answers inside it
(`intAddIn_eq_some_iff`, the pointer of the claim `profile-plus-exact`). A profile with no bound,
the native one's, refuses nothing. It does not establish that the OCaml row or the TypeScript
helper is this judgment: each is a trusted row, read against its source and run by a control.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine

/-- A value inside the profile: an integer image whose magnitude the profile admits
(`ProfileData.admitsNat`, the leaf of profile support). Every other value is inside. -/
def Within (profile : ProfileData) : Val → Bool
  | .nat n => profile.admitsNat n
  | .negInt n => profile.admitsNat (n + 1)
  | _ => true

/-- The checked addition of magnitudes: the reference sum, where the profile admits it. -/
def growIn (profile : ProfileData) (a b : Nat) : Option Nat :=
  if profile.admitsNat (Profile.grow a b) then some (Profile.grow a b) else none

theorem growIn_eq_some_iff (profile : ProfileData) (a b n : Nat) :
    growIn profile a b = some n ↔ Profile.grow a b = n ∧ profile.admitsNat n = true := by
  unfold growIn
  constructor
  · intro h
    split at h
    · next hg => cases h; exact ⟨rfl, hg⟩
    · exact nomatch h
  · rintro ⟨rfl, hle⟩
    rw [if_pos hle]

/-- The checked `plus`: the reference row with the checked growth. `none` is the refusal. -/
def intAddIn (profile : ProfileData) : Val → Val → Option Val
  | .nat a, .nat b => (growIn profile a b).map Val.nat
  | .nat a, .negInt b => some (if b < a then .nat (a - (b + 1)) else .negInt (b - a))
  | .negInt a, .nat b => some (if a < b then .nat (b - (a + 1)) else .negInt (a - b))
  | .negInt a, .negInt b => (growIn profile (a + 1) (b + 1)).map fun m => .negInt (m - 1)
  | _, _ => none

/-- **The checked row answers exactly when the reference row answers inside the profile.**
Premise: both arguments are inside it. -/
theorem intAddIn_eq_some_iff (profile : ProfileData) (x y v : Val)
    (hx : Within profile x = true) (hy : Within profile y = true) :
    intAddIn profile x y = some v ↔ intAdd x y = some v ∧ Within profile v = true := by
  cases x with
  | nat a =>
    cases y with
    | nat b =>
      show (growIn profile a b).map Val.nat = some v ↔
        some (Val.nat (Profile.grow a b)) = some v ∧ Within profile v = true
      constructor
      · intro h
        obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hg, hle⟩ := (growIn_eq_some_iff profile a b n).mp hn
        exact ⟨by rw [hg], hle⟩
      · rintro ⟨h, hw⟩
        cases h
        rw [(growIn_eq_some_iff profile a b _).mpr ⟨rfl, hw⟩]
        rfl
    | negInt b =>
      have ha : profile.admitsNat a = true := hx
      have hb : profile.admitsNat (b + 1) = true := hy
      show some _ = some v ↔ some _ = some v ∧ Within profile v = true
      constructor
      · intro h
        refine ⟨h, ?_⟩
        cases h
        split
        · exact profile.admitsNat_of_le ha (by omega)
        · exact profile.admitsNat_of_le hb (by omega)
      · exact fun h => h.1
    | _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩
  | negInt a =>
    cases y with
    | nat b =>
      have ha : profile.admitsNat (a + 1) = true := hx
      have hb : profile.admitsNat b = true := hy
      show some _ = some v ↔ some _ = some v ∧ Within profile v = true
      constructor
      · intro h
        refine ⟨h, ?_⟩
        cases h
        split
        · exact profile.admitsNat_of_le hb (by omega)
        · exact profile.admitsNat_of_le ha (by omega)
      · exact fun h => h.1
    | negInt b =>
      show (growIn profile (a + 1) (b + 1)).map (fun m => Store.Val.negInt (m - 1)) = some v ↔
        some (Store.Val.negInt (Profile.grow (a + 1) (b + 1) - 1)) = some v ∧
          Within profile v = true
      -- the sum of two magnitudes is at least 2, so taking one off and putting it back is the sum
      have back : Profile.grow (a + 1) (b + 1) - 1 + 1 = Profile.grow (a + 1) (b + 1) := by
        unfold Profile.grow
        omega
      constructor
      · intro h
        obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hg, hle⟩ := (growIn_eq_some_iff profile (a + 1) (b + 1) n).mp hn
        refine ⟨by rw [hg], ?_⟩
        show profile.admitsNat (n - 1 + 1) = true
        rw [← hg, back, hg]
        exact hle
      · rintro ⟨h, hw⟩
        cases h
        have hle : profile.admitsNat (Profile.grow (a + 1) (b + 1)) = true := by
          have within : profile.admitsNat (Profile.grow (a + 1) (b + 1) - 1 + 1) = true := hw
          rw [back] at within
          exact within
        rw [(growIn_eq_some_iff profile (a + 1) (b + 1) _).mpr ⟨rfl, hle⟩]
        rfl
    | _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩
  | _ => exact ⟨fun h => (nomatch h), fun h => (nomatch h.1)⟩

/-- Checked multiplication: the reference product, where the profile admits it.
Consumer: the profile-mul-exact compatibility claim and its actual atom reader. -/
def scaleIn (profile : ProfileData) (a b : Nat) : Option Nat :=
  if profile.admitsNat (Profile.scale a b) then some (Profile.scale a b) else none

/-- The checked multiplication answers exactly for the reference product inside the profile.
This is a proof-side judgment; target rows still require their external controls. -/
theorem scaleIn_eq_some_iff (profile : ProfileData) (a b n : Nat) :
    scaleIn profile a b = some n ↔ a * b = n ∧ profile.admitsNat n = true := by
  unfold scaleIn Profile.scale
  constructor
  · intro h
    split at h
    · next fits => cases h; exact ⟨rfl, fits⟩
    · exact nomatch h
  · rintro ⟨rfl, fits⟩
    rw [if_pos fits]

/-- The represented natural multiplication uses exactly the checked product judgment.
Claim: profile-mul-exact, translation-simulation R8. Target execution remains a separate control. -/
theorem mulIn_eq_some_iff (profile : ProfileData) (a b n : Nat) :
    scaleIn profile a b = some n ↔
      NativeAtom.eval .mul [.nat a, .nat b] = some (.nat n) ∧ Within profile (.nat n) = true := by
  change scaleIn profile a b = some n ↔
    some (Val.nat (a * b)) = some (Val.nat n) ∧ profile.admitsNat n = true
  simp only [Option.some.injEq, Store.Val.nat.injEq]
  exact scaleIn_eq_some_iff profile a b n

end Effect4.Program
