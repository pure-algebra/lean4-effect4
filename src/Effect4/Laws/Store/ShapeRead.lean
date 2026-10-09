import Effect4.Store.Domain.ShapeRead
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Store.ShapeRead — whatever reads from JSON is that value's print

`Store/Domain/ShapeRead.lean` reads a value tree from its JSON print under a shape. Its law is
exactness: whatever reads is the canonical print of the value it reads (`readIn_exact`). So a
canonical carrier read from JSON is the carrier whose print that JSON is (`Canonical.ofJson_exact`).

## Placement

Concept `exact-codecs`; property: a read paired with a write is exact when whatever reads is the
write of what it reads. Requirement R14 (program as data): the schema form an agent writes.

- **`json-read-exact`** (claim, role compatibility; pointer `Canonical.ofJson_exact`). Reach:
  every shape document and every JSON value, at every budget of option layers. Not established:
  the round trip, which holds only where every natural is at most 2^53 and no option holds a
  shape that prints `null`; the bytes, which the canonical codec owns (`Canonical.decode_exact`).
  Consumer: the session tool, whose requests may carry a program as JSON.
- **`natOfBinary64_finite`** (a step of `json-read-exact`; consumer `Tools.JsonBridge.ofLeanJson_num`,
  so the session tool and the MCP face). Reach: every `UInt64`. What reads is a non-negative
  finite binary64 datum, the binary64 of the natural read (`natOfBinary64_exact`), and that
  natural is below 2^1024: the read gives no natural for a negative or non-finite datum, which a
  host reads as another number. Not established: that every natural binary64 holds exactly reads
  back (the retraction), which the claim leaves out with the round trip; anything of how a host
  parses the datum's text.
-/

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (Json Float64)

/-- A natural read from a binary64 datum spells that datum. A step of `json-read-exact`. Its
consumer is `readIn_exact`. -/
@[semantics "exact-codecs" (requirement := R14)]
theorem natOfBinary64_exact {bits : UInt64} {n : Nat} (h : natOfBinary64 bits = some n) :
    Effect4.Arch.binary64OfNat n = bits := by
  unfold natOfBinary64 at h
  split at h
  · rename_i heq
    cases h
    exact heq.2
  · cases h

/-- The natural a non-negative finite datum stands for is below 2^1024: the biased exponent is at
most 2046 and the significand below 2^53. A step of `natOfBinary64_finite`. -/
theorem natCandidate_lt {bits : UInt64} (h : bits.toNat < Effect4.Arch.binary64Infinity) :
    natCandidate bits < 2 ^ 1024 := by
  have hinf : Effect4.Arch.binary64Infinity = 2047 * 2 ^ 52 := rfl
  have hpos : 0 < (2 : Nat) ^ 52 := Nat.two_pow_pos 52
  have he : bits.toNat / 2 ^ 52 ≤ 2046 := by
    rw [hinf] at h
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpos).mpr h)
  have hsig : bits.toNat % 2 ^ 52 + 2 ^ 52 < 2 ^ 53 := by
    have hm := Nat.mod_lt bits.toNat hpos
    rw [Nat.pow_succ]
    omega
  unfold natCandidate
  dsimp only
  split
  · exact Nat.two_pow_pos 1024
  · split
    · have hk : 53 + (bits.toNat / 2 ^ 52 - (1023 + 52)) ≤ 1024 := by omega
      calc (bits.toNat % 2 ^ 52 + 2 ^ 52) * 2 ^ (bits.toNat / 2 ^ 52 - (1023 + 52))
          < 2 ^ 53 * 2 ^ (bits.toNat / 2 ^ 52 - (1023 + 52)) :=
            Nat.mul_lt_mul_of_pos_right hsig (Nat.two_pow_pos _)
        _ = 2 ^ (53 + (bits.toNat / 2 ^ 52 - (1023 + 52))) := (Nat.pow_add 2 53 _).symm
        _ ≤ 2 ^ 1024 := Nat.pow_le_pow_right (by decide) hk
    · calc (bits.toNat % 2 ^ 52 + 2 ^ 52) / 2 ^ ((1023 + 52) - bits.toNat / 2 ^ 52)
          ≤ bits.toNat % 2 ^ 52 + 2 ^ 52 := Nat.div_le_self _ _
        _ < 2 ^ 53 := hsig
        _ ≤ 2 ^ 1024 := Nat.pow_le_pow_right (by decide) (by decide)

/-- **A natural reads only from a non-negative finite binary64**, and it is below 2^1024. So the
datum the read accepts is a number a binary64 host reads as that natural, never `+Infinity` or a
negative number whose bits the write happens to give back (2^2048 and `-1.0`). A step of
`json-read-exact`. Its consumer is `Tools.JsonBridge.ofLeanJson_num`. -/
@[semantics "exact-codecs" (requirement := R14)]
theorem natOfBinary64_finite {bits : UInt64} {n : Nat} (h : natOfBinary64 bits = some n) :
    bits.toNat < Effect4.Arch.binary64Infinity ∧ n < 2 ^ 1024 := by
  unfold natOfBinary64 at h
  split at h
  · rename_i heq
    cases h
    exact ⟨heq.1, natCandidate_lt heq.1⟩
  · cases h

/-- Bytes read from hex are spelled by that hex. A step of `json-read-exact`. Its consumer is
`readIn_exact`. -/
@[semantics "exact-codecs" (requirement := R14)]
theorem canonicalHex?_exact {h : String} {d : Bytes} (hd : canonicalHex? h = some d) :
    hexString d = h := by
  unfold canonicalHex? at hd
  obtain ⟨d', -, hd'⟩ := Option.bind_eq_some_iff.mp hd
  split at hd'
  · rename_i heq
    cases hd'
    exact heq
  · cases hd'

/-- A tag read from a case name prints as that name. A step of `json-read-exact`. Its consumer
is `readIn_exact`. -/
@[semantics "exact-codecs" (requirement := R14)]
theorem tagOfName_exact {name : String} {cases : List (String × Nat × List (String × Shape))}
    {tag : Nat} {fields : List (String × Shape)} (h : tagOfName name cases = some (tag, fields)) :
    caseAt tag cases = some (name, fields) := by
  unfold tagOfName at h
  obtain ⟨⟨n0, t0, f0⟩, -, h2⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h2
  split at h2
  · rename_i name' fields' hc
    split at h2
    · rename_i hn
      cases h2
      rw [hc, hn]
    · cases h2
  · cases h2

mutual
/-- **Whatever reads is the value's print**, under the same shape, at every budget. The pointer's
step of `json-read-exact`. Its consumer is `ShapeDoc.read_exact`. -/
@[semantics "exact-codecs" (requirement := R14)]
theorem readIn_exact {defs : List (String × Shape)} :
    ∀ {n : Nat} {s : Shape} {j : Json} {v : Val}, readIn defs n s j = some v → printIn defs s v = j
  | 0, _, _, _, h => by cases h
  | n + 1, s, j, v, h => by
    unfold readIn at h
    split at h
    next hs =>
      cases h
      rfl
    next hs =>
      cases h
      rfl
    next item j' hs _ =>
      obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
      have hp := readIn_exact ha
      simp only [printIn, hs]
      exact hp
    next b hs =>
      cases h
      rfl
    next x hs =>
      obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [printIn, Effect4.Arch.Json.ofNat, natOfBinary64_exact hm]
    next t hs =>
      cases h
      rfl
    next hx hs =>
      obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [printIn, canonicalHex?_exact hd]
    next hx hs =>
      obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [printIn, canonicalHex?_exact hd]
    next item js hs =>
      obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h
      have hp := readList_exact hxs
      simp only [printIn, hs, hp]
    next f g a b hs =>
      obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h2
      have hpx := readIn_exact hx
      have hpy := readIn_exact hy
      simp only [printIn, hs, hpx, hpy]
    next name fields entries hs =>
      obtain ⟨args, hargs, rfl⟩ := Option.map_eq_some_iff.mp h
      have hp := readFields_exact hargs
      simp only [printIn, hs, hp]
    next name cases hname hs =>
      split at h
      next hall =>
        obtain ⟨⟨tag, fields⟩, htag, h2⟩ := Option.bind_eq_some_iff.mp h
        dsimp only at h2
        by_cases hemp : fields.isEmpty = true
        · rw [if_pos hemp] at h2
          cases h2
          simp only [printIn, hs, tagOfName_exact htag, hall, ↓reduceIte]
        · rw [if_neg hemp] at h2
          cases h2
      next => cases h
    next name cases entries hs =>
      split at h
      next => cases h
      next hall =>
        obtain ⟨⟨tag, fields⟩, htag, h2⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨args, hargs, rfl⟩ := Option.map_eq_some_iff.mp h2
        have hp := readFields_exact hargs
        simp only [printIn, hs, tagOfName_exact htag, hall, hp, Bool.false_eq_true, ↓reduceIte]
    next k hx hs =>
      obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [printIn, hs, canonicalHex?_exact hd]
    next kn hx hs =>
      obtain ⟨k, hk, h2⟩ := Option.bind_eq_some_iff.mp h
      split at h2
      next hkind =>
        obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h2
        simp only [printIn, hs, hkind, canonicalHex?_exact hd]
      next => cases h2
    next => cases h

/-- The elements read are printed as the list read. A step of `readIn_exact`. -/
@[semantics "exact-codecs" (requirement := R14)]
theorem readList_exact {defs : List (String × Shape)} :
    ∀ {n : Nat} {item : Shape} {js : List Json} {xs : List Val},
      readList defs n item js = some xs → printList defs item xs = js
  | 0, _, _, _, h => by cases h
  | _ + 1, _, [], _, h => by
    unfold readList at h
    cases h
    rfl
  | n + 1, item, j :: js, xs, h => by
    unfold readList at h
    obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs', hxs, rfl⟩ := Option.map_eq_some_iff.mp h2
    have hp := readIn_exact hx
    have hps := readList_exact hxs
    simp only [printList, hp, hps]

/-- The fields read are printed as the entries read. A step of `readIn_exact`. -/
@[semantics "exact-codecs" (requirement := R14)]
theorem readFields_exact {defs : List (String × Shape)} :
    ∀ {n : Nat} {fields : List (String × Shape)} {entries : List (String × Json)}
      {args : List Val}, readFields defs n fields entries = some args →
      printFields defs fields args = entries
  | 0, _, _, _, h => by cases h
  | _ + 1, [], [], _, h => by
    unfold readFields at h
    cases h
    rfl
  | n + 1, (k, s) :: fields, (k', j) :: entries, args, h => by
    unfold readFields at h
    split at h
    next hk =>
      obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h2
      have hp := readIn_exact hx
      have hps := readFields_exact hxs
      simp only [printFields, hp, hps, hk]
    next => cases h
  | _ + 1, [], _ :: _, _, h => by
    unfold readFields at h
    cases h
  | _ + 1, _ :: _, [], _, h => by
    unfold readFields at h
    cases h
end


/-- **A document's reading is exact.** A step of `json-read-exact`. Its consumer is
`Canonical.ofJson_exact`. -/
@[semantics "exact-codecs" (requirement := R14)]
theorem ShapeDoc.read_exact {doc : ShapeDoc} {j : Json} {v : Val} (h : doc.read j = some v) :
    doc.print v = j :=
  readIn_exact h

/-- **A carrier read from JSON is the carrier whose canonical print that JSON is.** The pointer
of `json-read-exact`. -/
@[semantics "exact-codecs" (requirement := R14)]
theorem Canonical.ofJson_exact {α : Type} [Canonical α] {j : Json} {a : α}
    (h : Canonical.ofJson j = some a) : Canonical.print a = j := by
  unfold Canonical.ofJson at h
  obtain ⟨v, hv, ha⟩ := Option.bind_eq_some_iff.mp h
  have hva := Canonical.ofVal_exact ha
  subst hva
  exact ShapeDoc.read_exact hv

end Effect4.Store
