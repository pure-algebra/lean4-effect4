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
    exact heq
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
