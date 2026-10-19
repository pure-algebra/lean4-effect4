import Effect4.Store.Domain.ShapeRead
import Effect4.Store.Domain.ShapeJson
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Store.ShapeRead — whatever reads from JSON is that value's print

`Store/Domain/ShapeRead.lean` reads a value tree from its cases print (`ShapeDoc.print`) under a
shape. Its law is exactness: whatever reads is the cases print of the value it reads
(`readIn_exact`). So a canonical carrier read from JSON is the carrier whose cases print that JSON
is (`Canonical.ofJson_exact`). The public print, each list an array, is `Canonical.print`
(`Store/Domain/ShapeJson.lean`); the cases print is the normal form each law below names.

`Store/Domain/ShapeJson.lean` reads the JSON an agent writes, from the profile's tree, and refuses
at a place. Its laws are exactness modulo the normaliser `ShapeDoc.order` (`readAt_exact`, by one
induction beside the normaliser), the validity of every refusal's site (`readAt_site`), and the
agreement of the profile's tree with its binary64 image within the profile
(`ofBinary64_toBinary64`, over `natOfBinary64_binary64OfNat`).

No reader here has a budget. Each recurses on the JSON value's size, then on the definitions not
yet unfolded since the last node, then on the shape's size (`optionLayer?_lt`). So each law below
holds of the reader's whole answer, and no refusal stands for a spent budget.

## Placement

Concept `exact-codecs`; property: a read paired with a write is exact when whatever reads is the
write of what it reads. Requirement R8 (runs and faces as named connections,
`docs/core/system-map.md` §8): the JSON face of a carrier reads inside its profile as the
reference's value, and refuses outside it at a place. R14 is the sketch checker's, which reads
no JSON.

- **`json-read-exact`** (claim, role compatibility; pointer `Canonical.ofJson_exact`). Reach:
  every shape document and every JSON value. Not established:
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
- **`json-read-located`** (proposed claim, role compatibility; its pointer is
  `CodecProfile.profileLocated_exact`, `Laws/Tool/CodecProfile.lean`). The steps here:
  `readAt_exact` and `ShapeDoc.readLocated_exact` (exactness modulo `ShapeDoc.order`, for every
  tree and every agreeing binary64 tree); `Canonical.ofJsonAnyOrder_exact`
  (re-proved through them: the any-order reader is now the located reader's projection);
  `readAt_site` and `ShapeDoc.readLocated_site` (every refusal names a value of the input, or a
  field missing from an object of it; Codex's `readLocated_site` with the amended relation);
  `ShapeDoc.readLocated_erases` (the projection, by definition). Reach: every shape document
  and every profile tree. Not established: the round trip; that the old two-pass
  reader (`ShapeDoc.order`, then `readIn`) accepts exactly what the located reader accepts, which
  the batteries check on finite inputs; that the reported reason is the input's only fault.
  Consumers: the tool's JSON profile and the native shell.
- **`natOfBinary64_binary64OfNat`** (a step of `json-read-located`; consumer
  `ofBinary64_toBinary64`, then `CodecProfile.read_toBinary64`). Reach: every natural below
  2^53. It is the retraction `Data/JsonNumber.lean` owed, on the profile's domain; the naturals
  from 2^53 up with at most 53 significant bits stay owed.
-/

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (Json Float64 NatJson JsonStep JsonSite Located)

/-- A natural read from a binary64 datum spells that datum. A step of `json-read-exact`. Its
consumer is `readIn_exact`. -/
@[semantics "exact-codecs" (requirement := R8)]
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
@[semantics "exact-codecs" (requirement := R8)]
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
@[semantics "exact-codecs" (requirement := R8)]
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
@[semantics "exact-codecs" (requirement := R8)]
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

/-- **A layer reads the item of the shape's head**: where `optionLayer?` answers, the head is the
option of the item it answers. A step of `readIn_exact`, `readAt_exact` and `orderIn_option`. -/
theorem optionLayer?_head {defs : List (String × Shape)} {s item : Shape}
    {seen seen' : List String} (h : optionLayer? defs s seen = some (item, seen')) :
    headShape defs s = .option item := by
  unfold optionLayer? at h
  split at h
  · rename_i item' hs
    split at h
    · split at h
      · cases h
      · cases h
        exact hs
    · cases h
      exact hs
  · cases h

mutual
/-- **Whatever reads is the value's print**, under the same shape. The pointer's step of
`json-read-exact`. Its consumer is `ShapeDoc.read_exact`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem readIn_exact {defs : List (String × Shape)} :
    ∀ {seen : List String} {s : Shape} {j : Json} {v : Val},
      readIn defs seen s j = some v → printIn defs s v = j
  | seen, s, j, v, h => by
    unfold readIn at h
    split at h
    next hs =>
      cases h
      rfl
    next hs =>
      cases h
      rfl
    next j' _ hs _ =>
      split at h
      next item seen' hl =>
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp h
        have hp := readIn_exact ha
        simp only [printIn, optionLayer?_head hl]
        exact hp
      next => cases h
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
termination_by seen s j => (sizeOf j, unseenDefs defs seen, sizeOf s)
decreasing_by
  all_goals subst_vars
  · exact Prod.Lex.right _ (optionLayer?_lt ‹_›)
  all_goals
    apply Prod.Lex.left
    simp only [Json.arr.sizeOf_spec, Json.obj.sizeOf_spec, List.cons.sizeOf_spec,
      Prod.mk.sizeOf_spec]
    omega

/-- The elements read are printed as the list read. A step of `readIn_exact`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem readList_exact {defs : List (String × Shape)} :
    ∀ {item : Shape} {js : List Json} {xs : List Val},
      readList defs item js = some xs → printList defs item xs = js
  | _, [], _, h => by
    unfold readList at h
    cases h
    rfl
  | item, j :: js, xs, h => by
    unfold readList at h
    obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs', hxs, rfl⟩ := Option.map_eq_some_iff.mp h2
    have hp := readIn_exact hx
    have hps := readList_exact hxs
    simp only [printList, hp, hps]
termination_by _ js => (sizeOf js, 0, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec]
    omega

/-- The fields read are printed as the entries read. A step of `readIn_exact`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem readFields_exact {defs : List (String × Shape)} :
    ∀ {fields : List (String × Shape)} {entries : List (String × Json)} {args : List Val},
      readFields defs fields entries = some args → printFields defs fields args = entries
  | [], [], _, h => by
    unfold readFields at h
    cases h
    rfl
  | (k, s) :: fields, (k', j) :: entries, args, h => by
    unfold readFields at h
    split at h
    next hk =>
      obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h2
      have hp := readIn_exact hx
      have hps := readFields_exact hxs
      simp only [printFields, hp, hps, hk]
    next => cases h
  | [], _ :: _, _, h => by
    unfold readFields at h
    cases h
  | _ :: _, [], _, h => by
    unfold readFields at h
    cases h
termination_by _ entries => (sizeOf entries, 0, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    omega
end


/-- **A document's reading is exact.** A step of `json-read-exact`. Its consumer is
`Canonical.ofJson_exact`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem ShapeDoc.read_exact {doc : ShapeDoc} {j : Json} {v : Val} (h : doc.read j = some v) :
    doc.print v = j :=
  readIn_exact h

/-- **A carrier read from JSON is the carrier whose cases print that JSON is.** The pointer
of `json-read-exact`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem Canonical.ofJson_exact {α : Type} [Canonical α] {j : Json} {a : α}
    (h : Canonical.ofJson j = some a) : (Canonical.shape α).print (Canonical.toVal a) = j := by
  unfold Canonical.ofJson at h
  obtain ⟨v, hv, ha⟩ := Option.bind_eq_some_iff.mp h
  have hva := Canonical.ofVal_exact ha
  subst hva
  exact ShapeDoc.read_exact hv

/-! ## The binary64 spelling of a natural below 2^53

A natural below 2^53 has at most 53 significant bits, so its binary64 datum (`binary64OfNat`) is
exact and the reader takes the natural back (`natOfBinary64_binary64OfNat`). This is the theorem
`Data/JsonNumber.lean` owed for the profile's domain, and the step that lets the profile's tree
and the binary64 tree read alike (`ofBinary64_toBinary64`). -/

/-- The highest-bit loop, given fuel enough, adds the natural's `log2`. A step of
`natOfBinary64_binary64OfNat`, through `highestBit_eq`. -/
theorem highestBit_go {fuel m acc : Nat} (h : m ≤ fuel) :
    Effect4.Arch.highestBit.go fuel m acc = acc + m.log2 := by
  induction fuel generalizing m acc with
  | zero =>
    have hm : m = 0 := by omega
    subst hm
    rw [Nat.log2_def]
    rfl
  | succ fuel ih =>
    unfold Effect4.Arch.highestBit.go
    split
    · rename_i hm
      rw [Nat.log2_def, if_neg (by omega)]
      rfl
    · rename_i hm
      rw [ih (by omega), Nat.log2_def m, if_pos (by omega)]
      omega

/-- `Arch.highestBit` is `Nat.log2`. A step of `natOfBinary64_binary64OfNat`. -/
theorem highestBit_eq (n : Nat) : Effect4.Arch.highestBit n = n.log2 := by
  unfold Effect4.Arch.highestBit
  rw [highestBit_go (Nat.le_refl n), Nat.zero_add]

/-- **A natural below 2^53 reads back from its binary64 datum**: the retraction that
`Data/JsonNumber.lean` owed, on the profile's domain. A step of `json-read-located`. Its consumer
is `ofBinary64_toBinary64`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem natOfBinary64_binary64OfNat {n : Nat} (h : n < 2 ^ 53) :
    natOfBinary64 (Effect4.Arch.binary64OfNat n) = some n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    decide
  · have hn0 : n ≠ 0 := by omega
    have hle : 2 ^ n.log2 ≤ n := Nat.log2_self_le hn0
    have hlt : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
    have he : n.log2 ≤ 52 := by
      have := (Nat.log2_lt hn0).2 h
      omega
    have hk : 2 ^ n.log2 * 2 ^ (52 - n.log2) = 2 ^ 52 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hk1 : 2 ^ (n.log2 + 1) * 2 ^ (52 - n.log2) = 2 ^ 53 := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hs1 : 2 ^ 52 ≤ n * 2 ^ (52 - n.log2) := hk ▸ Nat.mul_le_mul_right _ hle
    have hs2 : n * 2 ^ (52 - n.log2) < 2 ^ 53 :=
      hk1 ▸ Nat.mul_lt_mul_of_pos_right hlt (Nat.two_pow_pos _)
    have hbits : (Effect4.Arch.binary64OfNat n).toNat =
        2 ^ 52 * (1023 + n.log2) + (n * 2 ^ (52 - n.log2) - 2 ^ 52) := by
      unfold Effect4.Arch.binary64OfNat
      rw [if_neg hn0]
      simp only [highestBit_eq, if_pos he, Nat.shiftLeft_eq, Nat.one_mul, UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega)]
      rw [Nat.mul_comm]
    have hsig : n * 2 ^ (52 - n.log2) - 2 ^ 52 < 2 ^ 52 := by omega
    have hdiv : (2 ^ 52 * (1023 + n.log2) + (n * 2 ^ (52 - n.log2) - 2 ^ 52)) / 2 ^ 52 =
        1023 + n.log2 := by
      rw [Nat.mul_add_div (Nat.two_pow_pos 52), Nat.div_eq_of_lt hsig, Nat.add_zero]
    have hmod : (2 ^ 52 * (1023 + n.log2) + (n * 2 ^ (52 - n.log2) - 2 ^ 52)) % 2 ^ 52 =
        n * 2 ^ (52 - n.log2) - 2 ^ 52 := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hsig]
    have hcand : natCandidate (Effect4.Arch.binary64OfNat n) = n := by
      unfold natCandidate
      simp only [hbits, hdiv, hmod]
      rw [if_neg (by omega), Nat.sub_add_cancel hs1]
      split
      · rename_i he52
        have : n.log2 = 52 := by omega
        simp only [this, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
      · rw [show 1023 + 52 - (1023 + n.log2) = 52 - n.log2 by omega]
        exact Nat.mul_div_cancel n (Nat.two_pow_pos _)
    unfold natOfBinary64
    rw [hcand, if_pos ⟨by rw [hbits]; unfold Effect4.Arch.binary64Infinity; omega, rfl⟩]

/-! ## The profile's tree and the binary64 tree

`Agrees t j` relates a profile tree to a binary64 tree with the same structure, keys and strings,
whose numbers are the binary64 data of the tree's naturals; a numeral agrees with any number,
since every reader refuses it. Both conversions give an agreeing pair (`agrees_toBinary64`,
`agrees_ofBinary64`), so one exactness proof serves the native face and the binary64 face. -/

mutual
/-- A profile tree and a binary64 tree agree. -/
inductive Agrees : NatJson → Json → Prop
  | null : Agrees .null .null
  | bool (b : Bool) : Agrees (.bool b) (.bool b)
  | nat (n : Nat) : Agrees (.nat n) (Effect4.Arch.Json.ofNat n)
  | numeral (text : String) (x : Float64) : Agrees (.numeral text) (.number x)
  | str (s : String) : Agrees (.str s) (.str s)
  | arr {ts : List NatJson} {js : List Json} : AgreesList ts js → Agrees (.arr ts) (.arr js)
  | obj {es : List (String × NatJson)} {fs : List (String × Json)} :
      AgreesEntries es fs → Agrees (.obj es) (.obj fs)

/-- `Agrees` over two lists, element by element. -/
inductive AgreesList : List NatJson → List Json → Prop
  | nil : AgreesList [] []
  | cons {t : NatJson} {j : Json} {ts : List NatJson} {js : List Json} :
      Agrees t j → AgreesList ts js → AgreesList (t :: ts) (j :: js)

/-- `Agrees` over two objects' entries, entry by entry, with the same keys in the same order. -/
inductive AgreesEntries : List (String × NatJson) → List (String × Json) → Prop
  | nil : AgreesEntries [] []
  | cons (k : String) {t : NatJson} {j : Json} {es : List (String × NatJson)}
      {fs : List (String × Json)} :
      Agrees t j → AgreesEntries es fs → AgreesEntries ((k, t) :: es) ((k, j) :: fs)
end

mutual
/-- A profile tree agrees with its binary64 image. A step of `json-read-located`. Its consumer is
`ShapeDoc.readLocated_exact`, the native face's exactness. -/
theorem agrees_toBinary64 : ∀ t : NatJson, Agrees t t.toBinary64
  | .null => .null
  | .bool b => .bool b
  | .nat n => .nat n
  | .numeral text => .numeral text Float64.nan
  | .str s => .str s
  | .arr ts => .arr (agreesList_toBinary64 ts)
  | .obj es => .obj (agreesEntries_toBinary64 es)
/-- `agrees_toBinary64` over a list. -/
theorem agreesList_toBinary64 : ∀ ts : List NatJson, AgreesList ts (NatJson.toBinary64List ts)
  | [] => .nil
  | t :: ts => .cons (agrees_toBinary64 t) (agreesList_toBinary64 ts)
/-- `agrees_toBinary64` over an object's entries. -/
theorem agreesEntries_toBinary64 :
    ∀ es : List (String × NatJson), AgreesEntries es (NatJson.toBinary64Entries es)
  | [] => .nil
  | (k, t) :: es => .cons k (agrees_toBinary64 t) (agreesEntries_toBinary64 es)
end

mutual
/-- A binary64 tree agrees with its profile tree. A step of `json-read-located`. Its consumer is
`Canonical.ofJsonAnyOrder_exact`, the binary64 face's exactness. -/
theorem agrees_ofBinary64 : ∀ j : Json, Agrees (NatJson.ofBinary64 j) j
  | .null => .null
  | .bool b => .bool b
  | .number x => by
    unfold NatJson.ofBinary64
    split
    · rename_i n hn
      have hb : Effect4.Arch.binary64OfNat n = x.bits := by
        unfold natOfBinary64 at hn
        split at hn
        · rename_i heq
          cases hn
          exact heq.2
        · cases hn
      obtain ⟨bits⟩ := x
      dsimp only at hb
      subst hb
      exact .nat n
    · exact .numeral "" x
  | .str s => .str s
  | .arr js => .arr (agreesList_ofBinary64 js)
  | .obj fs => .obj (agreesEntries_ofBinary64 fs)
/-- `agrees_ofBinary64` over a list. -/
theorem agreesList_ofBinary64 : ∀ js : List Json, AgreesList (NatJson.ofBinary64List js) js
  | [] => .nil
  | j :: js => .cons (agrees_ofBinary64 j) (agreesList_ofBinary64 js)
/-- `agrees_ofBinary64` over an object's entries. -/
theorem agreesEntries_ofBinary64 :
    ∀ fs : List (String × Json), AgreesEntries (NatJson.ofBinary64Entries fs) fs
  | [] => .nil
  | (k, j) :: fs => .cons k (agrees_ofBinary64 j) (agreesEntries_ofBinary64 fs)
end

/-- Agreeing objects have as many entries. A step of `readAt_exact`: the normaliser compares an
object's arity with its shape's. -/
theorem AgreesEntries.length_eq :
    ∀ {es : List (String × NatJson)} {fs : List (String × Json)},
      AgreesEntries es fs → es.length = fs.length
  | [], _, h => by cases h; rfl
  | _ :: es, _, h => by
    cases h with
    | cons k _ hrest =>
      simp only [List.length_cons, AgreesEntries.length_eq hrest]

/-- An entry the profile's object holds under a key, the agreeing binary64 object holds too, and
the two agree. A step of `readAt_exact` (fields, and a case object's tag). -/
theorem AgreesEntries.entryOf_some {n : String} :
    ∀ {es : List (String × NatJson)} {fs : List (String × Json)} {t : NatJson},
      AgreesEntries es fs → NatJson.entryOf n es = some t → ∃ j, entryOf n fs = some j ∧ Agrees t j
  | [], _, _, _, he => by cases he
  | (k, t') :: es, _, t, h, he => by
    cases h with
    | cons _ ht hrest =>
      unfold NatJson.entryOf at he
      unfold entryOf
      split at he
      · rename_i hk
        cases he
        rw [if_pos hk]
        exact ⟨_, rfl, ht⟩
      · rename_i hk
        rw [if_neg hk]
        exact AgreesEntries.entryOf_some hrest he

/-- A list family's cases, as `listParts?` finds them: `nil` and `cons`, with distinct tags. A
step of `readSpine_exact`, through `printIn_nil` and `printIn_cons`. -/
theorem listParts?_eq {cases : List (String × Nat × List (String × Shape))} {t0 t1 : Nat}
    {item tail : Shape} (h : listParts? cases = some (t0, t1, item, tail)) :
    cases = [("nil", t0, []), ("cons", t1, [("head", item), ("tail", tail)])] ∧ t0 ≠ t1 := by
  unfold listParts? at h
  split at h
  · split at h
    · rename_i hc
      cases h
      obtain ⟨h0, h1, h2, h3, h4⟩ := hc
      subst h0 h1 h2 h3
      exact ⟨rfl, h4⟩
    · cases h
  · cases h

/-- A list family's `nil` prints as its case object. A step of `readSpine_exact`. -/
theorem printIn_nil {defs : List (String × Shape)} {s : Shape} {name : String}
    {cases : List (String × Nat × List (String × Shape))} {t0 t1 : Nat} {item tail : Shape}
    (hs : headShape defs s = .sum name cases) (hp : listParts? cases = some (t0, t1, item, tail)) :
    printIn defs s (.ctor t0 []) = nilObject := by
  obtain ⟨hc, _⟩ := listParts?_eq hp
  subst hc
  simp only [printIn, hs, caseAt, ↓reduceIte, allNullary, nilObject]
  rfl

/-- A list family's `cons` prints as its case object, head and tail under their shapes. A step of
`readSpine_exact`. -/
theorem printIn_cons {defs : List (String × Shape)} {s : Shape} {name : String}
    {cases : List (String × Nat × List (String × Shape))} {t0 t1 : Nat} {item tail : Shape}
    (hs : headShape defs s = .sum name cases) (hp : listParts? cases = some (t0, t1, item, tail))
    (x rest : Val) :
    printIn defs s (.ctor t1 [x, rest]) =
      .obj [("_tag", .str "cons"), ("head", printIn defs item x), ("tail", printIn defs tail rest)] := by
  obtain ⟨hc, hne⟩ := listParts?_eq hp
  subst hc
  simp only [printIn, hs, caseAt, if_neg hne, ↓reduceIte, allNullary, printFields]
  rfl


/-! ## Exactness of the profile's reader -/

/-- A bound `Except` that answers reads its first step. -/
theorem except_bind_ok {ε α β : Type} {e : Except ε α} {f : α → Except ε β} {b : β}
    (h : e.bind f = .ok b) : ∃ a, e = .ok a ∧ f a = .ok b := by
  cases e with
  | error x => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A mapped `Except` that answers reads its argument. -/
theorem except_map_ok {ε α β : Type} {e : Except ε α} {f : α → β} {b : β}
    (h : e.map f = .ok b) : ∃ a, e = .ok a ∧ f a = b := by
  cases e with
  | error x => cases h
  | ok a =>
    cases h
    exact ⟨a, rfl, rfl⟩

/-- The fields read are as many as the shape's. A step of `readFieldsAt_exact`. -/
theorem readFieldsAt_length {defs : List (String × Shape)} {es : List (String × NatJson)}
    {p : List JsonStep} :
    ∀ {fields : List (String × Shape)} {xs : List Val},
      readFieldsAt defs fields es p = .ok xs → xs.length = fields.length
  | [], _, h => by
    unfold readFieldsAt at h
    cases h
    rfl
  | (n, s) :: fields, xs, h => by
    unfold readFieldsAt at h
    split at h
    · obtain ⟨x, -, h2⟩ := except_bind_ok h
      obtain ⟨xs', hxs, rfl⟩ := except_map_ok h2
      simp only [List.length_cons, readFieldsAt_length hxs]
    · cases h

/-- As many printed fields as values, when the values are as many as the fields. -/
theorem printFields_length {defs : List (String × Shape)} :
    ∀ {fields : List (String × Shape)} {xs : List Val},
      xs.length = fields.length → (printFields defs fields xs).length = fields.length
  | [], [], _ => rfl
  | (_, _) :: fields, _ :: xs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [printFields, List.length_cons, printFields_length h]

/-- Under an option, a value that is not `null` is ordered under the item, past one layer. A step
of `readAt_exact`. -/
theorem orderIn_option {defs : List (String × Shape)} {seen seen' : List String}
    {s item : Shape} {j : Json} (hl : optionLayer? defs s seen = some (item, seen'))
    (hj : j ≠ .null) : orderIn defs seen s j = orderIn defs seen' item j := by
  rw [orderIn.eq_def]
  cases j with
  | null => exact absurd rfl hj
  | _ =>
    simp only [optionLayer?_head hl]
    split
    next item'' seen'' hl' =>
      rw [hl] at hl'
      cases hl'
      rfl
    next hl' =>
      rw [hl] at hl'
      cases hl'

/-- The shape's fields are ordered one by one, each at the first entry with its name. A step of
`readFieldsAt_exact`. -/
theorem orderFields_cons {defs : List (String × Shape)} {n : String} {s : Shape}
    {fields : List (String × Shape)} {entries : List (String × Json)} {j : Json}
    (hj : entryOf n entries = some j) :
    orderFields defs ((n, s) :: fields) entries =
      (orderFields defs fields entries).map ((n, orderIn defs [] s j) :: ·) := by
  rw [orderFields.eq_def]
  dsimp only
  split
  next j' hj' =>
    rw [hj] at hj'
    cases hj'
    rfl
  next hj' =>
    rw [hj] at hj'
    cases hj'

/-- A tree that agrees with `null` is `null`. -/
theorem Agrees.null_right {t : NatJson} (h : Agrees t .null) : t = .null := by
  cases h
  rfl


mutual
/-- **Whatever the profile's reader reads is the value whose print is its input, normalised**:
for a binary64 tree that agrees with the input, the normaliser's output is the print. The
pointer's step of `json-read-located`. Its consumer is `ShapeDoc.readLocated_exact`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem readAt_exact {defs : List (String × Shape)} :
    ∀ {seen : List String} {s : Shape} {t : NatJson} {j : Json} {p : List JsonStep} {v : Val},
      Agrees t j → readAt defs seen s t p = .ok v → orderIn defs seen s j = printIn defs s v
  | seen, s, t, j, p, v, hA, h => by
    unfold readAt at h
    split at h
    next _ _ _ hs =>
      cases h
      cases hA
      rw [orderIn.eq_def]
      simp only [hs, printIn]
    next t' _ _ _ hs hnull =>
      split at h
      next item seen' hl =>
        obtain ⟨x, hx, rfl⟩ := except_map_ok h
        have hj : j ≠ .null := fun hj => hnull (Agrees.null_right (hj ▸ hA))
        rw [orderIn_option hl hj, readAt_exact hA hx]
        simp only [printIn, optionLayer?_head hl]
      next => cases h
    next _ _ item ts hs =>
      obtain ⟨xs, hxs, rfl⟩ := except_map_ok h
      cases hA with
      | arr hts =>
        rw [orderIn.eq_def]
        simp only [hs, printIn, readItems_exact hts hxs]
    next _ _ f g a b hs =>
      obtain ⟨x, hx, h2⟩ := except_bind_ok h
      obtain ⟨y, hy, rfl⟩ := except_map_ok h2
      cases hA with
      | arr hts =>
        cases hts with
        | cons ha hts' =>
          cases hts' with
          | cons hb hnil =>
            cases hnil
            rw [orderIn.eq_def]
            simp only [hs, printIn, readAt_exact ha hx, readAt_exact hb hy]
    next _ _ name cases ts hs =>
      split at h
      next t0 t1 item tail hp =>
        cases hA with
        | arr hts =>
          rw [orderIn.eq_def]
          simp only [hs, hp]
          exact readSpine_exact hs hp hts h
      next => cases h
    next _ _ name fields entries hs =>
      split at h
      next => cases h
      next =>
        obtain ⟨xs, hxs, h2⟩ := except_bind_ok h
        unfold closeObject at h2
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h2
        split at h2
        next => cases h2
        next =>
          split at h2
          next hlen =>
            cases h2
            cases hA with
            | @obj _ fs hes =>
              have hl : (printFields defs fields xs).length = fs.length := by
                rw [printFields_length (readFieldsAt_length hxs), hlen, AgreesEntries.length_eq hes]
              rw [orderIn.eq_def]
              simp only [hs, readFieldsAt_exact hes hxs]
              rw [if_pos hl]
              simp only [printIn, hs]
          next => cases h2
    next _ _ name cases entries hs =>
      split at h
      next => cases h
      next hnull =>
        split at h
        next tagName htag =>
          split at h
          next tag fields hname =>
            split at h
            next => cases h
            next =>
              obtain ⟨xs, hxs, h2⟩ := except_bind_ok h
              unfold closeObject at h2
              simp only [↓reduceIte] at h2
              split at h2
              next => cases h2
              next =>
                split at h2
                next hlen =>
                  cases h2
                  cases hA with
                  | @obj _ fs hes =>
                    obtain ⟨jt, hjt, hag⟩ := AgreesEntries.entryOf_some hes htag
                    cases hag
                    have hl : (printFields defs fields xs).length + 1 = fs.length := by
                      rw [printFields_length (readFieldsAt_length hxs), hlen,
                        AgreesEntries.length_eq hes]
                    rw [orderIn.eq_def]
                    simp only [hs, hjt, hname, readFieldsAt_exact hes hxs]
                    rw [if_pos hl]
                    simp only [printIn, hs, tagOfName_exact hname, hnull, Bool.false_eq_true,
                      ↓reduceIte]
                next => cases h2
          next => cases h
        next => cases h
        next => cases h
    next _ _ hs =>
      cases h
      cases hA
      rw [orderIn.eq_def]
      simp only [hs, printIn]
    next _ _ b hs =>
      cases h
      cases hA
      rw [orderIn.eq_def]
      simp only [hs, printIn]
    next _ _ n hs =>
      split at h
      next =>
        cases h
        cases hA
        rw [orderIn.eq_def]
        simp only [hs, printIn, Effect4.Arch.Json.ofNat]
      next => cases h
    next => cases h
    next _ _ x hs =>
      cases h
      cases hA
      rw [orderIn.eq_def]
      simp only [hs, printIn]
    next _ _ hx hs =>
      split at h
      next d hd =>
        cases h
        cases hA
        rw [orderIn.eq_def]
        simp only [hs, printIn, canonicalHex?_exact hd]
      next => cases h
    next _ _ hx hs =>
      split at h
      next d hd =>
        cases h
        cases hA
        rw [orderIn.eq_def]
        simp only [hs, printIn, canonicalHex?_exact hd]
      next => cases h
    next _ _ name cases hs =>
      split at h
      next hall =>
        split at h
        next tag htag =>
          cases h
          cases hA
          rw [orderIn.eq_def]
          simp only [hs, printIn, tagOfName_exact htag, hall, ↓reduceIte]
        next => cases h
        next => cases h
      next => cases h
    next _ _ k hx hs =>
      split at h
      next d hd =>
        cases h
        cases hA
        rw [orderIn.eq_def]
        simp only [hs, printIn, canonicalHex?_exact hd]
      next => cases h
    next _ _ kn hx hs =>
      split at h
      next k hk =>
        split at h
        next hname =>
          split at h
          next d hd =>
            cases h
            cases hA with
            | obj hes =>
              cases hes with
              | cons _ hkind hes' =>
                cases hes' with
                | cons _ haddr hnil =>
                  cases hnil
                  cases hkind
                  cases haddr
                  have hkj : kindJson k.byte = .str kn := by
                    unfold kindName? at hname
                    obtain ⟨k', hk', hname'⟩ := Option.map_eq_some_iff.mp hname
                    unfold kindJson
                    rw [hk']
                    exact congrArg Json.str hname'
                  rw [orderIn.eq_def]
                  simp only [hs, printIn, hkj, canonicalHex?_exact hd]
          next => cases h
        next => cases h
      next => cases h
    next => cases h
termination_by seen s t => (sizeOf t, unseenDefs defs seen, sizeOf s)
decreasing_by
  all_goals subst_vars
  · exact Prod.Lex.right _ (optionLayer?_lt ‹_›)
  all_goals
    apply Prod.Lex.left
    simp only [NatJson.arr.sizeOf_spec, NatJson.obj.sizeOf_spec, List.cons.sizeOf_spec]
    omega

/-- The elements read are printed as the list ordered. A step of `readAt_exact`. -/
theorem readItems_exact {defs : List (String × Shape)} :
    ∀ {item : Shape} {ts : List NatJson} {js : List Json} {p : List JsonStep}
      {i : Nat} {xs : List Val},
      AgreesList ts js → readItems defs item ts p i = .ok xs →
        orderList defs item js = printList defs item xs
  | _, [], _, _, _, _, hA, h => by
    cases hA
    unfold readItems at h
    cases h
    simp only [orderList, printList]
  | item, t :: ts, _, p, i, _, hA, h => by
    cases hA with
    | cons ht hts =>
      unfold readItems at h
      obtain ⟨x, hx, h2⟩ := except_bind_ok h
      obtain ⟨xs, hxs, rfl⟩ := except_map_ok h2
      simp only [orderList, printList, readAt_exact ht hx, readItems_exact hts hxs]
termination_by _ ts => (sizeOf ts, 0, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec]
    omega

/-- The fields read are the entries ordered. A step of `readAt_exact`. -/
theorem readFieldsAt_exact {defs : List (String × Shape)} {es : List (String × NatJson)}
    {fs : List (String × Json)} {p : List JsonStep} :
    ∀ {fields : List (String × Shape)} {xs : List Val},
      AgreesEntries es fs → readFieldsAt defs fields es p = .ok xs →
        orderFields defs fields fs = some (printFields defs fields xs)
  | [], _, _, h => by
    unfold readFieldsAt at h
    cases h
    simp only [orderFields, printFields]
  | (n, s) :: fields, _, hA, h => by
    unfold readFieldsAt at h
    split at h
    next t ht =>
      obtain ⟨x, hx, h2⟩ := except_bind_ok h
      obtain ⟨xs, hxs, rfl⟩ := except_map_ok h2
      obtain ⟨j, hj, hag⟩ := AgreesEntries.entryOf_some hA ht
      rw [orderFields_cons hj]
      simp only [readFieldsAt_exact hA hxs, readAt_exact hag hx, Option.map_some, printFields]
    next => cases h
termination_by fields => (sizeOf es, 0, fields.length)
decreasing_by
  · exact Prod.Lex.left _ _ (NatJson.sizeOf_entryOf_lt ‹_›)
  · exact Prod.Lex.right _ (Prod.Lex.right _ (Nat.lt_succ_self _))

/-- A list family's array is printed as the normaliser writes its cells. A step of
`readAt_exact`. -/
theorem readSpine_exact {defs : List (String × Shape)} :
    ∀ {t0 t1 : Nat} {item tail s : Shape} {name : String}
      {cases : List (String × Nat × List (String × Shape))} {ts : List NatJson} {js : List Json}
      {p : List JsonStep} {i : Nat} {v : Val},
      headShape defs s = .sum name cases → listParts? cases = some (t0, t1, item, tail) →
        AgreesList ts js → readSpine defs t0 t1 item tail ts p i = .ok v →
          orderSpine defs item tail js = printIn defs s v
  | _, _, _, _, _, _, _, [], _, _, _, _, hs, hp, hA, h => by
    cases hA
    unfold readSpine at h
    cases h
    rw [printIn_nil hs hp]
    simp only [orderSpine]
  | _, _, item, tail, _, _, _, t :: ts, _, p, i, _, hs, hp, hA, h => by
    cases hA with
    | cons ht hts =>
      unfold readSpine at h
      obtain ⟨x, hx, h2⟩ := except_bind_ok h
      obtain ⟨rest, hrest, rfl⟩ := except_map_ok h2
      rw [printIn_cons hs hp]
      split at hrest
      next name' cases' htail =>
        split at hrest
        next t0' t1' item' tail' hp' =>
          simp only [orderSpine, htail, hp', readAt_exact ht hx,
            readSpine_exact htail hp' hts hrest]
        next => cases hrest
      next => cases hrest
termination_by _ _ _ _ _ _ _ ts => (sizeOf ts, 0, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec]
    omega
end

/-- **A value tree the profile's reader reads is the one whose print is any agreeing binary64
tree, normalised.** A step of `json-read-located`. Its consumers are `ShapeDoc.readLocated_exact`
and `Canonical.ofJsonAnyOrder_exact`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem ShapeDoc.readLocated_exact_of {doc : ShapeDoc} {t : NatJson} {j : Json} {v : Val}
    (hA : Agrees t j) (h : doc.readLocated t = .ok v) : doc.print v = doc.order j := by
  unfold ShapeDoc.readLocated at h
  unfold ShapeDoc.print ShapeDoc.order
  exact (readAt_exact hA h).symm

/-- **Whatever the profile's reader reads from a tree is the value whose print is the tree's
binary64 image, normalised by `ShapeDoc.order`.** Exactness of the native face. A step of
`json-read-located`. Its consumer is `Canonical.readLocated_exact`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem ShapeDoc.readLocated_exact {doc : ShapeDoc} {t : NatJson} {v : Val}
    (h : doc.readLocated t = .ok v) : doc.print v = doc.order t.toBinary64 :=
  ShapeDoc.readLocated_exact_of (agrees_toBinary64 t) h

/-- **A carrier read from the profile's tree is the carrier whose cases print is the tree's
binary64 image, normalised.** A step of `json-read-located`. Its consumer is
`CodecProfile.profileLocated_exact` (`Laws/Tool/CodecProfile.lean`). -/
@[semantics "exact-codecs" (requirement := R8)]
theorem Canonical.readLocated_exact {α : Type} [Canonical α] {t : NatJson} {a : α}
    (h : Canonical.readLocated t = .ok a) :
    (Canonical.shape α).print (Canonical.toVal a) = (Canonical.shape α).order t.toBinary64 := by
  unfold Canonical.readLocated at h
  obtain ⟨v, hv, ha⟩ := except_bind_ok h
  split at ha
  · rename_i a' ha'
    cases ha
    have hva := Canonical.ofVal_exact ha'
    subst hva
    exact ShapeDoc.readLocated_exact hv
  · cases ha

/-- **A carrier read from an agent's JSON is the carrier whose cases print the normalised JSON
is**: exactness modulo the named normaliser (`ShapeDoc.order`), which puts objects in the shape's
order and writes each list given as an array as its cases. The reader is the profile's located
reader on the binary64 tree's profile tree (`NatJson.ofBinary64`). A step of `json-read-exact`.
Its consumer: the session tool's JSON profile (`Tool.CodecProfile`), which reads a request
through it and prints through `Canonical.print`, each list an array. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem Canonical.ofJsonAnyOrder_exact {α : Type} [Canonical α] {j : Json} {a : α}
    (h : Canonical.ofJsonAnyOrder j = some a) :
    (Canonical.shape α).print (Canonical.toVal a) = (Canonical.shape α).order j := by
  unfold Canonical.ofJsonAnyOrder at h
  cases hr : Canonical.readLocated (α := α) (NatJson.ofBinary64 j) with
  | error r =>
    rw [hr] at h
    cases h
  | ok a' =>
    rw [hr] at h
    cases h
    unfold Canonical.readLocated at hr
    obtain ⟨v, hv, ha⟩ := except_bind_ok hr
    split at ha
    · rename_i a'' ha'
      cases ha
      have hva := Canonical.ofVal_exact ha'
      subst hva
      exact ShapeDoc.readLocated_exact_of (agrees_ofBinary64 j) hv
    · cases ha

/-- **The located reader erases to its projection**: forgetting where and why it refuses gives
the `Option` reader. The old `Option` readers are projections of the located one (Codex's R4.1),
so this law holds by definition, and it is the bridge their callers rewrite by. A step of
`json-read-located`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem ShapeDoc.readLocated_erases (doc : ShapeDoc) (t : NatJson) :
    (doc.readLocated t).toOption = doc.readAny t := rfl


/-! ## The sites of the profile's refusals -/

/-- **A site in a tree**: a value's path reaches a value of the tree; a missing field's parent is an
object of the tree, and it lacks the field; a place in the shape is the shape's root. The relation
`readLocated_site` holds every refusal to. -/
def _root_.Effect4.JsonSite.Valid (t : NatJson) : JsonSite → Prop
  | .value p => ∃ u, t.at? p = some u
  | .missing p f => ∃ entries, t.at? p = some (.obj entries) ∧ NatJson.entryOf f entries = none
  | .schema p => p = []

/-- A path's value is reached in two legs. A step of `readLocated_site`. -/
theorem NatJson.at?_append (q : List JsonStep) :
    ∀ (p : List JsonStep) (t : NatJson), t.at? (p ++ q) = (t.at? p).bind (·.at? q)
  | [], _ => rfl
  | .key k :: p, t => by
    cases t with
    | obj entries =>
      simp only [List.cons_append, NatJson.at?]
      cases NatJson.entryOf k entries with
      | none => rfl
      | some t' => exact NatJson.at?_append q p t'
    | _ => rfl
  | .index i :: p, t => by
    cases t with
    | arr elements =>
      simp only [List.cons_append, NatJson.at?]
      cases elements[i]? with
      | none => rfl
      | some t' => exact NatJson.at?_append q p t'
    | _ => rfl

/-- An array's element is reached one index further. A step of `readLocated_site`. -/
theorem NatJson.at?_index {t₀ : NatJson} {p : List JsonStep} {ts : List NatJson} {i : Nat}
    {t : NatJson} (hp : t₀.at? p = some (.arr ts)) (hi : ts[i]? = some t) :
    t₀.at? (p ++ [.index i]) = some t := by
  rw [NatJson.at?_append, hp]
  simp only [Option.bind_some, NatJson.at?, hi]

/-- An object's entry is reached one key further. A step of `readLocated_site`. -/
theorem NatJson.at?_key {t₀ : NatJson} {p : List JsonStep} {entries : List (String × NatJson)}
    {k : String} {t : NatJson} (hp : t₀.at? p = some (.obj entries))
    (hk : NatJson.entryOf k entries = some t) : t₀.at? (p ++ [.key k]) = some t := by
  rw [NatJson.at?_append, hp]
  simp only [Option.bind_some, NatJson.at?, hk]

/-- The element a dropped list starts with is at its index, and the rest is one more dropped. -/
theorem drop_eq_cons {α : Type} :
    ∀ {l : List α} {i : Nat} {a : α} {rest : List α},
      l.drop i = a :: rest → l[i]? = some a ∧ l.drop (i + 1) = rest
  | [], i, _, _, h => by
    rw [List.drop_nil] at h
    cases h
  | _ :: _, 0, _, _, h => by
    rw [List.drop_zero] at h
    cases h
    exact ⟨rfl, rfl⟩
  | _ :: xs, i + 1, _, _, h => by
    rw [List.drop_succ_cons] at h
    rw [List.getElem?_cons_succ, List.drop_succ_cons]
    exact drop_eq_cons h

/-- A mapped `Except` that refuses refused before the map. -/
theorem except_map_error {ε α β : Type} {e : Except ε α} {f : α → β} {r : ε}
    (h : e.map f = .error r) : e = .error r := by
  cases e with
  | error x =>
    cases h
    rfl
  | ok a => cases h

/-- A bound `Except` that refuses refused at its first step or at its second. -/
theorem except_bind_error {ε α β : Type} {e : Except ε α} {f : α → Except ε β} {r : ε}
    (h : e.bind f = .error r) : e = .error r ∨ ∃ a, e = .ok a ∧ f a = .error r := by
  cases e with
  | error x =>
    cases h
    exact .inl rfl
  | ok a => exact .inr ⟨a, rfl, h⟩

/-- An object's last checks refuse at the object. A step of `readLocated_site`. -/
theorem closeObject_site {s : Shape} {fields : List (String × Shape)} {tagged : Bool} {tag : Nat}
    {entries : List (String × NatJson)} {p : List JsonStep} {args : List Val} {r : JsonRefusal}
    (h : closeObject s fields tagged tag entries p args = .error r) : r.site = .value p := by
  unfold closeObject at h
  split at h
  · cases h
    rfl
  · generalize (if tagged = true then 1 else 0) = k at h
    split at h
    · cases h
    · cases h
      rfl

mutual
/-- **Every refusal of the profile's reader names a site of its input**: a value it holds, or a
field missing from an object it holds. The pointer's step of `json-read-located`'s diagnostic
property. Its consumer is `ShapeDoc.readLocated_site`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem readAt_site {defs : List (String × Shape)} {t₀ : NatJson} :
    ∀ {seen : List String} {s : Shape} {t : NatJson} {p : List JsonStep} {r : JsonRefusal},
      t₀.at? p = some t → readAt defs seen s t p = .error r → JsonSite.Valid t₀ r.site
  | seen, s, t, p, r, hp, h => by
    unfold readAt at h
    split at h
    next => cases h
    next t' _ _ _ hs hnull =>
      split at h
      next item seen' hl => exact readAt_site hp (except_map_error h)
      next =>
        cases h
        exact ⟨_, hp⟩
    next _ _ item ts hs => exact readItems_site hp List.drop_zero (except_map_error h)
    next _ _ f g a b hs =>
      rcases except_bind_error h with h1 | ⟨x, -, h2⟩
      · exact readAt_site (NatJson.at?_index hp rfl) h1
      · exact readAt_site (NatJson.at?_index hp rfl) (except_map_error h2)
    next _ _ name cases ts hs =>
      split at h
      next => exact readSpine_site hp List.drop_zero h
      next =>
        cases h
        exact ⟨_, hp⟩
    next _ _ name fields entries hs =>
      split at h
      next =>
        cases h
        exact ⟨_, hp⟩
      next =>
        rcases except_bind_error h with h1 | ⟨xs, -, h2⟩
        · exact readFieldsAt_site hp h1
        · rw [closeObject_site h2]
          exact ⟨_, hp⟩
    next _ _ name cases entries hs =>
      split at h
      next =>
        cases h
        exact ⟨_, hp⟩
      next =>
        split at h
        next tagName htag =>
          split at h
          next tag fields hname =>
            split at h
            next =>
              cases h
              exact ⟨_, hp⟩
            next =>
              rcases except_bind_error h with h1 | ⟨xs, -, h2⟩
              · exact readFieldsAt_site hp h1
              · rw [closeObject_site h2]
                exact ⟨_, hp⟩
          next =>
            cases h
            exact ⟨_, hp⟩
        next u _ htag =>
          cases h
          exact ⟨_, NatJson.at?_key hp htag⟩
        next htag =>
          cases h
          exact ⟨entries, hp, htag⟩
    next =>
      cases h
    next =>
      cases h
    next _ _ n hs =>
      split at h
      next => cases h
      next =>
        cases h
        exact ⟨_, hp⟩
    next =>
      cases h
      exact ⟨_, hp⟩
    next => cases h
    next _ _ hx hs =>
      split at h
      next => cases h
      next =>
        cases h
        exact ⟨_, hp⟩
    next _ _ hx hs =>
      split at h
      next => cases h
      next =>
        cases h
        exact ⟨_, hp⟩
    next _ _ name cases hs =>
      split at h
      next =>
        split at h
        next => cases h
        next =>
          cases h
          exact ⟨_, hp⟩
        next =>
          cases h
          exact ⟨_, hp⟩
      next =>
        cases h
        exact ⟨_, hp⟩
    next _ _ k hx hs =>
      split at h
      next => cases h
      next =>
        cases h
        exact ⟨_, hp⟩
    next _ _ kn hx hs =>
      split at h
      next =>
        split at h
        next =>
          split at h
          next => cases h
          next =>
            cases h
            exact ⟨_, hp⟩
        next =>
          cases h
          exact ⟨_, hp⟩
      next =>
        cases h
        exact ⟨_, hp⟩
    next =>
      cases h
      exact ⟨_, hp⟩
termination_by seen s t => (sizeOf t, unseenDefs defs seen, sizeOf s)
decreasing_by
  all_goals subst_vars
  · exact Prod.Lex.right _ (optionLayer?_lt ‹_›)
  all_goals
    apply Prod.Lex.left
    simp only [NatJson.arr.sizeOf_spec, NatJson.obj.sizeOf_spec, List.cons.sizeOf_spec]
    omega

/-- A list's refusals name sites of the input; an element keeps its index. A step of
`readAt_site`. -/
theorem readItems_site {defs : List (String × Shape)} {t₀ : NatJson} {ts₀ : List NatJson}
    {p : List JsonStep} :
    ∀ {item : Shape} {ts : List NatJson} {i : Nat} {r : JsonRefusal},
      t₀.at? p = some (.arr ts₀) → ts₀.drop i = ts →
        readItems defs item ts p i = .error r → JsonSite.Valid t₀ r.site
  | _, [], _, _, _, _, h => by
    unfold readItems at h
    cases h
  | item, t :: ts, i, r, hp, hd, h => by
    unfold readItems at h
    rcases except_bind_error h with h1 | ⟨x, -, h2⟩
    · exact readAt_site (NatJson.at?_index hp (drop_eq_cons hd).1) h1
    · exact readItems_site hp (drop_eq_cons hd).2 (except_map_error h2)
termination_by _ ts => (sizeOf ts, 0, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec]
    omega

/-- A structure's or a case's refusals name sites of the input: a field's value, or the object
that lacks a field. A step of `readAt_site`. -/
theorem readFieldsAt_site {defs : List (String × Shape)} {t₀ : NatJson}
    {entries : List (String × NatJson)} {p : List JsonStep} :
    ∀ {fields : List (String × Shape)} {r : JsonRefusal},
      t₀.at? p = some (.obj entries) → readFieldsAt defs fields entries p = .error r →
        JsonSite.Valid t₀ r.site
  | [], _, _, h => by
    unfold readFieldsAt at h
    cases h
  | (n, s) :: fields, r, hp, h => by
    unfold readFieldsAt at h
    split at h
    next t ht =>
      rcases except_bind_error h with h1 | ⟨x, -, h2⟩
      · exact readAt_site (NatJson.at?_key hp ht) h1
      · exact readFieldsAt_site hp (except_map_error h2)
    next ht =>
      cases h
      exact ⟨entries, hp, ht⟩
termination_by fields => (sizeOf entries, 0, fields.length)
decreasing_by
  · exact Prod.Lex.left _ _ (NatJson.sizeOf_entryOf_lt ‹_›)
  · exact Prod.Lex.right _ (Prod.Lex.right _ (Nat.lt_succ_self _))

/-- A list family's array's refusals name sites of the input; an element keeps its index. A step
of `readAt_site`. -/
theorem readSpine_site {defs : List (String × Shape)} {t₀ : NatJson} {ts₀ : List NatJson}
    {p : List JsonStep} :
    ∀ {t0 t1 : Nat} {item tail : Shape} {ts : List NatJson} {i : Nat} {r : JsonRefusal},
      t₀.at? p = some (.arr ts₀) → ts₀.drop i = ts →
        readSpine defs t0 t1 item tail ts p i = .error r → JsonSite.Valid t₀ r.site
  | _, _, _, _, [], _, _, _, _, h => by
    unfold readSpine at h
    cases h
  | _, _, item, tail, t :: ts, i, r, hp, hd, h => by
    unfold readSpine at h
    rcases except_bind_error h with h1 | ⟨x, -, h2⟩
    · exact readAt_site (NatJson.at?_index hp (drop_eq_cons hd).1) h1
    · have h3 := except_map_error h2
      split at h3
      next =>
        split at h3
        next => exact readSpine_site hp (drop_eq_cons hd).2 h3
        next =>
          cases h3
          exact ⟨_, hp⟩
      next =>
        cases h3
        exact ⟨_, hp⟩
termination_by _ _ _ _ ts => (sizeOf ts, 0, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    simp only [List.cons.sizeOf_spec]
    omega
end

/-- **Every refusal of the profile's reader names a site of its input** (Codex's `readLocated_site`,
with the amended relation: a missing field names its present parent). The pointer's step of
`json-read-located`'s diagnostic property. Its consumer is `CodecProfile.profileLocated_site`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem ShapeDoc.readLocated_site {doc : ShapeDoc} {t : NatJson} {r : JsonRefusal}
    (h : doc.readLocated t = .error r) : JsonSite.Valid t r.site :=
  readAt_site (t₀ := t) (p := []) rfl h

/-- A carrier's refusals name sites of its input: the value tree's, or the root, where the carrier
refuses a tree that fits. A step of `CodecProfile.profileLocated_site`. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem Canonical.readLocated_site {α : Type} [Canonical α] {t : NatJson} {r : JsonRefusal}
    (h : Canonical.readLocated (α := α) t = .error r) : JsonSite.Valid t r.site := by
  unfold Canonical.readLocated at h
  rcases except_bind_error h with h1 | ⟨v, -, h2⟩
  · exact ShapeDoc.readLocated_site h1
  · split at h2
    · cases h2
    · cases h2
      exact ⟨t, rfl⟩


/-! ## The profile's tree within the profile and its binary64 image (K1)

A profile tree whose naturals are at most `NatJson.limit` and that holds no numeral is the profile
tree of its own binary64 image (`ofBinary64_toBinary64`). So the native face, which builds the
profile's tree from text, and the binary64 face, which builds the binary64 tree, read such a
tree alike. This replaces `kit_json.ml`'s comment-only caveat K1 ("the two spellings agree below
2^53") with a theorem. -/

mutual
/-- **A profile tree within the profile**: every natural at most `NatJson.limit`, and no numeral. -/
def _root_.Effect4.NatJson.within : NatJson → Bool
  | .nat n => decide (n ≤ NatJson.limit)
  | .numeral _ => false
  | .arr ts => NatJson.withinList ts
  | .obj entries => NatJson.withinEntries entries
  | _ => true

/-- `within` over a list. -/
def _root_.Effect4.NatJson.withinList : List NatJson → Bool
  | [] => true
  | t :: ts => t.within && NatJson.withinList ts

/-- `within` over an object's entries. -/
def _root_.Effect4.NatJson.withinEntries : List (String × NatJson) → Bool
  | [] => true
  | (_, t) :: entries => t.within && NatJson.withinEntries entries
end

mutual
/-- **A profile tree within the profile is the profile tree of its binary64 image.** The step of
`CodecProfile.read_toBinary64` (`Laws/Tool/CodecProfile.lean`): the two faces read alike within
the profile. Concept `exact-codecs`, requirement R8. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem ofBinary64_toBinary64 : ∀ {t : NatJson}, t.within = true → NatJson.ofBinary64 t.toBinary64 = t
  | .null, _ => rfl
  | .bool _, _ => rfl
  | .nat n, h => by
    simp only [NatJson.within, decide_eq_true_eq] at h
    have hn : n < 2 ^ 53 := by
      unfold NatJson.limit at h
      omega
    simp only [NatJson.toBinary64, Effect4.Arch.Json.ofNat, NatJson.ofBinary64,
      natOfBinary64_binary64OfNat hn]
  | .numeral _, h => by simp only [NatJson.within, Bool.false_eq_true] at h
  | .str _, _ => rfl
  | .arr _, h => by
    simp only [NatJson.within] at h
    simp only [NatJson.toBinary64, NatJson.ofBinary64, ofBinary64List_toBinary64List h]
  | .obj _, h => by
    simp only [NatJson.within] at h
    simp only [NatJson.toBinary64, NatJson.ofBinary64, ofBinary64Entries_toBinary64Entries h]

/-- `ofBinary64_toBinary64` over a list. -/
theorem ofBinary64List_toBinary64List :
    ∀ {ts : List NatJson}, NatJson.withinList ts = true →
      NatJson.ofBinary64List (NatJson.toBinary64List ts) = ts
  | [], _ => rfl
  | _ :: _, h => by
    simp only [NatJson.withinList, Bool.and_eq_true] at h
    simp only [NatJson.toBinary64List, NatJson.ofBinary64List, ofBinary64_toBinary64 h.1,
      ofBinary64List_toBinary64List h.2]

/-- `ofBinary64_toBinary64` over an object's entries. -/
theorem ofBinary64Entries_toBinary64Entries :
    ∀ {entries : List (String × NatJson)}, NatJson.withinEntries entries = true →
      NatJson.ofBinary64Entries (NatJson.toBinary64Entries entries) = entries
  | [], _ => rfl
  | (_, _) :: _, h => by
    simp only [NatJson.withinEntries, Bool.and_eq_true] at h
    simp only [NatJson.toBinary64Entries, NatJson.ofBinary64Entries, ofBinary64_toBinary64 h.1,
      ofBinary64Entries_toBinary64Entries h.2]
end

end Effect4.Store
