import Hash.Sha256.Api
import Effect4.Store.Val

/-!
# Store.Digest

Owner: the content address (SHA-256 of a byte string) and the one hexadecimal codec.

`Digest`, `sha256`, `Digest.hex` and `sha256_length` are today's `src/Effect4/Store/Digest.lean`
verbatim: the hash is lean4-hash's `Hash.Sha256.sha256`, whose meaning is `sha256_spec` (FIPS
180-4) and whose family reaches no `Classical.choice`; the digest is a byte list so it has
decidable equality and can key a store; the hex spelling is the lowercase two-characters-per-
byte form (`Digest.lean:39-55`). No security property is claimed: a digest is an address, and
every law that would need collision freedom names it as a hypothesis.

The hex codec is the one the plan retires the other two copies for (`OCaml5.Bridge`,
`Surface.Observability`; the facts note §2). It works on code points: `hexCodes` writes the
lowercase digits of a byte string, `bytesOfHexCodes` reads digits of either case, and the
`List Char` and `String` faces are maps over those. It is exact up to case
(`hexCodes_of_bytesOfHexCodes`: what decodes, re-printed, is the input lowercased) and exact on
its own output (`bytesOfHexCodes_hexCodes`). `Digest.ofHex?` reads a string through its UTF-8
bytes, `s.toByteArray.data.toList`, never `String.toList`: on this toolchain `String.toList`
reaches `Classical.choice` and the bytes do not, and a hex digit is one ASCII byte, so the
bytes are the code points (`utf8Bytes_map_ofNat`).
-/

set_option autoImplicit false

namespace Effect4.Store

/-- A content address: thirty-two bytes, and the proof that there are thirty-two. The length is
carried in the type (Foldlab's `Addr32`) because the class laws need it: `Canonical Digest`
checks the length in `ofVal`, so `ofVal_toVal` and `fits` would be false for a shorter value
if one could be built. -/
structure Digest where
  bytes : Bytes
  length_eq : bytes.length = 32

theorem Digest.ext {a b : Digest} (h : a.bytes = b.bytes) : a = b := by
  cases a
  cases b
  cases h
  rfl

instance Digest.instDecidableEq : DecidableEq Digest := fun a b =>
  if h : a.bytes = b.bytes then isTrue (Digest.ext h)
  else isFalse fun e => h (congrArg Digest.bytes e)

instance Digest.instRepr : Repr Digest := ⟨fun d _ => repr d.bytes⟩

theorem sha256_bytes_length (bytes : Bytes) :
    (Hash.Sha256.sha256 bytes.toByteArray).toList.length = 32 := by
  simp [Hash.Sha256.Digest.toList, Hash.Sha256.sha256]
  exact Hash.Sha256.Fast.size_sha256 _

/-- SHA-256 of a byte string. -/
def sha256 (bytes : Bytes) : Digest :=
  ⟨(Hash.Sha256.sha256 bytes.toByteArray).toList, sha256_bytes_length bytes⟩

/-! ## Hexadecimal, on code points -/

/-- One hexadecimal digit as a code point, lowercase: `0`–`9` then `a`–`f`. -/
def hexDigit (n : Nat) : Nat := if n < 10 then 48 + n else 87 + n

/-- The value of a hexadecimal digit's code point, either case. -/
def hexVal (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55)
  else none

/-- An uppercase digit's code point lowered; every other code point kept. -/
def lowerHex (c : Nat) : Nat := if 65 ≤ c ∧ c ≤ 70 then c + 32 else c

/-- The lowercase hexadecimal digits of a byte string, as code points. -/
def hexCodes : Bytes → List Nat
  | [] => []
  | b :: bs => hexDigit (b.toNat / 16) :: hexDigit (b.toNat % 16) :: hexCodes bs

/-- The bytes a digit string spells, two digits per byte, either case. -/
def bytesOfHexCodes : List Nat → Option Bytes
  | [] => some []
  | c₁ :: c₂ :: rest =>
    match hexVal c₁, hexVal c₂, bytesOfHexCodes rest with
    | some h, some l, some bs => some (UInt8.ofNat (h * 16 + l) :: bs)
    | _, _, _ => none
  | [_] => none

theorem hexVal_hexDigit : ∀ n, n < 16 → hexVal (hexDigit n) = some n := by decide

theorem hexDigit_lt (n : Nat) (h : n < 16) : hexDigit n < 128 := by
  unfold hexDigit
  split <;> omega

/-- A code point with a digit value is that digit, up to case. -/
theorem hexVal_some {c n : Nat} (h : hexVal c = some n) : n < 16 ∧ lowerHex c = hexDigit n := by
  unfold hexVal at h
  by_cases h1 : 48 ≤ c ∧ c ≤ 57
  · rw [if_pos h1] at h
    injection h with h
    subst h
    refine ⟨by omega, ?_⟩
    unfold lowerHex hexDigit
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  · rw [if_neg h1] at h
    by_cases h2 : 97 ≤ c ∧ c ≤ 102
    · rw [if_pos h2] at h
      injection h with h
      subst h
      refine ⟨by omega, ?_⟩
      unfold lowerHex hexDigit
      rw [if_neg (by omega), if_neg (by omega)]
      omega
    · rw [if_neg h2] at h
      by_cases h3 : 65 ≤ c ∧ c ≤ 70
      · rw [if_pos h3] at h
        injection h with h
        subst h
        refine ⟨by omega, ?_⟩
        unfold lowerHex hexDigit
        rw [if_pos h3, if_neg (by omega)]
        omega
      · rw [if_neg h3] at h
        exact nomatch h

theorem hexCodes_lt (bs : Bytes) : ∀ n ∈ hexCodes bs, n < 128 := by
  induction bs with
  | nil => intro n hn; exact nomatch hn
  | cons b bs ih =>
    intro n hn
    have hb := UInt8.toNat_lt b
    simp only [hexCodes, List.mem_cons] at hn
    rcases hn with rfl | rfl | hn
    · exact hexDigit_lt _ (by omega)
    · exact hexDigit_lt _ (by omega)
    · exact ih n hn

theorem length_hexCodes (bs : Bytes) : (hexCodes bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [hexCodes, List.length_cons, ih]
    omega

/-- Round trip: the digits of a byte string read back as the byte string. -/
theorem bytesOfHexCodes_hexCodes (bs : Bytes) : bytesOfHexCodes (hexCodes bs) = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have hb := UInt8.toNat_lt b
    have hbyte : UInt8.ofNat (b.toNat / 16 * 16 + b.toNat % 16) = b := by
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_ofNat']
      omega
    simp only [hexCodes, bytesOfHexCodes, hexVal_hexDigit _ (by omega : b.toNat / 16 < 16),
      hexVal_hexDigit _ (by omega : b.toNat % 16 < 16), ih, hbyte]

/-- Exactness up to case: a digit string that decodes is, lowercased, the digits of what it
decodes to. -/
theorem hexCodes_of_bytesOfHexCodes : ∀ (cs : List Nat) (bs : Bytes),
    bytesOfHexCodes cs = some bs → hexCodes bs = cs.map lowerHex
  | [], bs, h => by
    injection h with h
    subst h
    rfl
  | [_], _, h => by
    simp only [bytesOfHexCodes] at h
    exact nomatch h
  | c₁ :: c₂ :: rest, bs, h => by
    simp only [bytesOfHexCodes] at h
    cases h₁ : hexVal c₁ with
    | none =>
      simp only [h₁] at h
      exact nomatch h
    | some hv =>
      cases h₂ : hexVal c₂ with
      | none =>
        simp only [h₁, h₂] at h
        exact nomatch h
      | some lv =>
        cases h₃ : bytesOfHexCodes rest with
        | none =>
          simp only [h₁, h₂, h₃] at h
          exact nomatch h
        | some tail =>
          simp only [h₁, h₂, h₃] at h
          injection h with h
          subst h
          obtain ⟨hlt₁, hc₁⟩ := hexVal_some h₁
          obtain ⟨hlt₂, hc₂⟩ := hexVal_some h₂
          have hrest := hexCodes_of_bytesOfHexCodes rest tail h₃
          have hhi : (UInt8.ofNat (hv * 16 + lv)).toNat / 16 = hv := by
            rw [UInt8.toNat_ofNat']
            omega
          have hlo : (UInt8.ofNat (hv * 16 + lv)).toNat % 16 = lv := by
            rw [UInt8.toNat_ofNat']
            omega
          simp only [hexCodes, List.map_cons, hhi, hlo, hc₁, hc₂, hrest]

/-! ## Characters and strings: the faces -/

/-- The lowercase hexadecimal spelling of a byte string, as characters. -/
def hexOfBytes (bs : Bytes) : List Char := (hexCodes bs).map Char.ofNat

/-- The bytes a character string spells in hexadecimal, either case. -/
def bytesOfHex (cs : List Char) : Option Bytes := bytesOfHexCodes (cs.map Char.toNat)

theorem map_toNat_map_ofNat_char (ns : List Nat) (h : ∀ n ∈ ns, n < 0xd800) :
    (ns.map Char.ofNat).map Char.toNat = ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨toNat_ofNat_valid n (Or.inl (h n (by simp))), ih fun m hm => h m (by simp [hm])⟩

theorem bytesOfHex_hexOfBytes (bs : Bytes) : bytesOfHex (hexOfBytes bs) = some bs := by
  unfold bytesOfHex hexOfBytes
  rw [map_toNat_map_ofNat_char _ fun n hn => Nat.lt_trans (hexCodes_lt bs n hn) (by decide)]
  exact bytesOfHexCodes_hexCodes bs

/-- What decodes, re-printed, is the input lowercased. -/
theorem hexOfBytes_bytesOfHex {cs : List Char} {bs : Bytes} (h : bytesOfHex cs = some bs) :
    hexOfBytes bs = cs.map fun c => Char.ofNat (lowerHex c.toNat) := by
  unfold hexOfBytes
  rw [hexCodes_of_bytesOfHexCodes _ _ h, List.map_map, List.map_map]
  rfl

/-- ASCII code points encode as themselves: the bridge from a string's bytes to its digits. -/
theorem utf8Bytes_map_ofNat (ns : List Nat) (h : ∀ n ∈ ns, n < 0x80) :
    utf8Bytes (ns.map Char.ofNat) = ns.map UInt8.ofNat := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    have hn : n < 0x80 := h n (by simp)
    have hvalid : n.isValidChar := Or.inl (by omega)
    rw [List.map_cons, utf8Bytes_cons, encodeChar_one _ (by rw [toNat_ofNat_valid n hvalid]; omega),
      toNat_ofNat_valid n hvalid, ih fun m hm => h m (by simp [hm])]
    rfl

theorem map_toNat_map_ofNat (ns : List Nat) (h : ∀ n ∈ ns, n < 256) :
    (ns.map UInt8.ofNat).map UInt8.toNat = ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨UInt8.toNat_ofNat_of_lt' (h n (by simp)), ih fun m hm => h m (by simp [hm])⟩

namespace Digest

/-- The lowercase hexadecimal spelling: the one printer (`Digest.lean:54-55`). -/
def hex (d : Digest) : String := String.ofList (hexOfBytes d.bytes)

/-- A digest from its hexadecimal spelling, either case, exactly thirty-two bytes. The string
is read through its UTF-8 bytes, which are the code points because every hex digit is ASCII. -/
def ofHex? (s : String) : Option Digest :=
  match bytesOfHexCodes (s.toByteArray.data.toList.map UInt8.toNat) with
  | some bs => if h : bs.length = 32 then some ⟨bs, h⟩ else none
  | none => none

/-- A digest names thirty-two bytes; for `sha256` that is `sha256_bytes_length`. -/
theorem sha256_length (bytes : Bytes) : (sha256 bytes).bytes.length = 32 :=
  (sha256 bytes).length_eq

/-- The digit bytes of a digest's spelling are its digits. -/
theorem hex_bytes (d : Digest) :
    d.hex.toByteArray.data.toList.map UInt8.toNat = hexCodes d.bytes := by
  unfold hex hexOfBytes
  rw [String.toByteArray_ofList, utf8Encode_data_toList,
    utf8Bytes_map_ofNat _ (hexCodes_lt d.bytes),
    map_toNat_map_ofNat _ fun n hn => Nat.lt_trans (hexCodes_lt d.bytes n hn) (by decide)]

/-- Round trip: a digest is recovered from its spelling. -/
theorem ofHex?_hex (d : Digest) : ofHex? d.hex = some d := by
  cases d with
  | mk bs hl =>
    unfold ofHex?
    rw [hex_bytes, bytesOfHexCodes_hexCodes]
    show (if h : bs.length = 32 then some (Digest.mk bs h) else none) = some (Digest.mk bs hl)
    rw [dif_pos hl]

/-- Exactness up to case: a string that reads as a digest is that digest's spelling with its
digits lowercased. -/
theorem ofHex?_exact {s : String} {d : Digest} (h : ofHex? s = some d) :
    hexCodes d.bytes = (s.toByteArray.data.toList.map UInt8.toNat).map lowerHex := by
  unfold ofHex? at h
  split at h
  · next bs hbs =>
    split at h
    · next hlen =>
      injection h with h
      subst h
      exact hexCodes_of_bytesOfHexCodes _ _ hbs
    · exact nomatch h
  · exact nomatch h

end Digest

/-! ## Receipts, guarded: the CAVP digests `Test/Store/StoreContract.lean:21-28` pin, the
hex codec both ways, and the facts note §6 payload digest of the census entry. -/

#guard (sha256 []).hex = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard (sha256 [0xb4, 0x19, 0x0e]).hex =
  "dff2e73091f6c05e528896c4c831b9448653dc2ff043528f6769437bc7b975c2"
#guard (sha256 []).bytes.length = 32
#guard bytesOfHex ['f', 'f', '0', '0'] = some [255, 0]
#guard bytesOfHex ['F', 'F', '0', 'a'] = some [255, 10]
#guard bytesOfHex ['g', '0'] = none
#guard bytesOfHex ['0'] = none
#guard hexOfBytes [255, 10] = ['f', 'f', '0', 'a']
#guard Digest.ofHex? (sha256 []).hex = some (sha256 [])
#guard Digest.ofHex? "E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855" = some (sha256 [])
#guard Digest.ofHex? "e3b0" = none
#guard Digest.ofHex? "" = none
#guard (sha256 (Val.encode sampleEntry)).hex =
  "8fab161870afe7d35c681679cf5dced52845b5ebef2b84b6c85e4b49d00661fa"

/-! ## A digest from bytes -/

/-- A digest from exactly thirty-two bytes; the one length check the codecs share. Moved here
from `Store/Node.lean` at the landing (2026-09-05) so a module that needs only a `Digest`
(`Surface/Annotate.lean`) never imports the node layer. -/
def Digest.ofBytes? (bs : Bytes) : Option Digest :=
  if h : bs.length = 32 then some ⟨bs, h⟩ else none

theorem Digest.ofBytes?_bytes (d : Digest) : Digest.ofBytes? d.bytes = some d := by
  cases d with
  | mk bs hl =>
    show (if h : bs.length = 32 then some (Digest.mk bs h) else none) = some (Digest.mk bs hl)
    rw [dif_pos hl]

theorem Digest.ofBytes?_exact {bs : Bytes} {d : Digest} (h : Digest.ofBytes? bs = some d) :
    d.bytes = bs := by
  unfold Digest.ofBytes? at h
  split at h
  · injection h with h
    subst h
    rfl
  · exact nomatch h

/-! ## Receipts -/

#print axioms Digest.ext
#print axioms Digest.instDecidableEq
#print axioms Digest.ofBytes?
#print axioms Digest.ofBytes?_bytes
#print axioms Digest.ofBytes?_exact
#print axioms sha256_bytes_length
#print axioms sha256
#print axioms hexDigit
#print axioms hexVal
#print axioms hexCodes
#print axioms bytesOfHexCodes
#print axioms hexVal_hexDigit
#print axioms hexVal_some
#print axioms hexCodes_lt
#print axioms length_hexCodes
#print axioms bytesOfHexCodes_hexCodes
#print axioms hexCodes_of_bytesOfHexCodes
#print axioms hexOfBytes
#print axioms bytesOfHex
#print axioms bytesOfHex_hexOfBytes
#print axioms hexOfBytes_bytesOfHex
#print axioms utf8Bytes_map_ofNat
#print axioms map_toNat_map_ofNat
#print axioms Digest.hex
#print axioms Digest.ofHex?
#print axioms Digest.sha256_length
#print axioms Digest.hex_bytes
#print axioms Digest.ofHex?_hex
#print axioms Digest.ofHex?_exact

end Effect4.Store
