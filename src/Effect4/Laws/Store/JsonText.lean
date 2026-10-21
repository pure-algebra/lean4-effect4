import Effect4.Store.Domain.JsonText
import Effect4.Laws.Store.ShapeRead
import Effect4.Laws.Data.NatDecimal
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Store.JsonText — the profile's text reads back what the profile writes

`Store/Domain/JsonText.lean` reads JSON text into the profile's tree (`NatJson.parse`). Its law is
the round trip of the compact text: within the profile, the text `NatJson.render` writes for a
tree reads back as that tree (`parse_render`).

The proof runs the reader's explicit stack over the text `renderTo` writes. A value written
before any rest that starts with a comma, a close or nothing is read, and put to its context
(`readText_renderTo`); a list's items and an object's entries likewise (`readText_renderItems`,
`readText_renderEntries`). A string reads back through its escapes and `Store.decodeString`
(`stringText_quoted`), and a natural through its decimal digits (`numberText_digits`).

## Placement

Concept `exact-codecs`; property: a read paired with a write is exact when whatever reads is the
write of what it reads, and the read retracts the write on its domain. Requirement R8 (runs and
faces as named connections, `docs/core/system-map.md` §8): the two session drivers read one text
by one grammar, inside the profile.

- **`json-text-round-trip`** (proposed claim, role compatibility; pointer `parse_render`). Reach:
  every profile tree within the profile (`NatJson.within`: every natural at most
  `safeBound`, no numeral), every string. Not established: exactness against rendering, that
  whatever reads is a rendering modulo white space and the spelling of escapes and numbers;
  anything of a host's text before its bytes (a line's UTF-8 from `IO.getLine`); the lowered
  OCaml, which decisions row 391 trusts. Consumers: Lean's session driver
  (`tools/Drivers/Session.lean`) and the native shell (`ocaml/engine/kit/kit.ml`), whose replies
  this grammar reads back.
-/

set_option autoImplicit false

namespace Effect4.NatJson

/-! ## The reader's steps

One equation per mode and byte, each read off `readText`'s definition. They are the steps of
`readText_renderTo` and its list and entry forms. -/

/-- At the end of the text, the reader answers the mode's end. A step of `parse_render`. -/
theorem readText_nil {bs : List Nat} {m : TextMode} (h : skipSpace bs = []) :
    readText bs m = endOf m := by
  rw [readText.eq_1]
  split
  · rfl
  · next c rest heq =>
    rw [h] at heq
    cases heq

/-- A value starts at its first byte. A step of `readText_renderTo`. -/
theorem readText_value {bs rest r : List Nat} {c : Nat} {ctx : TextCtx} {m' : TextMode}
    (h : skipSpace bs = c :: rest) (hv : startValue ctx c rest = .ok (m', r)) :
    readText bs (.value ctx) = readText r m' := by
  rw [readText.eq_1]
  split
  · next heq =>
    rw [h] at heq
    cases heq
  · next c' rest' heq =>
    rw [h] at heq
    cases heq
    dsimp only
    split
    · next m'' r'' hv' =>
      rw [hv] at hv'
      cases hv'
      rfl
    · next e hv' =>
      rw [hv] at hv'
      cases hv'

/-- A value starts at its first byte, whatever the start answers. A step of
`readText_firstItem`. -/
theorem readText_value_eq {bs rest : List Nat} {c : Nat} {ctx : TextCtx}
    (h : skipSpace bs = c :: rest) :
    readText bs (.value ctx) =
      match startValue ctx c rest with
      | .ok (m', r) => readText r m'
      | .error e => .error e := by
  rw [readText.eq_1]
  split
  · next heq =>
    rw [h] at heq
    cases heq
  · next c' rest' heq =>
    rw [h] at heq
    cases heq
    dsimp only
    split
    · next m'' r'' hv' => rw [hv']
    · next e hv' => rw [hv']

/-- After `[`, a byte that closes nothing starts the first item, as a value would. A step of
`readText_renderTo`. -/
theorem readText_firstItem {bs rest : List Nat} {c : Nat} {ctx : TextCtx}
    (h : skipSpace bs = c :: rest) (hc : c ≠ 93) :
    readText bs (.firstItem ctx) = readText bs (.value (.item [] ctx)) := by
  rw [readText_value_eq h, readText.eq_1]
  split
  · next heq =>
    rw [h] at heq
    cases heq
  · next c' rest' heq =>
    rw [h] at heq
    cases heq
    dsimp only
    rw [if_neg hc]
    split
    · next m'' r'' hv' => rw [hv']
    · next e hv' => rw [hv']

/-- After `[`, a `]` closes the empty array. A step of `readText_renderTo`. -/
theorem readText_firstItem_close {bs rest : List Nat} {ctx : TextCtx}
    (h : skipSpace bs = 93 :: rest) :
    readText bs (.firstItem ctx) = readText rest (ctx.put (.arr [])) := by
  rw [readText.eq_1]
  split
  · next heq =>
    rw [h] at heq
    cases heq
  · next c' rest' heq =>
    rw [h] at heq
    cases heq
    rfl

/-- After `{`, a `}` closes the empty object. A step of `readText_renderTo`. -/
theorem readText_firstKey_close {bs rest : List Nat} {ctx : TextCtx}
    (h : skipSpace bs = 125 :: rest) :
    readText bs (.firstKey ctx) = readText rest (ctx.put (.obj [])) := by
  rw [readText.eq_1]
  split
  · next heq =>
    rw [h] at heq
    cases heq
  · next c' rest' heq =>
    rw [h] at heq
    cases heq
    rfl

/-- After `{`, a key read waits for its colon. A step of `readText_renderTo`. -/
theorem readText_firstKey_key {bs rest r : List Nat} {ctx : TextCtx} {k : String}
    (h : skipSpace bs = 34 :: rest) (hk : stringText rest = .ok (k, r)) :
    readText bs (.firstKey ctx) = readText r (.colon [] k ctx) := by
  rw [readText.eq_1]
  split
  · next heq =>
    rw [h] at heq
    cases heq
  · next c' rest' heq =>
    rw [h] at heq
    cases heq
    dsimp only
    rw [if_neg (by decide), if_pos rfl]
    split
    · next k' r' hk' =>
      rw [hk] at hk'
      cases hk'
      rfl
    · next e hk' =>
      rw [hk] at hk'
      cases hk'

/-- After a comma in an object, a key read waits for its colon. A step of
`readText_renderEntries`. -/
theorem readText_key {bs rest r : List Nat} {entries : List (String × NatJson)} {ctx : TextCtx}
    {k : String} (h : skipSpace bs = 34 :: rest) (hk : stringText rest = .ok (k, r)) :
    readText bs (.key entries ctx) = readText r (.colon entries k ctx) := by
  rw [readText.eq_1]
  split
  · next heq =>
    rw [h] at heq
    cases heq
  · next c' rest' heq =>
    rw [h] at heq
    cases heq
    dsimp only
    rw [if_pos rfl]
    split
    · next k' r' hk' =>
      rw [hk] at hk'
      cases hk'
      rfl
    · next e hk' =>
      rw [hk] at hk'
      cases hk'

/-- A colon after a key starts its value. A step of `readText_renderTo`. -/
theorem readText_colon {bs rest : List Nat} {entries : List (String × NatJson)} {k : String}
    {ctx : TextCtx} (h : skipSpace bs = 58 :: rest) :
    readText bs (.colon entries k ctx) = readText rest (.value (.member entries k ctx)) := by
  rw [readText.eq_1]
  split
  · next heq =>
    rw [h] at heq
    cases heq
  · next c' rest' heq =>
    rw [h] at heq
    cases heq
    rfl

/-- A comma after an item starts the next one. A step of `readText_renderItems`. -/
theorem readText_afterItem_comma {bs rest : List Nat} {items : List NatJson} {ctx : TextCtx}
    (h : skipSpace bs = 44 :: rest) :
    readText bs (.afterItem items ctx) = readText rest (.value (.item items ctx)) := by
  rw [readText.eq_1]
  split
  · next heq =>
    rw [h] at heq
    cases heq
  · next c' rest' heq =>
    rw [h] at heq
    cases heq
    rfl

/-- A `]` after an item closes the array, its items in order. A step of `readText_renderItems`. -/
theorem readText_afterItem_close {bs rest : List Nat} {items : List NatJson} {ctx : TextCtx}
    (h : skipSpace bs = 93 :: rest) :
    readText bs (.afterItem items ctx) = readText rest (ctx.put (.arr items.reverse)) := by
  rw [readText.eq_1]
  split
  · next heq =>
    rw [h] at heq
    cases heq
  · next c' rest' heq =>
    rw [h] at heq
    cases heq
    rfl

/-- A comma after a member waits for the next key. A step of `readText_renderEntries`. -/
theorem readText_afterMember_comma {bs rest : List Nat} {entries : List (String × NatJson)}
    {ctx : TextCtx} (h : skipSpace bs = 44 :: rest) :
    readText bs (.afterMember entries ctx) = readText rest (.key entries ctx) := by
  rw [readText.eq_1]
  split
  · next heq =>
    rw [h] at heq
    cases heq
  · next c' rest' heq =>
    rw [h] at heq
    cases heq
    rfl

/-- A `}` after a member closes the object, its entries in order. A step of
`readText_renderEntries`. -/
theorem readText_afterMember_close {bs rest : List Nat} {entries : List (String × NatJson)}
    {ctx : TextCtx} (h : skipSpace bs = 125 :: rest) :
    readText bs (.afterMember entries ctx) = readText rest (ctx.put (.obj entries.reverse)) := by
  rw [readText.eq_1]
  split
  · next heq =>
    rw [h] at heq
    cases heq
  · next c' rest' heq =>
    rw [h] at heq
    cases heq
    rfl

/-! ## Strings

`NatJson.render` writes a string's UTF-8 bytes between quotes, each byte as itself or as its
escape (`escapeByte`). The reader takes each escape back to its byte (`stringBytes_escapeByte`),
and `Store.decodeString` takes the bytes back to the string (`Store.decodeString_toUTF8`). -/

/-- A lowercase hexadecimal digit reads as its value. A step of `stringBytes_escapeByte`. -/
theorem hexValue_hexDigit {d : Nat} (hd : d < 16) : hexValue (hexDigit d) = some d := by
  unfold hexValue hexDigit
  split
  · rename_i h10
    rw [if_pos ⟨by omega, by omega⟩]
    congr 1
    omega
  · rename_i h10
    rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
    congr 1
    omega

/-- **Each byte reads back from its escape**: what `escapeByte` writes for a byte, the reader
takes as that byte. A step of `stringBytes_escapeTo`. -/
theorem stringBytes_escapeByte {c : Nat} (more acc : List Nat) :
    stringBytes (escapeByte c ++ more) acc = stringBytes more (c :: acc) := by
  unfold escapeByte
  split
  · next h34 =>
    subst h34
    rw [List.cons_append, List.cons_append, List.nil_append, stringBytes.eq_def]
    simp only [↓reduceIte, Nat.reduceEqDiff]
  · split
    · next h92 =>
      subst h92
      rw [List.cons_append, List.cons_append, List.nil_append, stringBytes.eq_def]
      simp only [↓reduceIte, Nat.reduceEqDiff]
    · split
      · next h10 =>
        subst h10
        rw [List.cons_append, List.cons_append, List.nil_append, stringBytes.eq_def]
        simp only [↓reduceIte, Nat.reduceEqDiff]
      · split
        · next h13 =>
          subst h13
          rw [List.cons_append, List.cons_append, List.nil_append, stringBytes.eq_def]
          simp only [↓reduceIte, Nat.reduceEqDiff]
        · split
          · next h9 =>
            subst h9
            rw [List.cons_append, List.cons_append, List.nil_append, stringBytes.eq_def]
            simp only [↓reduceIte, Nat.reduceEqDiff]
          · split
            · next h8 =>
              subst h8
              rw [List.cons_append, List.cons_append, List.nil_append, stringBytes.eq_def]
              simp only [↓reduceIte, Nat.reduceEqDiff]
            · split
              · next h12 =>
                subst h12
                rw [List.cons_append, List.cons_append, List.nil_append, stringBytes.eq_def]
                simp only [↓reduceIte, Nat.reduceEqDiff]
              · split
                · next h34 h92 h10 h13 h9 h8 h12 h32 =>
                  have hhex : hex4 48 48 (hexDigit (c / 16)) (hexDigit (c % 16)) = some c := by
                    unfold hex4
                    rw [hexValue_hexDigit (by omega), hexValue_hexDigit (by omega)]
                    have h48 : hexValue 48 = some 0 := rfl
                    rw [h48]
                    dsimp only
                    congr 1
                    omega
                  have hutf : utf8Of c = [c] := by
                    unfold utf8Of
                    rw [if_pos (by omega)]
                  simp only [List.cons_append, List.nil_append]
                  rw [stringBytes.eq_def]
                  simp only [↓reduceIte, Nat.reduceEqDiff, hhex]
                  rw [if_neg (by omega), if_neg (by omega), hutf, List.reverse_singleton,
                    List.singleton_append]
                · next h34 h92 h10 h13 h9 h8 h12 h32 =>
                  rw [List.singleton_append, stringBytes.eq_def]
                  simp only [h34, h92, h32, ↓reduceIte]

/-- **A string's content reads back from its escaped text**, up to the closing quote. A step of
`stringText_quoted`. -/
theorem stringBytes_escapeTo (rest : List Nat) :
    ∀ (cs acc : List Nat),
      stringBytes (escapeTo cs (34 :: rest)) acc = .ok (acc.reverse ++ cs, rest)
  | [], acc => by
    rw [escapeTo, stringBytes.eq_def]
    simp only [↓reduceIte, List.append_nil]
  | c :: cs, acc => by
    rw [escapeTo, stringBytes_escapeByte, stringBytes_escapeTo rest cs (c :: acc)]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

/-- **A string reads back from the text `render` writes for it.** A step of `parse_render`. -/
theorem stringText_quoted (s : String) (rest : List Nat) :
    stringText (escapeTo (codes s) (34 :: rest)) = .ok (s, rest) := by
  unfold stringText
  rw [stringBytes_escapeTo rest (codes s) []]
  have hbytes : ([].reverse ++ codes s).map UInt8.ofNat = s.toUTF8.data.toList := by
    simp only [List.reverse_nil, List.nil_append, codes, Data.Ascii.bytesOf, List.map_map]
    have hid : (UInt8.ofNat ∘ fun b : UInt8 => b.toNat) = id := by
      funext b
      exact UInt8.ofNat_toNat
    rw [hid, List.map_id]
  dsimp only
  rw [hbytes, Store.decodeString_toUTF8]

/-! ## Naturals

`NatJson.render` writes a natural as `Nat.repr` spells it: its decimal digits, the first no `0`
unless the natural is 0 (`toDigitsCore_head`), and at most `maxDigits` of them within the profile
(`toDigitsCore_length`). The reader reads them back as the natural (`numberText_repr`,
`numberOf_repr`), given what follows starts no number (`delimited`). -/

/-- A digit's character is the byte of its digit. A step of `codes_repr`. -/
theorem digitChar_toNat : ∀ m, m < 10 → (Nat.digitChar m).toNat = 48 + m := by decide

/-- Every character `toDigitsCore` adds is a digit's. A step of `codes_repr`. -/
theorem toDigitsCore_mem (fuel : Nat) : ∀ (n : Nat) (ds : List Char), n < fuel →
    ∀ ch ∈ Nat.toDigitsCore 10 fuel n ds, ch ∈ ds ∨ ∃ m, m < 10 ∧ ch = Nat.digitChar m := by
  induction fuel with
  | zero =>
    intro n _ h
    exact absurd h (Nat.not_lt_zero n)
  | succ fuel ih =>
    intro n ds hn ch hch
    simp only [Nat.toDigitsCore] at hch
    split at hch
    · rcases List.mem_cons.mp hch with h | h
      · exact .inr ⟨n % 10, Nat.mod_lt _ (by decide), h⟩
      · exact .inl h
    · rcases ih (n / 10) _ (by omega) ch hch with h | h
      · rcases List.mem_cons.mp h with h | h
        · exact .inr ⟨n % 10, Nat.mod_lt _ (by decide), h⟩
        · exact .inl h
      · exact .inr h

/-- A positive natural's first digit is no `0`. A step of `repr_head`. -/
theorem toDigitsCore_head (fuel : Nat) : ∀ (n : Nat) (ds : List Char), n < fuel → 0 < n →
    ∃ m tl, 0 < m ∧ m < 10 ∧ Nat.toDigitsCore 10 fuel n ds = Nat.digitChar m :: tl := by
  induction fuel with
  | zero =>
    intro n _ h
    exact absurd h (Nat.not_lt_zero n)
  | succ fuel ih =>
    intro n ds hn hpos
    simp only [Nat.toDigitsCore]
    split
    · next h0 => exact ⟨n % 10, ds, by omega, Nat.mod_lt _ (by decide), rfl⟩
    · next h0 => exact ih (n / 10) _ (by omega) (by omega)

/-- A natural below `10 ^ (k + 1)` has at most `k + 1` digits. A step of `repr_length`. -/
theorem toDigitsCore_length (fuel : Nat) : ∀ (n k : Nat) (ds : List Char), n < fuel →
    n < 10 ^ (k + 1) → (Nat.toDigitsCore 10 fuel n ds).length ≤ k + 1 + ds.length := by
  induction fuel with
  | zero =>
    intro n _ _ h
    exact absurd h (Nat.not_lt_zero n)
  | succ fuel ih =>
    intro n k ds hn hk
    simp only [Nat.toDigitsCore]
    split
    · simp only [List.length_cons]
      omega
    · next h0 =>
      cases k with
      | zero =>
        rw [Nat.pow_one] at hk
        omega
      | succ k =>
        rw [Nat.pow_succ] at hk
        have := ih (n / 10) k (Nat.digitChar (n % 10) :: ds) (by omega) (by omega)
        simp only [List.length_cons] at this
        omega

/-- **A natural's text as numbers** is its digit characters' codes. A step of `numberText_repr`. -/
theorem codes_repr (n : Nat) :
    codes (Nat.repr n) = (Nat.toDigitsCore 10 (n + 1) n []).map Char.toNat := by
  have hbytes : Data.Ascii.bytesOf (Nat.repr n) =
      (Nat.toDigitsCore 10 (n + 1) n []).flatMap String.utf8EncodeChar := by
    unfold Data.Ascii.bytesOf
    rw [String.toUTF8_eq_toByteArray, Nat.repr, String.toByteArray_ofList, List.utf8Encode,
      List.toList_data_toByteArray, Nat.toDigits]
  unfold codes
  rw [hbytes]
  have hall := toDigitsCore_mem (n + 1) n [] (Nat.lt_succ_self n)
  generalize Nat.toDigitsCore 10 (n + 1) n [] = L at hall ⊢
  induction L with
  | nil => rfl
  | cons ch L ih =>
    obtain ⟨m, hm, rfl⟩ := (hall ch List.mem_cons_self).resolve_left List.not_mem_nil
    rw [List.flatMap_cons, List.map_append, Data.NatDecimal.utf8_digitChar m hm,
      ih (fun c hc => hall c (List.mem_cons_of_mem _ hc)), List.map_cons, List.map_cons,
      List.map_nil, List.singleton_append, digitChar_toNat m hm,
      UInt8.toNat_ofNat_of_lt' (by show 48 + m < 256; omega)]

/-- Every byte of a natural's text is a digit. A step of `numberText_repr`. -/
theorem repr_digits (n : Nat) : ∀ c ∈ codes (Nat.repr n), isDigit c = true := by
  intro c hc
  rw [codes_repr] at hc
  obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hc
  obtain ⟨m, hm, rfl⟩ :=
    (toDigitsCore_mem (n + 1) n [] (Nat.lt_succ_self n) ch hch).resolve_left List.not_mem_nil
  rw [digitChar_toNat m hm]
  unfold isDigit
  rw [decide_eq_true (by omega : 48 ≤ 48 + m), decide_eq_true (by omega : 48 + m ≤ 57)]
  rfl

/-- **A natural's text spells it.** A step of `numberOf_repr`. -/
theorem repr_value (n : Nat) : digitsValue (codes (Nat.repr n)) = n := by
  unfold digitsValue codes
  rw [List.foldl_map]
  exact Data.NatDecimal.decodeBytes_repr n

/-- Within the profile, a natural's text has at most `maxDigits` digits. A step of
`numberOf_repr`. -/
theorem repr_length {n : Nat} (h : n ≤ safeBound) : (codes (Nat.repr n)).length ≤ maxDigits := by
  rw [codes_repr, List.length_map]
  have := toDigitsCore_length (n + 1) n 15 [] (Nat.lt_succ_self n)
    (by unfold safeBound at h; omega)
  simp only [List.length_nil] at this
  unfold maxDigits
  omega

/-- A natural's text is `0` alone, or starts with a digit from 1 to 9. A step of
`numberText_repr`. -/
theorem repr_head (n : Nat) :
    codes (Nat.repr n) = [48] ∨ ∃ d ds, codes (Nat.repr n) = d :: ds ∧ 49 ≤ d ∧ d ≤ 57 := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    exact .inl rfl
  · right
    obtain ⟨m, tl, hm0, hm, heq⟩ := toDigitsCore_head (n + 1) n [] (Nat.lt_succ_self n) hpos
    rw [codes_repr, heq, List.map_cons, digitChar_toNat m hm]
    exact ⟨48 + m, _, rfl, by omega, by omega⟩

/-- **What may follow a value the text writes**: nothing, a comma, or the close of an array or an
object. No number continues into it. -/
def delimited : List Nat → Bool
  | [] => true
  | c :: _ => c == 44 || c == 93 || c == 125

/-- No digit starts what follows a value. A step of `numberText_repr`. -/
theorem spanDigits_delimited {rest : List Nat} (hr : delimited rest = true) :
    spanDigits rest = ([], rest) := by
  cases rest with
  | nil => rfl
  | cons c tl =>
    unfold delimited at hr
    rw [spanDigits, if_neg]
    unfold isDigit
    simp only [Bool.or_eq_true, beq_iff_eq] at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega

/-- No exponent starts what follows a value. A step of `numberText_repr`. -/
theorem exponentPart_delimited {rest : List Nat} (hr : delimited rest = true) :
    exponentPart rest = .ok ([], rest) := by
  cases rest with
  | nil => rfl
  | cons c tl =>
    unfold delimited at hr
    simp only [Bool.or_eq_true, beq_iff_eq] at hr
    rw [exponentPart.eq_def]
    dsimp only
    rw [if_neg (by omega)]

/-- No fraction starts what follows a value. A step of `numberText_repr`. -/
theorem fractionPart_delimited {rest : List Nat} (hr : delimited rest = true) :
    fractionPart rest = .ok ([], rest) := by
  unfold fractionPart
  split
  · next rest' =>
    unfold delimited at hr
    simp only [Bool.or_eq_true, beq_iff_eq, Nat.reduceEqDiff, or_self] at hr
  · exact exponentPart_delimited hr

/-- Digits before what follows a value span to it. A step of `numberText_repr`. -/
theorem spanDigits_append {rest : List Nat} (hr : delimited rest = true) :
    ∀ ds : List Nat, (∀ c ∈ ds, isDigit c = true) → spanDigits (ds ++ rest) = (ds, rest)
  | [], _ => spanDigits_delimited hr
  | d :: ds, h => by
    rw [List.cons_append, spanDigits, if_pos (h d List.mem_cons_self),
      spanDigits_append hr ds (fun c hc => h c (List.mem_cons_of_mem d hc))]

/-- **A natural's text reads as a number's text**, up to what follows it. A step of
`startValue_nat`. -/
theorem numberText_repr (n : Nat) {rest : List Nat} (hr : delimited rest = true) :
    numberText (codes (Nat.repr n) ++ rest) = .ok (codes (Nat.repr n), rest) := by
  rcases repr_head n with h0 | ⟨d, ds, hds, hd1, hd2⟩
  · rw [h0, List.singleton_append]
    unfold numberText unsignedText
    simp only
    cases rest with
    | nil => rfl
    | cons c tl =>
      unfold delimited at hr
      simp only [Bool.or_eq_true, beq_iff_eq] at hr
      have hc : isDigit c = false := by
        rcases hr with (rfl | rfl) | rfl <;> rfl
      dsimp only
      rw [if_neg (by rw [hc]; exact Bool.false_ne_true), fractionPart_delimited (by
        unfold delimited
        simp only [Bool.or_eq_true, beq_iff_eq]
        exact hr)]
      rfl
  · have hall := repr_digits n
    rw [hds] at hall ⊢
    rw [List.cons_append]
    unfold numberText
    split
    · next tl heq =>
      cases heq
      exact absurd hd1 (by decide)
    · unfold unsignedText
      split
      · next tl heq =>
        cases heq
        exact absurd hd1 (by decide)
      · rw [digits1, ← List.cons_append, spanDigits_append hr (d :: ds) hall]
        simp only [Except.bind, fractionPart_delimited hr, Except.map, List.append_nil]

/-- **Within the profile, a natural's text is the natural.** A step of `startValue_nat`. -/
theorem numberOf_repr {n : Nat} (h : n ≤ safeBound) : numberOf (codes (Nat.repr n)) = .nat n := by
  unfold numberOf
  have hall : (codes (Nat.repr n)).all isDigit = true := List.all_eq_true.mpr (repr_digits n)
  rw [hall, Bool.true_and, decide_eq_true (repr_length h), if_pos rfl, repr_value]

/-! ## Values

Each scalar's text starts a value that is read whole and put to its context; an array or an
object opens its container. With the reader's steps, the round trip follows by one induction on
the tree, its lists and its entries. -/

/-- White space skips no byte a value starts with. A step of `readText_renderTo`. -/
theorem skipSpace_cons {c : Nat} {rest : List Nat} (hc : isSpace c = false) :
    skipSpace (c :: rest) = c :: rest := by
  rw [skipSpace, if_neg (by rw [hc]; exact Bool.false_ne_true)]

/-- `null` starts a value read whole. A step of `readText_renderTo`. -/
theorem startValue_null (ctx : TextCtx) (r : List Nat) :
    startValue ctx 110 (117 :: 108 :: 108 :: r) = .ok (ctx.put .null, r) := rfl

/-- `true` starts a value read whole. A step of `readText_renderTo`. -/
theorem startValue_true (ctx : TextCtx) (r : List Nat) :
    startValue ctx 116 (114 :: 117 :: 101 :: r) = .ok (ctx.put (.bool true), r) := rfl

/-- `false` starts a value read whole. A step of `readText_renderTo`. -/
theorem startValue_false (ctx : TextCtx) (r : List Nat) :
    startValue ctx 102 (97 :: 108 :: 115 :: 101 :: r) = .ok (ctx.put (.bool false), r) := rfl

/-- A string's text starts a value read whole. A step of `readText_renderTo`. -/
theorem startValue_str (ctx : TextCtx) (s : String) (r : List Nat) :
    startValue ctx 34 (escapeTo (codes s) (34 :: r)) = .ok (ctx.put (.str s), r) := by
  unfold startValue
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl, stringText_quoted]
  rfl

/-- Within the profile, a natural's text starts a value read whole, up to what follows it. A step
of `readText_renderTo`. -/
theorem startValue_nat {n : Nat} {d : Nat} {ds rest : List Nat} (ctx : TextCtx)
    (hn : n ≤ safeBound) (hr : delimited rest = true) (hds : codes (Nat.repr n) = d :: ds) :
    startValue ctx d (ds ++ rest) = .ok (ctx.put (.nat n), rest) := by
  have hd : isDigit d = true := repr_digits n d (by rw [hds]; exact List.mem_cons_self)
  have hd' : 48 ≤ d ∧ d ≤ 57 := by
    unfold isDigit at hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
    exact hd
  unfold startValue
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos (.inr hd), ← List.cons_append, ← hds,
    numberText_repr n hr]
  simp only [Except.map, numberOf_repr hn]

/-- A natural's text starts with no white space. A step of `readText_renderTo`. -/
theorem repr_first {n : Nat} {d : Nat} {ds : List Nat} (hds : codes (Nat.repr n) = d :: ds) :
    isSpace d = false ∧ d ≠ 93 ∧ d ≠ 125 := by
  have hd : isDigit d = true := repr_digits n d (by rw [hds]; exact List.mem_cons_self)
  unfold isDigit at hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
  refine ⟨?_, by omega, by omega⟩
  unfold isSpace
  rw [beq_false_of_ne (by omega : d ≠ 32), beq_false_of_ne (by omega : d ≠ 9),
    beq_false_of_ne (by omega : d ≠ 10), beq_false_of_ne (by omega : d ≠ 13)]
  rfl

/-- What follows a list's items is a comma or the close. A step of `readText_renderTo`. -/
theorem delimited_renderItems (rest : List Nat) :
    ∀ ts : List NatJson, delimited (renderItems ts (93 :: rest)) = true
  | [] => rfl
  | _ :: _ => rfl

/-- What follows an object's entries is a comma or the close. A step of `readText_renderTo`. -/
theorem delimited_renderEntries (rest : List Nat) :
    ∀ es : List (String × NatJson), delimited (renderEntries es (125 :: rest)) = true
  | [] => rfl
  | _ :: _ => rfl

/-- A value's text starts with no `]`. A step of `readText_renderTo`, where `[` opens an array. -/
theorem renderTo_first {t : NatJson} (ht : t.within = true) (rest : List Nat) :
    ∃ c tl, renderTo t rest = c :: tl ∧ isSpace c = false ∧ c ≠ 93 := by
  cases t with
  | null => exact ⟨110, _, rfl, rfl, by decide⟩
  | bool b =>
    cases b with
    | true => exact ⟨116, _, rfl, rfl, by decide⟩
    | false => exact ⟨102, _, rfl, rfl, by decide⟩
  | nat n =>
    rcases repr_head n with h0 | ⟨d, ds, hds, -, -⟩
    · refine ⟨48, rest, ?_, rfl, by decide⟩
      simp only [renderTo, h0, List.singleton_append]
    · obtain ⟨hs, h93, -⟩ := repr_first hds
      exact ⟨d, ds ++ rest, by simp only [renderTo, hds, List.cons_append], hs, h93⟩
  | numeral text => simp only [NatJson.within, Bool.false_eq_true] at ht
  | str s => exact ⟨34, _, rfl, rfl, by decide⟩
  | arr ts =>
    cases ts with
    | nil => exact ⟨91, _, rfl, rfl, by decide⟩
    | cons _ _ => exact ⟨91, _, rfl, rfl, by decide⟩
  | obj es =>
    cases es with
    | nil => exact ⟨123, _, rfl, rfl, by decide⟩
    | cons _ _ => exact ⟨123, _, rfl, rfl, by decide⟩

/-- A natural's text has a first byte. A step of `readText_renderTo`. -/
theorem repr_cons (n : Nat) : ∃ d ds, codes (Nat.repr n) = d :: ds := by
  rcases repr_head n with h0 | ⟨d, ds, hds, -, -⟩
  · exact ⟨48, [], h0⟩
  · exact ⟨d, ds, hds⟩

mutual
/-- **A value's text reads as the value**, put to its context, when what follows it starts no
number. The step of `parse_render`. -/
theorem readText_renderTo : ∀ {t : NatJson} {rest : List Nat} {ctx : TextCtx},
    t.within = true → delimited rest = true →
      readText (renderTo t rest) (.value ctx) = readText rest (ctx.put t)
  | .null, rest, ctx, _, _ =>
    readText_value (skipSpace_cons rfl) (startValue_null ctx rest)
  | .bool true, rest, ctx, _, _ => by
    simp only [renderTo, ↓reduceIte, List.cons_append, List.nil_append]
    exact readText_value (skipSpace_cons rfl) (startValue_true ctx rest)
  | .bool false, rest, ctx, _, _ => by
    simp only [renderTo, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
    exact readText_value (skipSpace_cons rfl) (startValue_false ctx rest)
  | .nat n, rest, ctx, ht, hr => by
    simp only [NatJson.within, decide_eq_true_eq] at ht
    obtain ⟨d, ds, hds⟩ := repr_cons n
    rw [renderTo, hds, List.cons_append]
    exact readText_value (skipSpace_cons (repr_first hds).1) (startValue_nat ctx ht hr hds)
  | .numeral _, _, _, ht, _ => by simp only [NatJson.within, Bool.false_eq_true] at ht
  | .str s, rest, ctx, _, _ => by
    rw [renderTo, quotedTo]
    exact readText_value (skipSpace_cons rfl) (startValue_str ctx s rest)
  | .arr [], rest, ctx, _, _ => by
    rw [renderTo, readText_value (skipSpace_cons rfl) rfl]
    exact readText_firstItem_close (skipSpace_cons rfl)
  | .arr (t :: ts), rest, ctx, ht, _ => by
    simp only [NatJson.within, NatJson.withinList, Bool.and_eq_true] at ht
    rw [renderTo, readText_value (skipSpace_cons rfl) rfl]
    obtain ⟨c, tl, heq, hs, h93⟩ := renderTo_first ht.1 (renderItems ts (93 :: rest))
    have hsk : skipSpace (renderTo t (renderItems ts (93 :: rest))) = c :: tl := by
      rw [heq]
      exact skipSpace_cons hs
    rw [readText_firstItem hsk h93,
      readText_renderTo ht.1 (delimited_renderItems rest ts)]
    exact readText_renderItems ht.2
  | .obj [], rest, ctx, _, _ => by
    rw [renderTo, readText_value (skipSpace_cons rfl) rfl]
    exact readText_firstKey_close (skipSpace_cons rfl)
  | .obj ((k, t) :: es), rest, ctx, ht, _ => by
    simp only [NatJson.within, NatJson.withinEntries, Bool.and_eq_true] at ht
    rw [renderTo, readText_value (skipSpace_cons rfl) rfl, quotedTo,
      readText_firstKey_key (skipSpace_cons rfl) (stringText_quoted k _),
      readText_colon (skipSpace_cons rfl),
      readText_renderTo ht.1 (delimited_renderEntries rest es)]
    exact readText_renderEntries ht.2

/-- **A list's items read as the list**, closed by `]`. A step of `readText_renderTo`. -/
theorem readText_renderItems : ∀ {ts : List NatJson} {rest : List Nat} {items : List NatJson}
    {ctx : TextCtx}, NatJson.withinList ts = true →
      readText (renderItems ts (93 :: rest)) (.afterItem items ctx) =
        readText rest (ctx.put (.arr (items.reverse ++ ts)))
  | [], rest, items, ctx, _ => by
    rw [renderItems, readText_afterItem_close (skipSpace_cons rfl), List.append_nil]
  | t :: ts, rest, items, ctx, h => by
    simp only [NatJson.withinList, Bool.and_eq_true] at h
    rw [renderItems, readText_afterItem_comma (skipSpace_cons rfl),
      readText_renderTo h.1 (delimited_renderItems rest ts)]
    rw [show (TextCtx.item items ctx).put t = .afterItem (t :: items) ctx from rfl,
      readText_renderItems h.2]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- **An object's entries read as the object**, closed by `}`. A step of `readText_renderTo`. -/
theorem readText_renderEntries : ∀ {es : List (String × NatJson)} {rest : List Nat}
    {entries : List (String × NatJson)} {ctx : TextCtx}, NatJson.withinEntries es = true →
      readText (renderEntries es (125 :: rest)) (.afterMember entries ctx) =
        readText rest (ctx.put (.obj (entries.reverse ++ es)))
  | [], rest, entries, ctx, _ => by
    rw [renderEntries, readText_afterMember_close (skipSpace_cons rfl), List.append_nil]
  | (k, t) :: es, rest, entries, ctx, h => by
    simp only [NatJson.withinEntries, Bool.and_eq_true] at h
    rw [renderEntries, readText_afterMember_comma (skipSpace_cons rfl), quotedTo,
      readText_key (skipSpace_cons rfl) (stringText_quoted k _),
      readText_colon (skipSpace_cons rfl),
      readText_renderTo h.1 (delimited_renderEntries rest es)]
    rw [show (TextCtx.member entries k ctx).put t = .afterMember ((k, t) :: entries) ctx from rfl,
      readText_renderEntries h.2]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
end

/-- **Within the profile, the text `render` writes reads back as the tree.** The pointer of the
proposed claim `json-text-round-trip`: the one grammar both session drivers read with retracts
the printer both write with, on every tree within the profile. -/
@[semantics "exact-codecs" (requirement := R8)]
theorem parse_render {t : NatJson} (h : t.within = true) : parse (render t) = .ok t := by
  unfold parse render
  rw [readText_renderTo h rfl, readText_nil rfl]
  rfl

end Effect4.NatJson
