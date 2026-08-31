/-!
# The decimal spelling, inverted

The number half of the canonical rendering's parser, and with it the
lemma the schema plane has been waiting on: `Nat.repr` is injective.

The route is the one `Cas.Values.JsonInj` takes for the escape alphabet
— invert the code rather than reason about it. Here the inverse is READ
OFF THE TOOLCHAIN: Lean 4.33's `Init.Data.Nat.ToString` ships
`Nat.ofDigitChars` together with `Nat.ofDigitChars_ten_toDigits`
(`ofDigitChars 10 (toDigits 10 n) 0 = n`), so the left inverse already
exists and `natRepr_inj` is three lines on top of it. (The 2026-08-29
survey's "the toolchain ships no injectivity lemma for `Nat.repr`" is
still true of the LEMMA; what it did not know is that the INVERSE is
shipped, which was the part that cost.)

What this module adds beyond that lemma is the parser component:

- `digitValue` — one decimal digit read back, the `hexValue` idiom;
- `takeDigits` — the greedy digit run, with the two laws the parser
  needs: it is exact on a digit block followed by a non-digit
  (`takeDigits_append`), and its answer always reassembles the input
  (`takeDigits_sound`);
- `parseNat` — the STRICT canonical natural: a nonempty digit run with
  no leading zero unless the whole spelling is `"0"`, which is exactly
  `Nat.repr`'s image (`canonDigits_toDigits`);
- `parseNat_toDigits` (adequacy, under the follow-set premise
  `NoDigitStart`) and `parseNat_sound` (exactness — whatever `parseNat`
  answers re-renders to the characters it consumed), the two halves
  the grammar's parser lifts.

## The follow set, named

`Nat.repr` is NOT prefix-free — `"1"` prefixes `"12"` — so the greedy
run agrees with the spelling only when the text that FOLLOWS it cannot
extend it. `NoDigitStart` is that side condition, and it is the whole
compact grammar's follow set in miniature: every position a number can
occupy in a canonical rendering is followed by `,`, `]`, `}`, or end of
input, none of which is a digit. `Cas.Values.JsonParse` discharges that
observation for the grammar; here it is a premise.
-/

namespace Cas.Json

/-! ## One digit -/

/-- One decimal digit read back — the inverse of `Nat.digitChar` on the
decimal range, spelled as a table so both directions close by `decide`.
Mirrors `hexValue` in `Cas.Values.JsonInj`. -/
def digitValue : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9
  | _ => none

/-- Forward: every decimal digit character reads back as its value. -/
theorem digitValue_digitChar : ∀ n, n < 10 → digitValue (Nat.digitChar n) = some n := by
  decide

/-- Backward: whatever `digitValue` answers is a decimal digit, it is
that character's `Nat.digitChar` spelling, and it agrees with the offset
arithmetic `Nat.ofDigitChars` performs. -/
theorem digitValue_sound {c : Char} {k : Nat} (h : digitValue c = some k) :
    k < 10 ∧ Nat.digitChar k = c ∧ c.toNat - '0'.toNat = k := by
  unfold digitValue at h
  split at h <;> simp_all <;> omega

/-! ## The greedy digit run -/

/-- The follow-set premise: this text cannot extend a decimal run. -/
def NoDigitStart : List Char → Prop
  | [] => True
  | c :: _ => digitValue c = none

/-- Take the longest decimal prefix. Greedy — and the greed is exactly
what `NoDigitStart` guards. -/
def takeDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    match digitValue c with
    | some _ => (c :: (takeDigits cs).1, (takeDigits cs).2)
    | none => ([], c :: cs)

/-- ADEQUACY of the run: a block of digits followed by anything that
cannot extend it is taken exactly. -/
theorem takeDigits_append :
    ∀ (ds rest : List Char), (∀ c ∈ ds, (digitValue c).isSome) →
      NoDigitStart rest → takeDigits (ds ++ rest) = (ds, rest)
  | [], rest, _, hr => by
    cases rest with
    | nil => rfl
    | cons c cs =>
      show takeDigits (c :: cs) = _
      simp only [takeDigits, show digitValue c = none from hr]
  | d :: ds, rest, hd, hr => by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hd d (by simp))
    show takeDigits (d :: (ds ++ rest)) = _
    simp only [takeDigits, hk,
      takeDigits_append ds rest (fun c hc => hd c (by simp [hc])) hr]

/-- EXACTNESS of the run: the answer reassembles the input, every
character taken is a digit, and what is left cannot extend the run. -/
theorem takeDigits_sound :
    ∀ (cs : List Char),
      (takeDigits cs).1 ++ (takeDigits cs).2 = cs ∧
      (∀ c ∈ (takeDigits cs).1, (digitValue c).isSome) ∧
      NoDigitStart (takeDigits cs).2
  | [] => ⟨rfl, by simp [takeDigits], trivial⟩
  | c :: cs => by
    match hc : digitValue c with
    | none =>
      refine ⟨?_, ?_, ?_⟩ <;> simp only [takeDigits, hc]
      · rfl
      · simp
      · exact hc
    | some k =>
      obtain ⟨hcat, hall, hns⟩ := takeDigits_sound cs
      refine ⟨?_, ?_, ?_⟩ <;> simp only [takeDigits, hc]
      · simpa using hcat
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hc ▸ rfl
        · exact hall d hd
      · exact hns

/-! ## The strict canonical natural -/

/-- A digit block is canonically spelled when it has no leading zero —
unless it IS the zero spelling. Exactly `Nat.repr`'s image. -/
def canonDigits : List Char → Bool
  | [] => false
  | d :: ds => !(d == '0' && !ds.isEmpty)

/-- THE strict natural parser: the greedy decimal run, refused unless it
is canonically spelled. Reads `"0"` and `"12"`; refuses `""`, `"00"`,
`"007"`, and `"01"`. -/
def parseNat (cs : List Char) : Option (Nat × List Char) :=
  if canonDigits (takeDigits cs).1 then
    some (Nat.ofDigitChars 10 (takeDigits cs).1 0, (takeDigits cs).2)
  else none

/-! ### `Nat.repr` is injective -/

/-- `Nat.repr` is INJECTIVE. The toolchain ships the inverse
(`Nat.ofDigitChars_ten_toDigits`); this is the lemma the schema plane
named as sub-obligation 2 of `Json.RenderPlainInjective`. -/
theorem natRepr_inj {n m : Nat} (h : Nat.repr n = Nat.repr m) : n = m := by
  have hd : Nat.toDigits 10 n = Nat.toDigits 10 m := by
    simpa using congrArg String.toList h
  simpa using congrArg (fun l => Nat.ofDigitChars 10 l 0) hd

/-- The same fact at `toString`, which is what the renderer calls. -/
theorem toString_nat_inj {n m : Nat} (h : toString n = toString m) : n = m :=
  natRepr_inj h

/-! ### The decimal spelling is canonical -/

/-- Every character of a decimal spelling is a digit. Proved off
`Nat.toDigits_eq_if`, so this module needs no `Char.isDigit` bridge. -/
theorem digitValue_mem_toDigits :
    ∀ (n : Nat), ∀ c ∈ Nat.toDigits 10 n, (digitValue c).isSome := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro c hc
    rw [Nat.toDigits_eq_if (by decide)] at hc
    split at hc
    · rw [List.mem_singleton] at hc
      subst hc
      rw [digitValue_digitChar _ (by omega)]
      rfl
    · rcases List.mem_append.mp hc with h | h
      · exact ih (n / 10) (Nat.div_lt_self (by omega) (by decide)) c h
      · rw [List.mem_singleton] at h
        subst h
        rw [digitValue_digitChar _ (Nat.mod_lt _ (by decide))]
        rfl

/-- A digit block whose leading digit is nonzero denotes a positive
number — the step that makes the reconstruction below legal. -/
private theorem ofDigitChars_pos {d : Char} {j : Nat} (ds : List Char)
    (hd : digitValue d = some j) (hj : j ≠ 0) :
    0 < Nat.ofDigitChars 10 (d :: ds) 0 := by
  have h48 : d.toNat - '0'.toNat = j := (digitValue_sound hd).2.2
  rw [Nat.ofDigitChars_cons, Nat.mul_zero, Nat.zero_add, h48,
    Nat.ofDigitChars_eq_ofDigitChars_zero]
  have hp : 0 < 10 ^ ds.length := Nat.pow_pos (by decide)
  have : 0 < 10 ^ ds.length * j := Nat.mul_pos hp (Nat.pos_of_ne_zero hj)
  omega

/-- A decimal spelling never leads with a zero unless it IS the zero
spelling: the strictness `parseNat` enforces is `Nat.repr`'s own
discipline, not an extra rule. -/
theorem canonDigits_toDigits (n : Nat) : canonDigits (Nat.toDigits 10 n) = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_if (by decide)]
    split
    · simp [canonDigits]
    · rename_i hge
      have hge : 10 ≤ n := by omega
      have hpos : 0 < n / 10 := Nat.div_pos hge (by decide)
      have hprev := ih (n / 10) (Nat.div_lt_self (by omega) (by decide))
      have hval : Nat.ofDigitChars 10 (Nat.toDigits 10 (n / 10)) 0 = n / 10 := by simp
      match hd : Nat.toDigits 10 (n / 10) with
      | [] => exact absurd hd Nat.toDigits_ne_nil
      | d :: ds =>
        rw [hd] at hprev hval
        have hd0 : d ≠ '0' := by
          intro h0
          subst h0
          cases ds with
          | nil =>
            simp [Nat.ofDigitChars_cons] at hval
            omega
          | cons e es => simp [canonDigits] at hprev
        simp [canonDigits, hd0]

/-- The reconstruction, with the accumulator the fold carries: reading a
digit block on top of a POSITIVE running value appends the block to that
value's spelling. Left-recursive, which is why the parser's exactness
needs no reverse recursor. -/
private theorem toDigits_ofDigitChars_acc :
    ∀ (ds : List Char) (init : Nat), (∀ c ∈ ds, (digitValue c).isSome) → 0 < init →
      Nat.toDigits 10 (Nat.ofDigitChars 10 ds init) = Nat.toDigits 10 init ++ ds
  | [], _, _, _ => by simp
  | c :: cs, init, hall, hpos => by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (hall c (by simp))
    obtain ⟨hk10, hkc, hk48⟩ := digitValue_sound hk
    rw [Nat.ofDigitChars_cons, hk48,
      toDigits_ofDigitChars_acc cs (10 * init + k)
        (fun x hx => hall x (by simp [hx])) (by omega),
      ← Nat.toDigits_append_toDigits (by decide) hpos hk10,
      Nat.toDigits_of_lt_base (b := 10) (n := k) hk10, hkc]
    simp

/-- The reconstruction: a canonically spelled digit block is exactly the
decimal spelling of the number it denotes. The exactness half of the
number parser. -/
theorem toDigits_ofDigitChars :
    ∀ (ds : List Char), (∀ c ∈ ds, (digitValue c).isSome) → canonDigits ds = true →
      Nat.toDigits 10 (Nat.ofDigitChars 10 ds 0) = ds
  | [], _, h => by simp [canonDigits] at h
  | d :: ds, hall, hcanon => by
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hall d (by simp))
    obtain ⟨hj10, hjc, hj48⟩ := digitValue_sound hj
    rw [Nat.ofDigitChars_cons, Nat.mul_zero, Nat.zero_add, hj48]
    by_cases hj0 : j = 0
    · subst hj0
      have hd0 : d = '0' := by rw [← hjc]; rfl
      subst hd0
      cases ds with
      | nil => simp
      | cons e es => simp [canonDigits] at hcanon
    · rw [toDigits_ofDigitChars_acc ds j (fun x hx => hall x (by simp [hx]))
        (Nat.pos_of_ne_zero hj0), Nat.toDigits_of_lt_base (by omega), hjc]
      rfl

/-! ### The two parser laws for numbers -/

/-- ADEQUACY: a decimal spelling, followed by anything that cannot
extend it, parses back to exactly its number. -/
theorem parseNat_toDigits (n : Nat) (rest : List Char) (h : NoDigitStart rest) :
    parseNat (Nat.toDigits 10 n ++ rest) = some (n, rest) := by
  simp only [parseNat, takeDigits_append _ _ (digitValue_mem_toDigits n) h,
    canonDigits_toDigits n, if_pos, Nat.ofDigitChars_ten_toDigits]

/-- ADEQUACY at `toString`, the spelling the renderer emits. -/
theorem parseNat_repr (n : Nat) (rest : List Char) (h : NoDigitStart rest) :
    parseNat ((toString n).toList ++ rest) = some (n, rest) := by
  simpa using parseNat_toDigits n rest h

/-- EXACTNESS: whatever `parseNat` answers re-renders to the characters
it consumed, and what it leaves cannot extend the run. -/
theorem parseNat_sound {cs : List Char} {n : Nat} {rest : List Char}
    (h : parseNat cs = some (n, rest)) :
    Nat.toDigits 10 n ++ rest = cs ∧ NoDigitStart rest := by
  obtain ⟨hcat, hall, hns⟩ := takeDigits_sound cs
  simp only [parseNat] at h
  split at h
  · rename_i hcanon
    have hpair := Option.some.inj h
    have hn : Nat.ofDigitChars 10 (takeDigits cs).1 0 = n := congrArg Prod.fst hpair
    have hr : (takeDigits cs).2 = rest := congrArg Prod.snd hpair
    subst hn; subst hr
    exact ⟨by rw [toDigits_ofDigitChars _ hall hcanon]; exact hcat, hns⟩
  · exact absurd h (by simp)

/-! ## The strictness, worked at elaboration

The acceptance contract for numbers, run so the refusals are visible in
the source rather than only stated in a docstring. -/

-- The zero spelling and an ordinary decimal are read; the follow set is
-- left untouched.
#guard parseNat "0".toList == some (0, [])
#guard parseNat "12".toList == some (12, [])
#guard parseNat "12]".toList == some (12, [']'])

-- No leading zeros, no empty run, no sign: the alternate spellings a
-- tolerant reader would admit are refused outright.
#guard parseNat "00".toList == none
#guard parseNat "01".toList == none
#guard parseNat "007".toList == none
#guard parseNat "".toList == none
#guard parseNat "+1".toList == none

end Cas.Json
