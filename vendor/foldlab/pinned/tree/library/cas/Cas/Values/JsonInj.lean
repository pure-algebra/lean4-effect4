import Cas.Values.Json

/-!
# Bytes determine the canonical value — the value-plane direction

`Cas.Values.Json` proves the rendering theorem in one direction: on a
canonically spelled value the canonical rendering performs no sort
(`renderCompact_eq_renderPlain`). The OTHER direction — the one the
schema plane's facades name "bytes determine the canonical value" — is
that the rendering is *injective*: two canonical values with the same
compact bytes are the same value.

This module states that direction precisely, refutes the naive form,
and discharges the escape half. The direction ITSELF is proved in
`Cas.Values.JsonParse`, from the strict parser: see
`Json.renderPlain_injective`.

## The naive form is false

`renderPlain` is NOT injective on `Value.Canonical`. The value model
carries two number constructors, `Value.nat` and `Value.int`, and the
canonical rendering sends both through `toString`:

    renderPlain (.nat 0) = "0" = renderPlain (.int 0)

`renderPlain_nat_int` is that identity for every `n`, and
`renderPlain_not_injective` is the refutation. This is a fact about the
value model, not about the printer — there is no escaping it inside
`Value`, because the two constructors have the same decimal spelling by
design (JSON has one number syntax).

## The corrected form — injectivity up to the number collapse

`Value.numNorm` is that collapse as a function: a nonnegative `.int`
rewritten to the `.nat` with the same decimal spelling, recursively.
`Value.NumNormal` names its fixed points. The collapse is exactly
rendering-invariant (`renderPlain_numNorm`), so `numNorm` is the
strongest conclusion any injectivity statement about `renderPlain` can
carry, and `RenderPlainInjective` states it:

    ∀ v w, v.Canonical → w.Canonical →
      renderPlain v = renderPlain w → v.numNorm = w.numNorm

This mirrors the schema plane's `Ast.repNorm` idiom exactly: a
projection that makes one identification, the identification named as a
function, and the law stated up to it with an on-the-nose corollary on
the fixed points.

## `RenderPlainInjective` is PROVED — in `Cas.Values.JsonParse`

It stays a `Prop`-valued definition here, because that is the shape the
schema plane's derivation was wired against and the wiring did not need
to change. What changed is that `Json.renderPlain_injective` now
inhabits it, so every law that took it as a hypothesis is unconditional
(`Cas.Schema.PayloadInj`). "The node at this address IS this code" is a
fact (survey blocker B7 closed, ruling 11 closed).

The proof is the strict parser's left-inverse property, and nothing
else: `parse (renderPlain v) = some v.numNorm` for every `v`, so two
values with one rendering are handed to one parser call, which answers
one value. The three sub-obligations this module named, and where each
landed:

1. **`escapeCompact` is injective — PROVED HERE** (`escapeCompact_inj`,
   and with it `renderPlain_str_inj`). The escape alphabet is
   prefix-free, and the proof is by the left-inverse route rather than
   by comparing codes pairwise: `unescapeOne` reads one code off the
   front of an escaped character list, `unescapeOne_escapeCharCompact`
   is its round trip with an arbitrary tail, and injectivity follows by
   list induction. This was the named likely wall; it was not one.

   One caveat the parser slice surfaced: `unescapeOne` is a left
   inverse ON THE IMAGE, which is exactly what the lemma above claims
   and LESS than a strict reader needs — it will also read `A` as
   `A`, a spelling the encoder never emits. `JsonParse.unescapeCanon`
   is the strict wrapper (read, re-encode, demand the same bytes).
2. **`Nat.repr` is injective — PROVED** (`Digits.natRepr_inj`,
   `Cas.Values.Digits`). The toolchain ships no such lemma, but Lean
   4.33 ships the INVERSE — `Nat.ofDigitChars` with
   `Nat.ofDigitChars_ten_toDigits` — which was the part that cost.
3. **The rendering is self-delimiting — PROVED**
   (`JsonParse.parseValue_renderChars`). It is a parser correctness
   proof, as expected, and the follow set is `Digits.NoDigitStart`:
   every position a value can occupy in a canonical rendering is
   followed by `,`, `]`, `}`, or end of input, none of which is a
   digit.
-/

namespace Cas.Json

/-! ## The number collapse -/

/-- The two number constructors have one decimal spelling: the compact
rendering cannot tell `.nat n` from `.int n`. -/
theorem renderPlain_nat_int (n : Nat) :
    renderPlain (.nat n) = renderPlain (.int (Int.ofNat n)) := rfl

/-- The naive rendering-injectivity statement is FALSE — canonicality
does not help, because both witnesses are scalars. -/
theorem renderPlain_not_injective :
    ¬ ∀ v w : Value, v.Canonical → w.Canonical →
        renderPlain v = renderPlain w → v = w := by
  intro h
  have := h (.nat 0) (.int 0) trivial trivial rfl
  exact Value.noConfusion this

mutual

/-- The rendering's number collapse as a function: a nonnegative `.int`
rewritten to the `.nat` with the same decimal spelling. The one
identification the compact rendering makes on the value model. -/
def Value.numNorm : Value → Value
  | .int i => if 0 ≤ i then .nat i.toNat else .int i
  | .arr xs => .arr (numNormItems xs)
  | .obj fs => .obj (numNormFields fs)
  | v => v

def numNormItems : List Value → List Value
  | [] => []
  | x :: xs => x.numNorm :: numNormItems xs

def numNormFields : List (String × Value) → List (String × Value)
  | [] => []
  | (k, v) :: fs => (k, v.numNorm) :: numNormFields fs

end

/-- The values the collapse leaves alone: every nonnegative number
already spelled `.nat`. -/
def Value.NumNormal (v : Value) : Prop := v.numNorm = v

mutual

theorem Value.numNorm_idem : ∀ (v : Value), v.numNorm.numNorm = v.numNorm
  | .null | .bool _ | .nat _ | .str _ => rfl
  | .int i => by
    by_cases h : 0 ≤ i
    · simp only [Value.numNorm, if_pos h]
    · simp only [Value.numNorm, if_neg h]
  | .arr xs => by
    simp only [Value.numNorm, numNormItems_idem xs]
  | .obj fs => by
    simp only [Value.numNorm, numNormFields_idem fs]

theorem numNormItems_idem :
    ∀ (xs : List Value), numNormItems (numNormItems xs) = numNormItems xs
  | [] => rfl
  | x :: xs => by
    simp only [numNormItems, Value.numNorm_idem x, numNormItems_idem xs]

theorem numNormFields_idem :
    ∀ (fs : List (String × Value)),
      numNormFields (numNormFields fs) = numNormFields fs
  | [] => rfl
  | (k, v) :: fs => by
    simp only [numNormFields, Value.numNorm_idem v, numNormFields_idem fs]

end

/-- Every normal form is `NumNormal`. -/
theorem Value.numNorm_numNormal (v : Value) : v.numNorm.NumNormal :=
  Value.numNorm_idem v

/-- The collapse touches no key. -/
theorem numNormFields_keys :
    ∀ (fs : List (String × Value)),
      (numNormFields fs).map (fun f => f.1) = fs.map (fun f => f.1)
  | [] => rfl
  | (k, v) :: fs => by
    simp only [numNormFields, List.map_cons, numNormFields_keys fs]

/-! The collapse preserves object keys, so it preserves canonical
spelling. -/

mutual

theorem Value.numNorm_canonical :
    ∀ (v : Value), v.Canonical → v.numNorm.Canonical
  | .null, _ | .bool _, _ | .nat _, _ | .str _, _ => trivial
  | .int i, _ => by
    simp only [Value.numNorm]
    split <;> trivial
  | .arr xs, h => by
    simp only [Value.numNorm]
    exact numNormItems_canonical xs h
  | .obj fs, ⟨hsorted, hfields⟩ => by
    simp only [Value.numNorm]
    refine ⟨?_, numNormFields_canonical fs hfields⟩
    have hkeys : List.Pairwise (· < ·) (fs.map (fun f => f.1)) :=
      (List.pairwise_map).mpr hsorted
    rw [← numNormFields_keys fs] at hkeys
    exact (List.pairwise_map).mp hkeys

theorem numNormItems_canonical :
    ∀ (xs : List Value), CanonicalItems xs → CanonicalItems (numNormItems xs)
  | [], _ => trivial
  | x :: xs, h => ⟨Value.numNorm_canonical x h.1, numNormItems_canonical xs h.2⟩

theorem numNormFields_canonical :
    ∀ (fs : List (String × Value)),
      CanonicalFields fs → CanonicalFields (numNormFields fs)
  | [], _ => trivial
  | (_, v) :: fs, h =>
    ⟨Value.numNorm_canonical v h.1, numNormFields_canonical fs h.2⟩

end

/-! ## The collapse is exactly rendering-invariant

Normalizing changes no bytes: `numNorm` identifies only what the
rendering already identifies, so no injectivity statement about
`renderPlain` can conclude more than `numNorm`-equality. -/

mutual

theorem renderPlain_numNorm :
    ∀ (v : Value), renderPlain v.numNorm = renderPlain v
  | .null | .bool _ | .nat _ | .str _ => rfl
  | .int i => by
    by_cases h : 0 ≤ i
    · show renderPlain (if 0 ≤ i then Value.nat i.toNat else Value.int i) = _
      rw [if_pos h]
      calc renderPlain (Value.nat i.toNat)
          = renderPlain (Value.int (Int.ofNat i.toNat)) := rfl
        _ = renderPlain (Value.int i) :=
              congrArg (fun z => renderPlain (Value.int z)) (Int.toNat_of_nonneg h)
    · show renderPlain (if 0 ≤ i then Value.nat i.toNat else Value.int i) = _
      rw [if_neg h]
  | .arr xs => by
    simp only [Value.numNorm, renderPlain, renderPlainItems_numNorm xs]
  | .obj fs => by
    simp only [Value.numNorm, renderPlain, renderPlainFields_numNorm fs]

theorem renderPlainItems_numNorm :
    ∀ (xs : List Value), renderPlainItems (numNormItems xs) = renderPlainItems xs
  | [] => rfl
  | x :: xs => by
    simp only [numNormItems, renderPlainItems, renderPlain_numNorm x,
      renderPlainItems_numNorm xs]

theorem renderPlainFields_numNorm :
    ∀ (fs : List (String × Value)),
      renderPlainFields (numNormFields fs) = renderPlainFields fs
  | [] => rfl
  | (k, v) :: fs => by
    simp only [numNormFields, renderPlainFields, renderPlain_numNorm v,
      renderPlainFields_numNorm fs]

end

/-! ## The escape alphabet is injective

The compact escape (`escapeCharCompact`) is a prefix-free code: `\`
opens either a two-character short escape or the six-character
`\u00xx`, and every other character codes as itself. Rather than
compare the eight classes pairwise, the code is inverted:
`unescapeOne` reads one code off the front of a character list, and
`unescapeOne_escapeCharCompact` is the round trip WITH AN ARBITRARY
TAIL — which is exactly prefix-freeness, in the form induction wants.
-/

/-- One lowercase hex digit read back — the inverse of `hexLower` on
the digit range. -/
def hexValue : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9 | 'a' => some 10 | 'b' => some 11
  | 'c' => some 12 | 'd' => some 13 | 'e' => some 14 | 'f' => some 15
  | _ => none

theorem hexValue_hexLower : ∀ n, n < 16 → hexValue (hexLower n) = some n := by
  decide

/-- Read one compact escape code off the front of a character list.
The left inverse of `escapeCharCompact` on its image
(`unescapeOne_escapeCharCompact`); its behaviour off the image is
irrelevant and unclaimed. -/
def unescapeOne : List Char → Option (Char × List Char)
  | [] => none
  | c :: rest =>
    if c = '\\' then
      match rest with
      | '"' :: r => some ('"', r)
      | '\\' :: r => some ('\\', r)
      | 'b' :: r => some (Char.ofNat 8, r)
      | 't' :: r => some (Char.ofNat 9, r)
      | 'n' :: r => some (Char.ofNat 10, r)
      | 'f' :: r => some (Char.ofNat 12, r)
      | 'r' :: r => some (Char.ofNat 13, r)
      | 'u' :: '0' :: '0' :: h :: l :: r =>
        match hexValue h, hexValue l with
        | some hv, some lv => some (Char.ofNat (hv * 16 + lv), r)
        | _, _ => none
      | _ => none
    else some (c, rest)

/-- PREFIX-FREEDOM, as a round trip: one character's code is read back
exactly, whatever follows it. -/
theorem unescapeOne_escapeCharCompact (c : Char) (rest : List Char) :
    unescapeOne ((escapeCharCompact c).toList ++ rest) = some (c, rest) := by
  simp only [escapeCharCompact]
  by_cases h1 : c = '"'
  · rw [if_pos h1, h1]; rfl
  rw [if_neg h1]
  by_cases h2 : c = '\\'
  · rw [if_pos h2, h2]; rfl
  rw [if_neg h2]
  by_cases h3 : c.toNat = 8
  · rw [if_pos h3, show c = Char.ofNat 8 by rw [← Char.ofNat_toNat c, h3]]; rfl
  rw [if_neg h3]
  by_cases h4 : c.toNat = 9
  · rw [if_pos h4, show c = Char.ofNat 9 by rw [← Char.ofNat_toNat c, h4]]; rfl
  rw [if_neg h4]
  by_cases h5 : c.toNat = 10
  · rw [if_pos h5, show c = Char.ofNat 10 by rw [← Char.ofNat_toNat c, h5]]; rfl
  rw [if_neg h5]
  by_cases h6 : c.toNat = 12
  · rw [if_pos h6, show c = Char.ofNat 12 by rw [← Char.ofNat_toNat c, h6]]; rfl
  rw [if_neg h6]
  by_cases h7 : c.toNat = 13
  · rw [if_pos h7, show c = Char.ofNat 13 by rw [← Char.ofNat_toNat c, h7]]; rfl
  rw [if_neg h7]
  by_cases h8 : c.toNat < 32
  · rw [if_pos h8, String.toList_ofList]
    show unescapeOne ('\\' :: 'u' :: '0' :: '0' ::
      hexLower (c.toNat / 16) :: hexLower (c.toNat % 16) :: rest) = _
    show (match hexValue (hexLower (c.toNat / 16)),
              hexValue (hexLower (c.toNat % 16)) with
          | some hv, some lv => some (Char.ofNat (hv * 16 + lv), rest)
          | _, _ => none) = _
    rw [hexValue_hexLower _ (by omega), hexValue_hexLower _ (by omega)]
    show some (Char.ofNat (c.toNat / 16 * 16 + c.toNat % 16), rest) = _
    rw [show c.toNat / 16 * 16 + c.toNat % 16 = c.toNat by omega,
      Char.ofNat_toNat]
  · rw [if_neg h8, String.toList_singleton]
    show (if c = '\\' then _ else some (c, rest)) = _
    rw [if_neg h2]

/-- The escape applied to a character list — the list-level twin of
`escapeCompact`, which is a `String.foldl`. -/
def escapeCodes : List Char → List Char
  | [] => []
  | c :: cs => (escapeCharCompact c).toList ++ escapeCodes cs

theorem foldl_escape_toList :
    ∀ (cs : List Char) (a : String),
      (cs.foldl (fun acc c => acc ++ escapeCharCompact c) a).toList
        = a.toList ++ escapeCodes cs
  | [], a => by simp [escapeCodes]
  | c :: cs, a => by
    simp only [List.foldl_cons, escapeCodes,
      foldl_escape_toList cs (a ++ escapeCharCompact c),
      String.toList_append, List.append_assoc]

theorem escapeCompact_toList (s : String) :
    (escapeCompact s).toList = escapeCodes s.toList := by
  simp only [escapeCompact, String.foldl_eq_foldl_toList,
    foldl_escape_toList s.toList "", String.toList_empty, List.nil_append]

theorem escapeCodes_inj :
    ∀ (cs ds : List Char), escapeCodes cs = escapeCodes ds → cs = ds
  | [], [], _ => rfl
  | [], d :: ds, h => by
    have hd := unescapeOne_escapeCharCompact d (escapeCodes ds)
    rw [show (escapeCharCompact d).toList ++ escapeCodes ds = ([] : List Char)
          from h.symm] at hd
    simp [unescapeOne] at hd
  | c :: cs, [], h => by
    have hc := unescapeOne_escapeCharCompact c (escapeCodes cs)
    rw [show (escapeCharCompact c).toList ++ escapeCodes cs = ([] : List Char)
          from h] at hc
    simp [unescapeOne] at hc
  | c :: cs, d :: ds, h => by
    have hc := unescapeOne_escapeCharCompact c (escapeCodes cs)
    have hd := unescapeOne_escapeCharCompact d (escapeCodes ds)
    rw [show (escapeCharCompact c).toList ++ escapeCodes cs
          = (escapeCharCompact d).toList ++ escapeCodes ds from h, hd] at hc
    have hpair := Option.some.inj hc
    have hce : d = c := congrArg Prod.fst hpair
    have hre : escapeCodes ds = escapeCodes cs := congrArg Prod.snd hpair
    rw [← hce, escapeCodes_inj cs ds hre.symm]

/-- SUB-OBLIGATION 1, DISCHARGED: the canonical escape is injective —
one escaped spelling per string. -/
theorem escapeCompact_inj {s t : String}
    (h : escapeCompact s = escapeCompact t) : s = t :=
  String.toList_inj.mp
    (escapeCodes_inj s.toList t.toList (by
      rw [← escapeCompact_toList, ← escapeCompact_toList, h]))

/-- The string arm of the rendering is injective outright: a rendered
JSON string determines its value. -/
theorem renderPlain_str_inj {s t : String}
    (h : renderPlain (.str s) = renderPlain (.str t)) : s = t := by
  refine escapeCompact_inj (String.toList_inj.mp ?_)
  have hl := congrArg String.toList h
  simp only [renderPlain, String.toList_append] at hl
  exact List.append_cancel_left (List.append_cancel_right hl)

/-! ## The direction, as a `Prop` -/

/-- THE direction: the compact canonical rendering is injective on
canonically spelled values, up to the number collapse.

Kept as a `Prop` rather than folded into a theorem statement because
that is the shape the schema plane was wired against.
`Cas.Values.JsonParse.renderPlain_injective` inhabits it — and proves
the stronger form with no canonicality premise
(`JsonParse.renderPlain_inj`), so the premises here are slack the
consumers happen to carry, not a restriction on the fact. -/
def RenderPlainInjective : Prop :=
  ∀ v w : Value, v.Canonical → w.Canonical →
    renderPlain v = renderPlain w → v.numNorm = w.numNorm

/-- On `NumNormal` values the obligation gives equality on the nose. -/
theorem renderPlain_inj_of_numNormal (hinj : RenderPlainInjective)
    {v w : Value} (hv : v.Canonical) (hw : w.Canonical)
    (hnv : v.NumNormal) (hnw : w.NumNormal)
    (h : renderPlain v = renderPlain w) : v = w := by
  have := hinj v w hv hw h
  rwa [hnv, hnw] at this

/-- The obligation transported to `renderCompact`, which is what the
payload bytes actually are: on canonical values the two renderings
agree (`renderCompact_eq_renderPlain`). -/
theorem renderCompact_inj_of (hinj : RenderPlainInjective)
    {v w : Value} (hv : v.Canonical) (hw : w.Canonical)
    (h : renderCompact v = renderCompact w) : v.numNorm = w.numNorm :=
  hinj v w hv hw (by
    rw [← renderCompact_eq_renderPlain v hv, ← renderCompact_eq_renderPlain w hw]
    exact h)

end Cas.Json
