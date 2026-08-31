import Cas.Values.Digits
import Cas.Values.JsonInj

/-!
# The strict canonical-JSON parser

The reader for the canonical value encoding: `Cas.Json.parse` accepts
EXACTLY the image of the canonical rendering and nothing else. It is the
missing first step of the bytes-in loop, and — through `parse_render` —
it is what discharges `Json.RenderPlainInjective`, the value plane's one
named open obligation (ruling 11, survey blocker B7).

## The acceptance contract

`parse : String → Option Value`. STRING, not `ByteArray`, and the reason
is the composition already in the estate: `Ast.payloadBytes` is
`Ast.payload.toUTF8`, and `String.toByteArray_inj` is a toolchain fact
the schema plane already leans on (`payloadBytes_inj`). Parsing at the
character level therefore reaches the bytes for free, whereas a
`ByteArray` parser would owe a UTF-8 decoder correctness proof that
nothing in the estate needs.

Accepted, exactly (`parse_sound`, `parse_render`):

- `null`, `true`, `false` — those five spellings, nothing else;
- integers as `Nat.repr` spells them: a nonempty decimal run with no
  leading zero unless the spelling is `"0"`, optionally preceded by `-`,
  and `-0` is refused. No `+`, no fraction, no exponent;
- strings as `escapeCompact` spells them: the two mandatory escapes, the
  five short escapes, lowercase `\u00xx` for the rest of the control
  range, every other character literal. The reader is `unescapeOne` —
  the same one `Cas.Values.JsonInj` proves the round trip for, so there
  is ONE escape alphabet in the estate — behind `unescapeCanon`, which
  re-encodes what it read and demands the input spelled it that way.
  `"A"` and `""` are therefore REFUSED: the canonical
  spellings are `"A"` and `"\b"`;
- arrays and objects with NO whitespace anywhere: `[`, `]`, `{`, `}`,
  `,` and `:` are adjacent to their neighbours.

Refused: whitespace, `+1`, `01`, `-0`, `1.0`, `1e5`, `'single quotes'`,
trailing commas, trailing input after the value, unpaired escapes.

## Sorted keys are the GATE's question, not the parser's

`parse` does NOT require object keys to be sorted, and does not sort
them. It answers the value as spelled, in the order the bytes carry it,
and `Value.Canonical` is then checked (or imposed by `canonValue`)
downstream. This is the door's existing split, verbatim — "Shape is the
decoder's question; discipline is the gate's" (`Cas.Schema.Ingest`) —
and it is what makes `parse_sound` a clean biconditional on the image of
`renderPlain`: an unsorted object is a real value with a real rendering,
so refusing it here would make the parser NOT a left inverse.

Nothing is lost for canonicality: `Ast.ingestBytes` runs `canonValue`
exactly as `ingest` does, and `Value.Canonical` is decided at the gate.

## The measure

`parseValue` is structural on a fuel argument, and the fuel the entry
point supplies is the input's own length. No `partial`, no
well-founded recursion, no `native_decide`: every parser call is
answered by the kernel. `parseFuel` (the invariant `|input| ≤ fuel`) is
what the adequacy proof carries, and it closes at the top because
`parse` starts with exactly `cs.length`.

## The follow set, discharged

`renderPlain` is not prefix-free — `"1"` prefixes `"12"` — so a number
is only recoverable when what follows cannot extend it
(`Digits.NoDigitStart`). The grammar discharges that premise: every
position a value can occupy is followed by `,`, `]`, `}`, or end of
input, which is exactly what `itemsChars` and `fieldsChars` spell. That
is why the adequacy statement quantifies over an arbitrary tail with
`NoDigitStart` rather than over the whole document.
-/

namespace Cas.Json

/-! ## The rendering, at the character level

`renderPlain` is a `String` fold through `String.intercalate`;
`renderChars` is the same rendering spelled on `List Char`, in the shape
the parser consumes — an array's tail carries its own closing bracket,
an object's its own brace. `renderChars_eq` is the bridge, proved once,
and everything below works on lists. Same idiom as `escapeCodes` for
`escapeCompact` in `Cas.Values.JsonInj`. -/

/-- One object field's characters, given the field value's. -/
def fieldChars (k : String) (body : List Char) : List Char :=
  '"' :: (escapeCodes k.toList ++ '"' :: ':' :: body)

mutual

/-- The canonical rendering as characters. -/
def renderChars : Value → List Char
  | .null => ['n', 'u', 'l', 'l']
  | .bool b => if b then ['t', 'r', 'u', 'e'] else ['f', 'a', 'l', 's', 'e']
  | .nat n => Nat.toDigits 10 n
  | .int i =>
    if 0 ≤ i then Nat.toDigits 10 i.toNat else '-' :: Nat.toDigits 10 (-i).toNat
  | .str s => '"' :: (escapeCodes s.toList ++ ['"'])
  | .arr [] => ['[', ']']
  | .arr (x :: xs) => '[' :: (renderChars x ++ itemsChars xs)
  | .obj [] => ['{', '}']
  | .obj ((k, v) :: fs) => '{' :: (fieldChars k (renderChars v) ++ fieldsChars fs)

/-- An array's tail: the remaining elements, each behind its comma, and
the closing bracket. -/
def itemsChars : List Value → List Char
  | [] => [']']
  | x :: xs => ',' :: (renderChars x ++ itemsChars xs)

/-- An object's tail: the remaining fields, each behind its comma, and
the closing brace. -/
def fieldsChars : List (String × Value) → List Char
  | [] => ['}']
  | (k, v) :: fs => ',' :: (fieldChars k (renderChars v) ++ fieldsChars fs)

end

/-! The punctuation literals the printer appends, as character lists —
so the bridge below rewrites without a `String`/`List` normalization
step at every joint. -/

private theorem toList_lbracket : ("[" : String).toList = ['['] := rfl
private theorem toList_rbracket : ("]" : String).toList = [']'] := rfl
private theorem toList_lbrace : ("{" : String).toList = ['{'] := rfl
private theorem toList_rbrace : ("}" : String).toList = ['}'] := rfl
private theorem toList_comma : ("," : String).toList = [','] := rfl
private theorem toList_quote : ("\"" : String).toList = ['"'] := rfl
private theorem toList_quotecolon : ("\":" : String).toList = ['"', ':'] := rfl

mutual

/-- THE BRIDGE: the character rendering is the canonical rendering. -/
theorem renderChars_eq : ∀ (v : Value), renderChars v = (renderPlain v).toList
  | .null => rfl
  | .bool b => by cases b <;> rfl
  | .nat n => by simp [renderChars, renderPlain]
  | .int i => by
    simp only [renderChars, renderPlain, Int.toString_eq_repr, Int.repr_eq_if]
    split
    · simp
    · simp [String.toList_append]
  | .str s => by
    simp only [renderChars, renderPlain, String.toList_append, escapeCompact_toList]
    rfl
  | .arr [] => by simp [renderChars, renderPlain, renderPlainItems]
  | .arr (x :: xs) => by
    simp only [renderChars, renderPlain, renderPlainItems, String.toList_append,
      toList_lbracket, toList_rbracket, List.append_assoc,
      itemsChars_eq xs (renderPlain x), ← renderChars_eq x]
    rfl
  | .obj [] => by simp [renderChars, renderPlain, renderPlainFields]
  | .obj ((k, v) :: fs) => by
    simp only [renderChars, renderPlain, renderPlainFields, String.toList_append,
      toList_lbrace, toList_rbrace, List.append_assoc,
      fieldsChars_eq fs ("\"" ++ escapeCompact k ++ "\":" ++ renderPlain v),
      ← renderChars_eq v, toList_quote, toList_quotecolon, escapeCompact_toList]
    simp [fieldChars]

/-- The array tail, against the printer's `intercalate`. The `pre`
parameter is the already-rendered head, which is what makes the
recursion structural in the list alone. -/
theorem itemsChars_eq : ∀ (xs : List Value) (pre : String),
    (String.intercalate "," (pre :: renderPlainItems xs)).toList ++ [']']
      = pre.toList ++ itemsChars xs
  | [], pre => by simp [itemsChars, renderPlainItems]
  | y :: ys, pre => by
    simp only [renderPlainItems, String.intercalate_cons_cons, String.toList_append,
      toList_comma, List.append_assoc, itemsChars_eq ys (renderPlain y),
      ← renderChars_eq y, itemsChars]
    simp

/-- The object tail, against the printer's `intercalate`. -/
theorem fieldsChars_eq : ∀ (fs : List (String × Value)) (pre : String),
    (String.intercalate "," (pre :: renderPlainFields fs)).toList ++ ['}']
      = pre.toList ++ fieldsChars fs
  | [], pre => by simp [fieldsChars, renderPlainFields]
  | (k, v) :: fs, pre => by
    simp only [renderPlainFields, String.intercalate_cons_cons, String.toList_append,
      toList_comma, List.append_assoc,
      fieldsChars_eq fs ("\"" ++ escapeCompact k ++ "\":" ++ renderPlain v),
      ← renderChars_eq v, fieldsChars, fieldChars, toList_quote, toList_quotecolon,
      escapeCompact_toList]
    simp

end

/-! ## The first character of a rendering

The one place the grammar is not decided by a literal: an array's
opening bracket is followed either by `]` (the empty array) or by a
value, and the two are told apart by the fact that NO value renders
starting with `]`. Every other branch of the parser dispatches on a
character the rendering supplies literally. -/

private theorem toDigits_head (n : Nat) :
    ∃ c t, Nat.toDigits 10 n = c :: t ∧ digitValue c ≠ none := by
  match hd : Nat.toDigits 10 n with
  | [] => exact absurd hd Nat.toDigits_ne_nil
  | c :: t =>
    refine ⟨c, t, rfl, ?_⟩
    have := digitValue_mem_toDigits n c (by rw [hd]; simp)
    intro h
    rw [h] at this
    exact absurd this (by simp)

/-- No value's rendering begins with a closing bracket. -/
theorem renderChars_head : ∀ (v : Value), ∃ c t, renderChars v = c :: t ∧ c ≠ ']'
  | .null => ⟨'n', ['u', 'l', 'l'], rfl, by decide⟩
  | .bool true => ⟨'t', ['r', 'u', 'e'], rfl, by decide⟩
  | .bool false => ⟨'f', ['a', 'l', 's', 'e'], rfl, by decide⟩
  | .str _ => ⟨'"', _, rfl, by decide⟩
  | .arr [] => ⟨'[', [']'], rfl, by decide⟩
  | .arr (_ :: _) => ⟨'[', _, rfl, by decide⟩
  | .obj [] => ⟨'{', ['}'], rfl, by decide⟩
  | .obj ((_, _) :: _) => ⟨'{', _, rfl, by decide⟩
  | .nat n => by
    obtain ⟨c, t, hct, hdv⟩ := toDigits_head n
    exact ⟨c, t, hct, fun h => hdv (by rw [h]; rfl)⟩
  | .int i => by
    simp only [renderChars]
    split
    · obtain ⟨c, t, hct, hdv⟩ := toDigits_head i.toNat
      exact ⟨c, t, hct, fun h => hdv (by rw [h]; rfl)⟩
    · exact ⟨'-', _, rfl, by decide⟩

/-! ## The parser

Structural on fuel throughout — no `partial`, no well-founded
recursion. The dispatch is by `if` on the leading character rather than
by deep literal patterns, because that is what the adequacy proof can
drive: at a number the leading character is `Nat.digitChar k` for an
unknown `k`, and only an `if` chain lets the proof discharge the
branches it does not take. -/

/-- Match a fixed literal off the front, or refuse. -/
def matchLit : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | _ :: _, [] => none
  | c :: l, d :: cs => if c = d then matchLit l cs else none

theorem matchLit_append : ∀ (l r : List Char), matchLit l (l ++ r) = some r
  | [], _ => rfl
  | c :: l, r => by simp [matchLit, matchLit_append l r]

theorem matchLit_sound : ∀ (l cs r : List Char), matchLit l cs = some r → l ++ r = cs
  | [], cs, r, h => by simpa using (Option.some.inj h).symm
  | _ :: _, [], _, h => by simp [matchLit] at h
  | c :: l, d :: cs, r, h => by
    simp only [matchLit] at h
    split at h
    · rename_i hcd
      subst hcd
      simp only [List.cons_append, List.cons.injEq, true_and]
      exact matchLit_sound l cs r h
    · simp at h

/-! ### The escape reader, and the strictness it needs

`unescapeOne` (`Cas.Values.JsonInj`) reads a code and is a left inverse
ON THE ENCODER'S IMAGE — which is all its round-trip lemma claims, and
less than a strict parser needs. It happily reads `A` as `A` and
`` as a backspace, neither of which the encoder ever emits (`A` is
literal; a backspace is `\b`). Admitting them would make `parse` accept
two spellings of one string, and `parse_sound` would be FALSE.

`unescapeCanon` is the fix, and it is the estate's own byte-identity
idiom applied one level down: read the character, then RE-ENCODE it and
demand the input actually spells it that way. The re-encoding is
`matchLit` against `escapeCharCompact`, so the check is local (at most
six characters), soundness is `matchLit_sound` and adequacy is
`matchLit_append` — no case analysis over the escape alphabet at all. -/

/-- The STRICT escape reader: `unescapeOne` answers the character, and
the answer is admitted only if the input spells it the way
`escapeCharCompact` spells it. -/
def unescapeCanon (cs : List Char) : Option (Char × List Char) :=
  match unescapeOne cs with
  | some (ch, _) => (matchLit (escapeCharCompact ch).toList cs).map fun r => (ch, r)
  | none => none

/-- ADEQUACY: a canonically escaped character is read back, with its
tail untouched. -/
theorem unescapeCanon_escapeCharCompact (c : Char) (rest : List Char) :
    unescapeCanon ((escapeCharCompact c).toList ++ rest) = some (c, rest) := by
  simp only [unescapeCanon, unescapeOne_escapeCharCompact c rest,
    matchLit_append, Option.map_some]

/-- SOUNDNESS: whatever the reader answers is spelled the way the
encoder spells it. Immediate — that is what the reader checks. -/
theorem unescapeCanon_sound {cs : List Char} {ch : Char} {rest : List Char}
    (h : unescapeCanon cs = some (ch, rest)) :
    (escapeCharCompact ch).toList ++ rest = cs := by
  unfold unescapeCanon at h
  split at h
  · rename_i c' _ _
    match hm : matchLit (escapeCharCompact c').toList cs with
    | none => simp [hm] at h
    | some r =>
      simp only [hm] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hc, hr⟩ := h
      subst hc; subst hr
      exact matchLit_sound _ _ _ hm
  · simp at h

/-- Read a canonical string body up to its closing quote, one escape
code at a time through `unescapeCanon`. The closing quote is tested
FIRST, which is what makes the reader stop: `escapeCharCompact` never
emits a bare `"`. -/
def parseStrChars : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, c :: cs =>
    if c = '"' then some ([], cs)
    else
      match unescapeCanon (c :: cs) with
      | some (ch, rest) => (parseStrChars f rest).map fun p => (ch :: p.1, p.2)
      | none => none

mutual

/-- THE value parser: one value off the front of the input, with the
remainder. -/
def parseValue : Nat → List Char → Option (Value × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, c :: cs =>
    if c = 'n' then (matchLit ['u', 'l', 'l'] cs).map fun r => (Value.null, r)
    else if c = 't' then (matchLit ['r', 'u', 'e'] cs).map fun r => (Value.bool true, r)
    else if c = 'f' then
      (matchLit ['a', 'l', 's', 'e'] cs).map fun r => (Value.bool false, r)
    else if c = '"' then
      (parseStrChars f cs).map fun p => (Value.str (String.ofList p.1), p.2)
    else if c = '-' then
      match parseNat cs with
      | some (n, r) => if n = 0 then none else some (Value.int (-(Int.ofNat n)), r)
      | none => none
    else if c = '[' then
      match cs with
      | [] => none
      | d :: cs' =>
        if d = ']' then some (Value.arr [], cs')
        else
          match parseValue f (d :: cs') with
          | some (x, r) => (parseItems f r).map fun p => (Value.arr (x :: p.1), p.2)
          | none => none
    else if c = '{' then
      match cs with
      | [] => none
      | d :: cs' =>
        if d = '}' then some (Value.obj [], cs')
        else
          match parseField f (d :: cs') with
          | some (kv, r) => (parseFields f r).map fun p => (Value.obj (kv :: p.1), p.2)
          | none => none
    else (parseNat (c :: cs)).map fun p => (Value.nat p.1, p.2)

/-- An array's tail: `]`, or `,` and another element. -/
def parseItems : Nat → List Char → Option (List Value × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, c :: cs =>
    if c = ']' then some ([], cs)
    else if c = ',' then
      match parseValue f cs with
      | some (x, r) => (parseItems f r).map fun p => (x :: p.1, p.2)
      | none => none
    else none

/-- One object field: `"key":value`, no space around the colon. -/
def parseField : Nat → List Char → Option ((String × Value) × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, c :: cs =>
    if c = '"' then
      match parseStrChars f cs with
      | some (k, d :: r) =>
        if d = ':' then
          match parseValue f r with
          | some (v, r') => some ((String.ofList k, v), r')
          | none => none
        else none
      | _ => none
    else none

/-- An object's tail: `}`, or `,` and another field. -/
def parseFields : Nat → List Char → Option (List (String × Value) × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, c :: cs =>
    if c = '}' then some ([], cs)
    else if c = ',' then
      match parseField f cs with
      | some (kv, r) => (parseFields f r).map fun p => (kv :: p.1, p.2)
      | none => none
    else none

end

/-- The entry point on characters: one value, and NOTHING after it. The
fuel is the input's own length, which the adequacy proof shows is always
enough. -/
def parseChars (cs : List Char) : Option Value :=
  match parseValue cs.length cs with
  | some (v, []) => some v
  | _ => none

/-- THE STRICT PARSER: the canonical rendering, read back. Total, and
refuses everything the canonical rendering does not emit. -/
def parse (s : String) : Option Value := parseChars s.toList

/-! ## Adequacy — the rendering parses back

The left-inverse direction, with an ARBITRARY TAIL, which is the form
the induction wants and the form that makes the follow set visible:
reading a rendered value off the front of `renderChars v ++ rest`
answers `v.numNorm` and leaves `rest` untouched, provided `rest` cannot
extend a decimal run. Same shape as
`JsonInj.unescapeOne_escapeCharCompact`, one level up. -/

/-- The escape of a character is nonempty and never opens with a bare
quote — which is why the string reader can test for the closing quote
first and stop there. Derived from the round trip rather than by
re-casing the eight escape classes. -/
private theorem escapeCharCompact_cons (c : Char) :
    ∃ d t, (escapeCharCompact c).toList = d :: t ∧ d ≠ '"' := by
  simp only [escapeCharCompact]
  by_cases h1 : c = '"'
  · rw [if_pos h1]; exact ⟨'\\', ['"'], rfl, by decide⟩
  rw [if_neg h1]
  by_cases h2 : c = '\\'
  · rw [if_pos h2]; exact ⟨'\\', ['\\'], rfl, by decide⟩
  rw [if_neg h2]
  by_cases h3 : c.toNat = 8
  · rw [if_pos h3]; exact ⟨'\\', ['b'], rfl, by decide⟩
  rw [if_neg h3]
  by_cases h4 : c.toNat = 9
  · rw [if_pos h4]; exact ⟨'\\', ['t'], rfl, by decide⟩
  rw [if_neg h4]
  by_cases h5 : c.toNat = 10
  · rw [if_pos h5]; exact ⟨'\\', ['n'], rfl, by decide⟩
  rw [if_neg h5]
  by_cases h6 : c.toNat = 12
  · rw [if_pos h6]; exact ⟨'\\', ['f'], rfl, by decide⟩
  rw [if_neg h6]
  by_cases h7 : c.toNat = 13
  · rw [if_pos h7]; exact ⟨'\\', ['r'], rfl, by decide⟩
  rw [if_neg h7]
  by_cases h8 : c.toNat < 32
  · rw [if_pos h8]
    exact ⟨'\\', ['u', '0', '0', hexLower (c.toNat / 16), hexLower (c.toNat % 16)],
      String.toList_ofList, by decide⟩
  · rw [if_neg h8]
    exact ⟨c, [], String.toList_singleton c, h1⟩

/-- ADEQUACY of the string reader: an escaped body followed by its
closing quote is read back exactly, whatever follows the quote. -/
theorem parseStrChars_escapeCodes :
    ∀ (cs rest : List Char) (f : Nat),
      (escapeCodes cs ++ '"' :: rest).length ≤ f →
      parseStrChars f (escapeCodes cs ++ '"' :: rest) = some (cs, rest)
  | [], rest, f, hlen => by
    cases f with
    | zero => simp [escapeCodes] at hlen
    | succ f => simp [escapeCodes, parseStrChars]
  | c :: cs, rest, f, hlen => by
    obtain ⟨d, t, hdt, hd⟩ := escapeCharCompact_cons c
    have hsplit : escapeCodes (c :: cs) ++ '"' :: rest
        = d :: (t ++ (escapeCodes cs ++ '"' :: rest)) := by
      simp only [escapeCodes, hdt]
      simp
    have hone : unescapeCanon (d :: (t ++ (escapeCodes cs ++ '"' :: rest)))
        = some (c, escapeCodes cs ++ '"' :: rest) := by
      rw [← List.cons_append, ← hdt]
      exact unescapeCanon_escapeCharCompact c (escapeCodes cs ++ '"' :: rest)
    rw [hsplit] at hlen ⊢
    cases f with
    | zero => simp at hlen
    | succ f =>
      have hlen' : (escapeCodes cs ++ '"' :: rest).length ≤ f := by
        simp only [List.length_cons, List.length_append] at hlen ⊢
        omega
      simp only [parseStrChars, if_neg hd, hone,
        parseStrChars_escapeCodes cs rest f hlen', Option.map_some]

/-- No decimal run can be extended across an array's tail: it opens with
`]` or `,`. -/
private theorem noDigitStart_itemsChars (xs : List Value) (rest : List Char) :
    NoDigitStart (itemsChars xs ++ rest) := by
  cases xs <;> simp only [itemsChars, List.cons_append] <;> rfl

/-- The same for an object's tail: `}` or `,`. -/
private theorem noDigitStart_fieldsChars (fs : List (String × Value)) (rest : List Char) :
    NoDigitStart (fieldsChars fs ++ rest) := by
  match fs with
  | [] => rfl
  | (_, _) :: _ => rfl

/-- A digit character is none of the grammar's literal openers — the
step that lets the number arm be the parser's fall-through. -/
private theorem digit_ne (d : Char) {c : Char}
    (hc : digitValue c ≠ none) (hd : digitValue d = none) : c ≠ d :=
  fun h => hc (h ▸ hd)

/-- One field, given the adequacy of its value's parse. Stated with the
value's law as a HYPOTHESIS rather than as a fourth member of the mutual
group below: `parseField` consumes no character before descending into
the value, so it has no decreasing argument of its own. -/
private theorem parseField_of (k : String) (v : Value) (rest : List Char) (f : Nat)
    (hv : ∀ (r : List Char) (g : Nat), (renderChars v ++ r).length ≤ g →
      NoDigitStart r → parseValue g (renderChars v ++ r) = some (v.numNorm, r))
    (hlen : (fieldChars k (renderChars v) ++ rest).length ≤ f)
    (hr : NoDigitStart rest) :
    parseField f (fieldChars k (renderChars v) ++ rest)
      = some ((k, v.numNorm), rest) := by
  have hsplit : fieldChars k (renderChars v) ++ rest
      = '"' :: (escapeCodes k.toList ++ '"' :: (':' :: (renderChars v ++ rest))) := by
    simp [fieldChars]
  rw [hsplit] at hlen ⊢
  cases f with
  | zero => simp at hlen
  | succ f =>
    have hlens : (escapeCodes k.toList ++ '"' :: (':' :: (renderChars v ++ rest))).length ≤ f := by
      simp only [List.length_cons] at hlen
      omega
    have hlenv : (renderChars v ++ rest).length ≤ f := by
      simp only [List.length_cons, List.length_append] at hlen ⊢
      omega
    simp only [parseField,
      parseStrChars_escapeCodes k.toList (':' :: (renderChars v ++ rest)) f hlens,
      hv rest f hlenv hr, String.ofList_toList]
    simp

mutual

/-- ADEQUACY: a rendered value, followed by anything that cannot extend
a decimal run, parses back to exactly that value's number-normal form,
leaving the tail untouched. THE law the obligation rides on. -/
theorem parseValue_renderChars : ∀ (v : Value) (rest : List Char) (f : Nat),
    (renderChars v ++ rest).length ≤ f → NoDigitStart rest →
    parseValue f (renderChars v ++ rest) = some (v.numNorm, rest)
  | .null, rest, f, hlen, _ => by
    cases f with
    | zero => simp [renderChars] at hlen
    | succ f => simp [renderChars, parseValue, matchLit, Value.numNorm]
  | .bool b, rest, f, hlen, _ => by
    cases f with
    | zero => cases b <;> simp [renderChars] at hlen
    | succ f => cases b <;> simp [renderChars, parseValue, matchLit, Value.numNorm]
  | .nat n, rest, f, hlen, hr => by
    obtain ⟨c, t, hct, hdv⟩ := toDigits_head n
    have hsplit : renderChars (.nat n) ++ rest = c :: (t ++ rest) := by
      simp only [renderChars, hct]; simp
    rw [hsplit] at hlen ⊢
    cases f with
    | zero => simp at hlen
    | succ f =>
      have hback : c :: (t ++ rest) = Nat.toDigits 10 n ++ rest := by
        rw [hct]; simp
      simp only [parseValue,
        if_neg (digit_ne 'n' hdv rfl), if_neg (digit_ne 't' hdv rfl),
        if_neg (digit_ne 'f' hdv rfl), if_neg (digit_ne '"' hdv rfl),
        if_neg (digit_ne '-' hdv rfl), if_neg (digit_ne '[' hdv rfl),
        if_neg (digit_ne '{' hdv rfl), hback,
        parseNat_toDigits n rest hr, Option.map_some, Value.numNorm]
  | .int i, rest, f, hlen, hr => by
    by_cases hi : 0 ≤ i
    · obtain ⟨c, t, hct, hdv⟩ := toDigits_head i.toNat
      have hsplit : renderChars (.int i) ++ rest = c :: (t ++ rest) := by
        simp only [renderChars, if_pos hi, hct]; simp
      rw [hsplit] at hlen ⊢
      cases f with
      | zero => simp at hlen
      | succ f =>
        have hback : c :: (t ++ rest) = Nat.toDigits 10 i.toNat ++ rest := by
          rw [hct]; simp
        simp only [parseValue,
          if_neg (digit_ne 'n' hdv rfl), if_neg (digit_ne 't' hdv rfl),
          if_neg (digit_ne 'f' hdv rfl), if_neg (digit_ne '"' hdv rfl),
          if_neg (digit_ne '-' hdv rfl), if_neg (digit_ne '[' hdv rfl),
          if_neg (digit_ne '{' hdv rfl), hback,
          parseNat_toDigits i.toNat rest hr, Option.map_some, Value.numNorm,
          if_pos hi]
    · have hsplit : renderChars (.int i) ++ rest
          = '-' :: (Nat.toDigits 10 (-i).toNat ++ rest) := by
        simp only [renderChars, if_neg hi]; simp
      rw [hsplit] at hlen ⊢
      cases f with
      | zero => simp at hlen
      | succ f =>
        have hnn : (0 : Int) ≤ -i := by omega
        have hcast : ((-i).toNat : Int) = -i := Int.toNat_of_nonneg hnn
        have hne : (-i).toNat ≠ 0 := by omega
        have hval : -(Int.ofNat (-i).toNat) = i := by
          rw [show (Int.ofNat (-i).toNat) = -i from Int.toNat_of_nonneg hnn]
          omega
        simp only [parseValue, parseNat_toDigits (-i).toNat rest hr,
          if_neg hne, hval, Value.numNorm, if_neg hi]
        simp
  | .str s, rest, f, hlen, _ => by
    have hsplit : renderChars (.str s) ++ rest
        = '"' :: (escapeCodes s.toList ++ '"' :: rest) := by
      simp only [renderChars]; simp
    rw [hsplit] at hlen ⊢
    cases f with
    | zero => simp at hlen
    | succ f =>
      have hlen' : (escapeCodes s.toList ++ '"' :: rest).length ≤ f := by
        simp only [List.length_cons] at hlen; omega
      simp only [parseValue,
        parseStrChars_escapeCodes s.toList rest f hlen', Option.map_some,
        String.ofList_toList, Value.numNorm]
      simp
  | .arr [], rest, f, hlen, _ => by
    cases f with
    | zero => simp [renderChars] at hlen
    | succ f =>
      simp [renderChars, parseValue, Value.numNorm, numNormItems]
  | .arr (x :: xs), rest, f, hlen, hr => by
    obtain ⟨d, t, hdt, hd⟩ := renderChars_head x
    have hsplit : renderChars (.arr (x :: xs)) ++ rest
        = '[' :: (d :: (t ++ (itemsChars xs ++ rest))) := by
      simp only [renderChars, hdt]; simp
    have hback : d :: (t ++ (itemsChars xs ++ rest))
        = renderChars x ++ (itemsChars xs ++ rest) := by
      rw [hdt]; simp
    rw [hsplit] at hlen ⊢
    cases f with
    | zero => simp at hlen
    | succ f =>
      have hlenx : (renderChars x ++ (itemsChars xs ++ rest)).length ≤ f := by
        rw [← hback]
        simp only [List.length_cons] at hlen ⊢
        omega
      have hleni : (itemsChars xs ++ rest).length ≤ f := by
        rw [← hback] at hlenx
        simp only [List.length_cons, List.length_append] at hlenx ⊢
        omega
      simp only [parseValue, if_neg hd, hback,
        parseValue_renderChars x (itemsChars xs ++ rest) f hlenx
          (noDigitStart_itemsChars xs rest),
        parseItems_itemsChars xs rest f hleni hr, Option.map_some,
        Value.numNorm, numNormItems]
      simp
  | .obj [], rest, f, hlen, _ => by
    cases f with
    | zero => simp [renderChars] at hlen
    | succ f =>
      simp [renderChars, parseValue, Value.numNorm, numNormFields]
  | .obj ((k, v) :: fs), rest, f, hlen, hr => by
    have hsplit : renderChars (.obj ((k, v) :: fs)) ++ rest
        = '{' :: ('"' :: (escapeCodes k.toList ++ '"' :: ':' ::
            (renderChars v ++ (fieldsChars fs ++ rest)))) := by
      simp only [renderChars, fieldChars]; simp
    have hback : '"' :: (escapeCodes k.toList ++ '"' :: ':' ::
        (renderChars v ++ (fieldsChars fs ++ rest)))
        = fieldChars k (renderChars v) ++ (fieldsChars fs ++ rest) := by
      simp [fieldChars]
    rw [hsplit] at hlen ⊢
    cases f with
    | zero => simp at hlen
    | succ f =>
      have hlenf : (fieldChars k (renderChars v) ++ (fieldsChars fs ++ rest)).length ≤ f := by
        rw [← hback]
        simp only [List.length_cons] at hlen ⊢
        omega
      have hlens : (fieldsChars fs ++ rest).length ≤ f := by
        simp only [fieldChars, List.length_cons, List.length_append] at hlenf ⊢
        omega
      simp only [parseValue, if_neg (by decide : ('"' : Char) ≠ '}'), hback,
        parseField_of k v (fieldsChars fs ++ rest) f
          (parseValue_renderChars v) hlenf (noDigitStart_fieldsChars fs rest),
        parseFields_fieldsChars fs rest f hlens hr, Option.map_some,
        Value.numNorm, numNormFields]
      simp

/-- ADEQUACY for an array's tail. -/
theorem parseItems_itemsChars : ∀ (xs : List Value) (rest : List Char) (f : Nat),
    (itemsChars xs ++ rest).length ≤ f → NoDigitStart rest →
    parseItems f (itemsChars xs ++ rest) = some (numNormItems xs, rest)
  | [], rest, f, hlen, _ => by
    cases f with
    | zero => simp [itemsChars] at hlen
    | succ f => simp [itemsChars, parseItems, numNormItems]
  | x :: xs, rest, f, hlen, hr => by
    have hsplit : itemsChars (x :: xs) ++ rest
        = ',' :: (renderChars x ++ (itemsChars xs ++ rest)) := by
      simp only [itemsChars]; simp
    rw [hsplit] at hlen ⊢
    cases f with
    | zero => simp at hlen
    | succ f =>
      have hlenx : (renderChars x ++ (itemsChars xs ++ rest)).length ≤ f := by
        simp only [List.length_cons] at hlen; omega
      have hleni : (itemsChars xs ++ rest).length ≤ f := by
        simp only [List.length_append] at hlenx ⊢; omega
      simp only [parseItems, if_neg (by decide : (',' : Char) ≠ ']'),
        parseValue_renderChars x (itemsChars xs ++ rest) f hlenx
          (noDigitStart_itemsChars xs rest),
        parseItems_itemsChars xs rest f hleni hr, Option.map_some, numNormItems]
      simp

/-- ADEQUACY for an object's tail. -/
theorem parseFields_fieldsChars :
    ∀ (fs : List (String × Value)) (rest : List Char) (f : Nat),
      (fieldsChars fs ++ rest).length ≤ f → NoDigitStart rest →
      parseFields f (fieldsChars fs ++ rest) = some (numNormFields fs, rest)
  | [], rest, f, hlen, _ => by
    cases f with
    | zero => simp [fieldsChars] at hlen
    | succ f => simp [fieldsChars, parseFields, numNormFields]
  | (k, v) :: fs, rest, f, hlen, hr => by
    have hsplit : fieldsChars ((k, v) :: fs) ++ rest
        = ',' :: (fieldChars k (renderChars v) ++ (fieldsChars fs ++ rest)) := by
      simp only [fieldsChars]; simp
    rw [hsplit] at hlen ⊢
    cases f with
    | zero => simp at hlen
    | succ f =>
      have hlenf : (fieldChars k (renderChars v) ++ (fieldsChars fs ++ rest)).length ≤ f := by
        simp only [List.length_cons] at hlen; omega
      have hlens : (fieldsChars fs ++ rest).length ≤ f := by
        simp only [fieldChars, List.length_cons, List.length_append] at hlenf ⊢
        omega
      simp only [parseFields, if_neg (by decide : (',' : Char) ≠ '}'),
        parseField_of k v (fieldsChars fs ++ rest) f
          (parseValue_renderChars v) hlenf (noDigitStart_fieldsChars fs rest),
        parseFields_fieldsChars fs rest f hlens hr, Option.map_some, numNormFields]
      simp

end

/-! ### The document laws

The adequacy statement at the entry point, where the tail is empty (so
the follow-set premise is vacuous) and the fuel is the input's own
length (so the fuel premise is `≤` on the nose). -/

/-- ADEQUACY, at the door: the canonical rendering of ANY value parses
back to that value's number-normal form. -/
theorem parse_renderPlain (v : Value) : parse (renderPlain v) = some v.numNorm := by
  have h := parseValue_renderChars v [] (renderChars v).length (by simp) trivial
  rw [List.append_nil] at h
  simp only [parse, parseChars, ← renderChars_eq v, h]

/-- On the nose, for the values the parser itself produces. -/
theorem parse_renderPlain' {v : Value} (hv : v.NumNormal) :
    parse (renderPlain v) = some v := by
  rw [parse_renderPlain v, hv]

/-- THE law at the canonical bytes: on canonically spelled values, the
compact canonical rendering parses back to the value's number-normal
form. This is the payload path (`Ast.payload = renderCompact
a.envelope`, `payload_renderPlain`). -/
theorem parse_render {v : Value} (hv : v.Canonical) :
    parse (renderCompact v) = some v.numNorm := by
  rw [renderCompact_eq_renderPlain v hv, parse_renderPlain v]

/-- On the nose, mirroring the `repNorm` treatment on the schema
plane. -/
theorem parse_render' {v : Value} (hc : v.Canonical) (hn : v.NumNormal) :
    parse (renderCompact v) = some v := by
  rw [parse_render hc, hn]

/-! ### `RenderPlainInjective`, DISCHARGED

The obligation falls out of adequacy alone: two values with one
rendering are handed to one parser call, which answers one value.

Worth recording: the obligation as stated carries `Canonical` premises
on both values, and the parser does not need them. The premises were an
artefact of the anticipated proof route (through the sort), not of the
fact — `renderPlain_inj` is the unrestricted statement, and
`renderPlain_injective` is it weakened to the shape the schema plane's
consumers already take as a hypothesis. -/

/-- The canonical rendering is injective up to the number collapse, with
NO canonicality premise. -/
theorem renderPlain_inj {v w : Value} (h : renderPlain v = renderPlain w) :
    v.numNorm = w.numNorm := by
  have hv := parse_renderPlain v
  rw [h, parse_renderPlain w] at hv
  exact (Option.some.inj hv).symm

/-- LAW SM-11: the canonical rendering is injective, proved rather
than assumed.

THE NAMED OBLIGATION, DISCHARGED (`Cas.Values.JsonInj`, ruling 11,
survey blocker B7): bytes determine the canonical value. -/
theorem renderPlain_injective : RenderPlainInjective :=
  fun _ _ _ _ h => renderPlain_inj h

/-- The same at `renderCompact`, which is what the payload bytes are. -/
theorem renderCompact_inj {v w : Value} (hv : v.Canonical) (hw : w.Canonical)
    (h : renderCompact v = renderCompact w) : v.numNorm = w.numNorm :=
  renderCompact_inj_of renderPlain_injective hv hw h

/-! ## Exactness — nothing but the rendering parses

The other half of the contract, and the half that makes `parse` a
CHARACTERIZATION rather than merely a left inverse: whatever the parser
answers, it answers because the input spelled it. Every accepted
document is the canonical rendering of the value answered — so the image
of `parse` is exactly the image of `renderPlain`, and there is no second
spelling anywhere in the grammar.

The parser's answers are always `NumNormal`: it has no arm that produces
a nonnegative `Value.int`. That is the exactness statement's only
qualifier, and it is carried alongside rather than assumed. -/

/-- EXACTNESS of the string reader. -/
theorem parseStrChars_sound : ∀ (f : Nat) (cs k r : List Char),
    parseStrChars f cs = some (k, r) → escapeCodes k ++ '"' :: r = cs
  | 0, _, _, _, h => by simp [parseStrChars] at h
  | _ + 1, [], _, _, h => by simp [parseStrChars] at h
  | f + 1, c :: cs, k, r, h => by
    simp only [parseStrChars] at h
    by_cases hq : c = '"'
    · subst hq
      rw [if_pos rfl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hk, hr⟩ := h
      subst hk; subst hr
      simp [escapeCodes]
    · rw [if_neg hq] at h
      match hu : unescapeCanon (c :: cs) with
      | none => simp [hu] at h
      | some (ch, rest) =>
        simp only [hu] at h
        match hps : parseStrChars f rest with
        | none => simp [hps] at h
        | some (k', r') =>
          simp only [hps] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hk, hr⟩ := h
          subst hk; subst hr
          rw [escapeCodes, List.append_assoc,
            parseStrChars_sound f rest k' r' hps, unescapeCanon_sound hu]

mutual

/-- EXACTNESS: whatever the value parser answers, the input it consumed
is that value's canonical rendering — and the value is number-normal. -/
theorem parseValue_sound : ∀ (f : Nat) (cs : List Char) (v : Value) (r : List Char),
    parseValue f cs = some (v, r) → renderChars v ++ r = cs ∧ v.numNorm = v
  | 0, _, _, _, h => by simp [parseValue] at h
  | _ + 1, [], _, _, h => by simp [parseValue] at h
  | f + 1, c :: cs, v, r, h => by
    simp only [parseValue] at h
    by_cases h1 : c = 'n'
    · subst h1
      rw [if_pos rfl] at h
      match hm : matchLit ['u', 'l', 'l'] cs with
      | none => simp [hm] at h
      | some r' =>
        simp only [hm] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, hr⟩ := h
        subst hv; subst hr
        exact ⟨by rw [← matchLit_sound _ _ _ hm]; rfl, rfl⟩
    rw [if_neg h1] at h
    by_cases h2 : c = 't'
    · subst h2
      rw [if_pos rfl] at h
      match hm : matchLit ['r', 'u', 'e'] cs with
      | none => simp [hm] at h
      | some r' =>
        simp only [hm] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, hr⟩ := h
        subst hv; subst hr
        exact ⟨by rw [← matchLit_sound _ _ _ hm]; rfl, rfl⟩
    rw [if_neg h2] at h
    by_cases h3 : c = 'f'
    · subst h3
      rw [if_pos rfl] at h
      match hm : matchLit ['a', 'l', 's', 'e'] cs with
      | none => simp [hm] at h
      | some r' =>
        simp only [hm] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, hr⟩ := h
        subst hv; subst hr
        exact ⟨by rw [← matchLit_sound _ _ _ hm]; rfl, rfl⟩
    rw [if_neg h3] at h
    by_cases h4 : c = '"'
    · subst h4
      rw [if_pos rfl] at h
      match hs : parseStrChars f cs with
      | none => simp [hs] at h
      | some (k, r') =>
        simp only [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, hr⟩ := h
        subst hv; subst hr
        refine ⟨?_, rfl⟩
        rw [← parseStrChars_sound f cs k r' hs]
        simp [renderChars, String.toList_ofList]
    rw [if_neg h4] at h
    by_cases h5 : c = '-'
    · subst h5
      rw [if_pos rfl] at h
      match hn : parseNat cs with
      | none => simp [hn] at h
      | some (n, r') =>
        simp only [hn] at h
        by_cases hz : n = 0
        · simp [hz] at h
        · rw [if_neg hz] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hv, hr⟩ := h
          subst hv; subst hr
          have hpos : 0 < n := Nat.pos_of_ne_zero hz
          have hcast : (Int.ofNat n) = (n : Int) := rfl
          have hneg : ¬ (0 : Int) ≤ -(Int.ofNat n) := by rw [hcast]; omega
          have htn : (-(-(Int.ofNat n))).toNat = n := by rw [hcast]; omega
          refine ⟨?_, by simp only [Value.numNorm, if_neg hneg]⟩
          simp only [renderChars, if_neg hneg, htn, List.cons_append,
            (parseNat_sound hn).1]
    rw [if_neg h5] at h
    by_cases h6 : c = '['
    · subst h6
      rw [if_pos rfl] at h
      cases cs with
      | nil => simp at h
      | cons d cs' =>
        dsimp only at h
        by_cases hd : d = ']'
        · subst hd
          rw [if_pos rfl] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hv, hr⟩ := h
          subst hv; subst hr
          exact ⟨rfl, rfl⟩
        · rw [if_neg hd] at h
          match hx : parseValue f (d :: cs') with
          | none => simp [hx] at h
          | some (x, r1) =>
            simp only [hx] at h
            match hxs : parseItems f r1 with
            | none => simp [hxs] at h
            | some (xs, r2) =>
              simp only [hxs] at h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hv, hr⟩ := h
              subst hv; subst hr
              obtain ⟨hx1, hx2⟩ := parseValue_sound f (d :: cs') x r1 hx
              obtain ⟨hxs1, hxs2⟩ := parseItems_sound f r1 xs r2 hxs
              refine ⟨?_, by simp only [Value.numNorm, numNormItems, hx2, hxs2]⟩
              simp only [renderChars, List.cons_append, List.append_assoc,
                hxs1, hx1]
    rw [if_neg h6] at h
    by_cases h7 : c = '{'
    · subst h7
      rw [if_pos rfl] at h
      cases cs with
      | nil => simp at h
      | cons d cs' =>
        dsimp only at h
        by_cases hd : d = '}'
        · subst hd
          rw [if_pos rfl] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hv, hr⟩ := h
          subst hv; subst hr
          exact ⟨rfl, rfl⟩
        · rw [if_neg hd] at h
          match hkv : parseField f (d :: cs') with
          | none => simp [hkv] at h
          | some (kv, r1) =>
            simp only [hkv] at h
            match hfs : parseFields f r1 with
            | none => simp [hfs] at h
            | some (fs, r2) =>
              simp only [hfs] at h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hv, hr⟩ := h
              subst hv; subst hr
              obtain ⟨hk1, hk2⟩ := parseField_sound f (d :: cs') kv r1 hkv
              obtain ⟨hfs1, hfs2⟩ := parseFields_sound f r1 fs r2 hfs
              refine ⟨?_, ?_⟩
              · simp only [renderChars, List.cons_append, List.append_assoc,
                  hfs1, hk1]
              · simp only [Value.numNorm, numNormFields, hfs2]
                rw [show ((kv.1, kv.2.numNorm) : String × Value) = kv by
                  rw [hk2]]
    · rw [if_neg h7] at h
      match hn : parseNat (c :: cs) with
      | none => simp [hn] at h
      | some (n, r') =>
        simp only [hn] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hv, hr⟩ := h
        subst hv; subst hr
        exact ⟨(parseNat_sound hn).1, rfl⟩

/-- EXACTNESS for an array's tail. -/
theorem parseItems_sound : ∀ (f : Nat) (cs : List Char) (xs : List Value) (r : List Char),
    parseItems f cs = some (xs, r) → itemsChars xs ++ r = cs ∧ numNormItems xs = xs
  | 0, _, _, _, h => by simp [parseItems] at h
  | _ + 1, [], _, _, h => by simp [parseItems] at h
  | f + 1, c :: cs, xs, r, h => by
    simp only [parseItems] at h
    by_cases h1 : c = ']'
    · subst h1
      rw [if_pos rfl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hv, hr⟩ := h
      subst hv; subst hr
      exact ⟨rfl, rfl⟩
    rw [if_neg h1] at h
    by_cases h2 : c = ','
    · subst h2
      rw [if_pos rfl] at h
      match hx : parseValue f cs with
      | none => simp [hx] at h
      | some (x, r1) =>
        simp only [hx] at h
        match hxs : parseItems f r1 with
        | none => simp [hxs] at h
        | some (ys, r2) =>
          simp only [hxs] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hv, hr⟩ := h
          subst hv; subst hr
          obtain ⟨hx1, hx2⟩ := parseValue_sound f cs x r1 hx
          obtain ⟨hxs1, hxs2⟩ := parseItems_sound f r1 ys r2 hxs
          exact ⟨by simp only [itemsChars, List.cons_append, List.append_assoc,
            hxs1, hx1], by simp only [numNormItems, hx2, hxs2]⟩
    · rw [if_neg h2] at h; simp at h

/-- EXACTNESS for one object field. -/
theorem parseField_sound :
    ∀ (f : Nat) (cs : List Char) (kv : String × Value) (r : List Char),
      parseField f cs = some (kv, r) →
        fieldChars kv.1 (renderChars kv.2) ++ r = cs ∧ kv.2.numNorm = kv.2
  | 0, _, _, _, h => by simp [parseField] at h
  | _ + 1, [], _, _, h => by simp [parseField] at h
  | f + 1, c :: cs, kv, r, h => by
    simp only [parseField] at h
    by_cases h1 : c = '"'
    · subst h1
      rw [if_pos rfl] at h
      match hs : parseStrChars f cs with
      | none => simp [hs] at h
      | some (k, []) => simp [hs] at h
      | some (k, d :: r1) =>
        simp only [hs] at h
        by_cases hd : d = ':'
        · subst hd
          rw [if_pos rfl] at h
          match hv : parseValue f r1 with
          | none => simp [hv] at h
          | some (w, r2) =>
            simp only [hv] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hkv, hr⟩ := h
            subst hkv; subst hr
            obtain ⟨hv1, hv2⟩ := parseValue_sound f r1 w r2 hv
            refine ⟨?_, hv2⟩
            simp only [fieldChars, String.toList_ofList, List.cons_append,
              List.append_assoc, hv1]
            rw [← parseStrChars_sound f cs k (':' :: r1) hs]
        · rw [if_neg hd] at h; simp at h
    · rw [if_neg h1] at h; simp at h

/-- EXACTNESS for an object's tail. -/
theorem parseFields_sound :
    ∀ (f : Nat) (cs : List Char) (fs : List (String × Value)) (r : List Char),
      parseFields f cs = some (fs, r) → fieldsChars fs ++ r = cs ∧ numNormFields fs = fs
  | 0, _, _, _, h => by simp [parseFields] at h
  | _ + 1, [], _, _, h => by simp [parseFields] at h
  | f + 1, c :: cs, fs, r, h => by
    simp only [parseFields] at h
    by_cases h1 : c = '}'
    · subst h1
      rw [if_pos rfl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hv, hr⟩ := h
      subst hv; subst hr
      exact ⟨rfl, rfl⟩
    rw [if_neg h1] at h
    by_cases h2 : c = ','
    · subst h2
      rw [if_pos rfl] at h
      match hkv : parseField f cs with
      | none => simp [hkv] at h
      | some (kv, r1) =>
        simp only [hkv] at h
        match hfs : parseFields f r1 with
        | none => simp [hfs] at h
        | some (gs, r2) =>
          simp only [hfs] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hv, hr⟩ := h
          subst hv; subst hr
          obtain ⟨hk1, hk2⟩ := parseField_sound f cs kv r1 hkv
          obtain ⟨hfs1, hfs2⟩ := parseFields_sound f r1 gs r2 hfs
          refine ⟨?_, ?_⟩
          · simp only [fieldsChars, List.cons_append, List.append_assoc, hfs1, hk1]
          · simp only [numNormFields, hfs2]
            rw [show ((kv.1, kv.2.numNorm) : String × Value) = kv by rw [hk2]]
    · rw [if_neg h2] at h; simp at h

end

/-- EXACTNESS at the door: every document `parse` accepts IS the
canonical rendering of the value it answers, and that value is
number-normal. With `parse_renderPlain`, the image of `parse` is exactly
the image of `renderPlain`. -/
theorem parse_sound {s : String} {v : Value} (h : parse s = some v) :
    renderPlain v = s ∧ v.NumNormal := by
  simp only [parse, parseChars] at h
  match hp : parseValue s.toList.length s.toList with
  | none => simp [hp] at h
  | some (w, []) =>
    simp only [hp] at h
    obtain ⟨h1, h2⟩ := parseValue_sound _ _ _ _ hp
    have hw : w = v := Option.some.inj h
    subst hw
    refine ⟨String.toList_inj.mp ?_, h2⟩
    rw [← renderChars_eq w, ← h1]
    simp
  | some (w, _ :: _) => simp [hp] at h

/-- EXACTNESS at the canonical bytes. The premise is the one thing the
parser deliberately does not check: it answers objects in the order the
bytes carry them, so an accepted document is `renderPlain`'s image
always, and `renderCompact`'s image exactly when the answer is
canonically spelled. That is the gate's question, and this is where it
is paid. -/
theorem parse_sound_compact {s : String} {v : Value} (h : parse s = some v)
    (hc : v.Canonical) : renderCompact v = s := by
  rw [renderCompact_eq_renderPlain v hc]
  exact (parse_sound h).1

/-! ## The acceptance contract, worked at elaboration

`Value` carries no `BEq`, so the answers are compared through the
rendering — which is exactly the identity that matters here. The
refusals are the point: every one of them is a spelling a tolerant JSON
reader would accept and the canonical encoding never emits. -/

private def reshow : Option Value → Option String
  | some v => some (renderPlain v)
  | none => none

-- ACCEPTED: the canonical spellings, round-tripping on the nose.
#guard reshow (parse "null") == some "null"
#guard reshow (parse "true") == some "true"
#guard reshow (parse "false") == some "false"
#guard reshow (parse "0") == some "0"
#guard reshow (parse "-3") == some "-3"
#guard reshow (parse "[]") == some "[]"
#guard reshow (parse "{}") == some "{}"
#guard reshow (parse "{\"a\":[0,12,-3,\"hi\\n\\\"x\\\\\",true,null],\"b\":{}}")
  == some "{\"a\":[0,12,-3,\"hi\\n\\\"x\\\\\",true,null],\"b\":{}}"
#guard reshow (parse "\"\\u0001\\u001f\"") == some "\"\\u0001\\u001f\""
#guard reshow (parse "\"\\b\\t\\n\\f\\r\"") == some "\"\\b\\t\\n\\f\\r\""
#guard reshow (parse "\"A\"") == some "\"A\""

-- ONE SPELLING PER STRING: `unescapeOne` alone would read all three of
-- these, and the re-encoding check in `unescapeCanon` is what refuses
-- them. Without it `parse_sound` would be false.
#guard reshow (parse "\"\\u0041\"") == none  -- the canonical spelling is `A`
#guard reshow (parse "\"\\u0008\"") == none  -- the canonical spelling is `\b`
#guard reshow (parse "\"\\u001F\"") == none  -- the escape emits lowercase hex

-- SORTED KEYS ARE THE GATE'S QUESTION: an unsorted object is a value
-- with a rendering, so the parser answers it as spelled.
#guard reshow (parse "{\"b\":1,\"a\":2}") == some "{\"b\":1,\"a\":2}"

-- REFUSED: whitespace anywhere, alternate number spellings, alternate
-- string spellings, trailing input, trailing commas, truncation.
#guard reshow (parse "  1") == none
#guard reshow (parse "1 ") == none
#guard reshow (parse "[1, 2]") == none
#guard reshow (parse "{\"a\": 1}") == none
#guard reshow (parse "01") == none
#guard reshow (parse "-0") == none
#guard reshow (parse "+1") == none
#guard reshow (parse "1.0") == none
#guard reshow (parse "1e5") == none
#guard reshow (parse "'x'") == none
#guard reshow (parse "\"\\x\"") == none
#guard reshow (parse "[1,2,]") == none
#guard reshow (parse "nul") == none
#guard reshow (parse "truex") == none
#guard reshow (parse "") == none
#guard reshow (parse "[1") == none

end Cas.Json
