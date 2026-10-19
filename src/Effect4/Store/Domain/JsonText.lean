module

public import Effect4.Data.NatJson
public import Effect4.Data.Located
public import Effect4.Store.Carrier.Utf8

/-!
# Store.JsonText — the profile's JSON text, read

Owner: the one reader of JSON text into the profile's tree (`Effect4.NatJson`). It reads the
text's bytes as natural numbers, as `NatJson.render` writes them, and it refuses at a byte offset
with what it expects there. Both session drivers read their text through it: Lean's driver
(`tools/Drivers/Session.lean`) and the native shell, where it is lowered to OCaml
(`ocaml/engine/kit/kit.ml`).

**The grammar** is RFC 8259's, with I-JSON's strings (RFC 7493 §2.1: no lone surrogate):
- white space is space, tab, line feed and carriage return, and nothing else: no comment;
- a number is an optional `-`, then `0` or a digit from 1 to 9 and more digits, then an
  optional fraction and an optional exponent;
- a string's content is UTF-8 (`Store.decodeString`), a control byte stands escaped, and the
  escapes are `\" \\ \/ \b \f \n \r \t` and `\u` with four hexadecimal digits, where a high
  surrogate is followed by an escaped low one;
- the literals `true`, `false` and `null`, arrays and objects.

**What the profile decides here**, once for both drivers:
- a number that is no natural written plainly (`-0`, `1e0`, `1.5`, `-1`) is a `numeral` with its
  text, and every reader refuses it at its place (`Store/Domain/ShapeJson.lean`);
- a natural of more than `maxDigits` digits is a `numeral` too, so no host integer overflows,
  and the reader refuses it at its place as outside the profile;
- a key written twice stays in its object, in order, and the reader refuses it at its object;
- a comment, an unquoted key and a control byte inside a string are refused here, at their byte.

**The reader** (`readText`) holds an explicit stack: the mode says what it expects next, and the
context (`TextCtx`) where the value it reads goes. Every step takes a byte at least, so it recurses
on the text's length and no budget bounds it.

**The law** (`parse_render`, `Laws/Store/JsonText.lean`): within the profile, reading a tree's
compact text gives the tree back.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.NatJson

/-- **What the text reader expects** where it refuses. -/
inductive TextReason where
  /-- A value: an object, an array, a string, a number, `true`, `false` or `null`. -/
  | value
  /-- A comma, or the close of the open array or object. -/
  | separator
  /-- An object's key: a string. -/
  | key
  /-- The colon after an object's key. -/
  | colon
  /-- A digit of a number. -/
  | digit
  /-- No digit after a number's leading zero. -/
  | leadingZero
  /-- A string's closing quote. -/
  | quote
  /-- An escape: `"`, `\`, `/`, `b`, `f`, `n`, `r`, `t`, or `u` and four hexadecimal digits. -/
  | escape
  /-- No control byte, below 32, inside a string: it stands escaped. -/
  | control
  /-- A surrogate pair: a high surrogate's escape, then a low one's. -/
  | surrogate
  /-- A string's content as UTF-8. -/
  | utf8
  /-- The end of the text, after its one value. -/
  | end_
deriving DecidableEq

/-- **A refusal of JSON text**: what the reader expects, at a byte offset. -/
abbrev TextRefusal : Type := Located Nat TextReason

/-- Where the reader stops inside the text: what it expects, and the text from that byte on.
`parse` turns the text into its offset. -/
abbrev TextStop : Type := TextReason × List Nat

/-! ## Bytes, white space, digits -/

/-- White space between tokens: space, tab, line feed, carriage return. -/
def isSpace (c : Nat) : Bool := c == 32 || c == 9 || c == 10 || c == 13

/-- The text from its first byte that is no white space. -/
def skipSpace : List Nat → List Nat
  | [] => []
  | c :: rest => if isSpace c then skipSpace rest else c :: rest

/-- Whether a byte is a decimal digit. -/
def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- The digits at the head of a text, and the rest. -/
def spanDigits : List Nat → List Nat × List Nat
  | [] => ([], [])
  | c :: rest =>
    if isDigit c then
      match spanDigits rest with
      | (ds, r) => (c :: ds, r)
    else ([], c :: rest)

/-! ## Numbers -/

/-- One digit at least, and the rest; or where a digit was expected. -/
def digits1 (bs : List Nat) : Except TextStop (List Nat × List Nat) :=
  match spanDigits bs with
  | ([], _) => .error (.digit, bs)
  | (d :: ds, r) => .ok (d :: ds, r)

/-- A number's exponent, if it has one: `e` or `E`, a sign or none, and digits. -/
def exponentPart : List Nat → Except TextStop (List Nat × List Nat)
  | [] => .ok ([], [])
  | e :: rest =>
    if e = 101 ∨ e = 69 then
      match rest with
      | [] => .error (.digit, [])
      | s :: rest' =>
        if s = 43 ∨ s = 45 then (digits1 rest').map fun (ds, r) => (e :: s :: ds, r)
        else (digits1 (s :: rest')).map fun (ds, r) => (e :: ds, r)
    else .ok ([], e :: rest)

/-- A number's fraction, if it has one (`.` and digits), then its exponent. -/
def fractionPart (bs : List Nat) : Except TextStop (List Nat × List Nat) :=
  match bs with
  | 46 :: rest =>
    (digits1 rest).bind fun (ds, r) => (exponentPart r).map fun (es, r') => (46 :: ds ++ es, r')
  | _ => exponentPart bs

/-- A number's text after its sign: `0`, which no digit follows, or a digit from 1 to 9 and more
digits; then its fraction and its exponent. -/
def unsignedText (bs : List Nat) : Except TextStop (List Nat × List Nat) :=
  match bs with
  | 48 :: rest =>
    match rest with
    | c :: _ =>
      if isDigit c then .error (.leadingZero, rest)
      else (fractionPart rest).map fun (fe, r) => (48 :: fe, r)
    | [] => .ok ([48], [])
  | _ => (digits1 bs).bind fun (ds, r) => (fractionPart r).map fun (fe, r') => (ds ++ fe, r')

/-- **A number's text** at the head of a text (RFC 8259's `number`), and the rest. -/
def numberText (bs : List Nat) : Except TextStop (List Nat × List Nat) :=
  match bs with
  | 45 :: rest => (unsignedText rest).map fun (t, r) => (45 :: t, r)
  | _ => unsignedText bs

/-- The natural a text of digits spells. -/
def digitsValue (ds : List Nat) : Nat := ds.foldl (fun acc c => acc * 10 + (c - 48)) 0

/-- **The most digits a natural of the tree takes**: 16. Every natural the tree holds from text
is below 10^16, which a host's 63-bit integer holds, and `NatJson.limit` is below it. -/
def maxDigits : Nat := 16

/-- **A number of the tree** from its text: a natural where the text is digits only, at most
`maxDigits` of them; otherwise a numeral with its text, which every reader refuses at its place. -/
def numberOf (text : List Nat) : NatJson :=
  if text.all isDigit && decide (text.length ≤ maxDigits) then .nat (digitsValue text)
  else .numeral (String.ofList (text.map Char.ofNat))

/-! ## Strings -/

/-- A hexadecimal digit's value, in either case. -/
def hexValue (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else if 65 ≤ c ∧ c ≤ 70 then some (c - 55)
  else none

/-- Four hexadecimal digits' value. -/
def hex4 (a b c d : Nat) : Option Nat :=
  match hexValue a, hexValue b, hexValue c, hexValue d with
  | some a, some b, some c, some d => some (((a * 16 + b) * 16 + c) * 16 + d)
  | _, _, _, _ => none

/-- A code point's UTF-8 bytes. -/
def utf8Of (cp : Nat) : List Nat :=
  if cp < 0x80 then [cp]
  else if cp < 0x800 then [0xC0 + cp / 64, 0x80 + cp % 64]
  else if cp < 0x10000 then [0xE0 + cp / 4096, 0x80 + cp / 64 % 64, 0x80 + cp % 64]
  else [0xF0 + cp / 262144, 0x80 + cp / 4096 % 64, 0x80 + cp / 64 % 64, 0x80 + cp % 64]

/-- **A string's content bytes**, from after its opening quote: each byte as it stands or as its
escape spells it, newest first in `acc`; and the text after the closing quote. -/
def stringBytes : List Nat → List Nat → Except TextStop (List Nat × List Nat)
  | [], _ => .error (.quote, [])
  | c :: rest, acc =>
    if c = 34 then .ok (acc.reverse, rest)
    else if c = 92 then
      match rest with
      | [] => .error (.escape, [])
      | e :: rest' =>
        if e = 34 then stringBytes rest' (34 :: acc)
        else if e = 92 then stringBytes rest' (92 :: acc)
        else if e = 47 then stringBytes rest' (47 :: acc)
        else if e = 98 then stringBytes rest' (8 :: acc)
        else if e = 102 then stringBytes rest' (12 :: acc)
        else if e = 110 then stringBytes rest' (10 :: acc)
        else if e = 114 then stringBytes rest' (13 :: acc)
        else if e = 116 then stringBytes rest' (9 :: acc)
        else if e = 117 then
          match rest' with
          | a :: b :: c' :: d :: rest'' =>
            match hex4 a b c' d with
            | none => .error (.escape, rest)
            | some cp =>
              if 0xDC00 ≤ cp ∧ cp < 0xE000 then .error (.surrogate, c :: rest)
              else if 0xD800 ≤ cp ∧ cp < 0xDC00 then
                match rest'' with
                | 92 :: 117 :: a' :: b' :: c'' :: d' :: rest''' =>
                  match hex4 a' b' c'' d' with
                  | some lo =>
                    if 0xDC00 ≤ lo ∧ lo < 0xE000 then
                      stringBytes rest'''
                        ((utf8Of (0x10000 + (cp - 0xD800) * 1024 + (lo - 0xDC00))).reverse ++ acc)
                    else .error (.surrogate, rest'')
                  | none => .error (.escape, rest'')
                | _ => .error (.surrogate, rest'')
              else stringBytes rest'' ((utf8Of cp).reverse ++ acc)
          | _ => .error (.escape, rest)
        else .error (.escape, rest)
    else if c < 32 then .error (.control, c :: rest)
    else stringBytes rest (c :: acc)

/-- **A string literal** from after its opening quote: its content as a string, and the text
after it. Content that is no UTF-8 is refused at the byte after the opening quote. -/
def stringText (bs : List Nat) : Except TextStop (String × List Nat) :=
  match stringBytes bs [] with
  | .error e => .error e
  | .ok (content, rest) =>
    match Store.decodeString (content.map UInt8.ofNat) with
    | some s => .ok (s, rest)
    | none => .error (.utf8, bs)

/-! ## The reader -/

/-- **Where a value being read goes**: it is the text's one value, an open array's next item, or
the value of a key of an open object. Items and entries are newest first, and each container
keeps the context it goes to. -/
inductive TextCtx where
  | top
  | item (items : List NatJson) (up : TextCtx)
  | member (entries : List (String × NatJson)) (key : String) (up : TextCtx)

/-- **What the reader expects next.** -/
inductive TextMode where
  /-- A value, which goes to the context. -/
  | value (ctx : TextCtx)
  /-- After `[`: a value, or `]`. -/
  | firstItem (ctx : TextCtx)
  /-- After `{`: a key, or `}`. -/
  | firstKey (ctx : TextCtx)
  /-- After a comma in an object: a key. -/
  | key (entries : List (String × NatJson)) (ctx : TextCtx)
  /-- After a key: a colon. -/
  | colon (entries : List (String × NatJson)) (key : String) (ctx : TextCtx)
  /-- After an array's item: a comma, or `]`. -/
  | afterItem (items : List NatJson) (ctx : TextCtx)
  /-- After an object's member: a comma, or `}`. -/
  | afterMember (entries : List (String × NatJson)) (ctx : TextCtx)
  /-- The text's value, read: only white space may follow. -/
  | done (v : NatJson)

/-- **A value read goes to its context**: it is the text's value, an array's next item, or the
value of the key read before it. -/
def TextCtx.put (v : NatJson) : TextCtx → TextMode
  | .top => .done v
  | .item items up => .afterItem (v :: items) up
  | .member entries key up => .afterMember ((key, v) :: entries) up

/-- **The start of a value** at its first byte `c`: a scalar read whole and put to the context,
or an array or an object opened. The next mode, and the text after what it read. -/
def startValue (ctx : TextCtx) (c : Nat) (rest : List Nat) : Except TextStop (TextMode × List Nat) :=
  if c = 123 then .ok (.firstKey ctx, rest)
  else if c = 91 then .ok (.firstItem ctx, rest)
  else if c = 34 then (stringText rest).map fun (s, r) => (ctx.put (.str s), r)
  else if c = 116 then
    match rest with
    | 114 :: 117 :: 101 :: r => .ok (ctx.put (.bool true), r)
    | _ => .error (.value, c :: rest)
  else if c = 102 then
    match rest with
    | 97 :: 108 :: 115 :: 101 :: r => .ok (ctx.put (.bool false), r)
    | _ => .error (.value, c :: rest)
  else if c = 110 then
    match rest with
    | 117 :: 108 :: 108 :: r => .ok (ctx.put .null, r)
    | _ => .error (.value, c :: rest)
  else if c = 45 ∨ isDigit c then
    (numberText (c :: rest)).map fun (text, r) => (ctx.put (numberOf text), r)
  else .error (.value, c :: rest)

/-! ### The termination steps -/

/-- A mapped `Except` that answers read its argument. A step of the length lemmas below; the same
fact stands in `Laws/Store/ShapeRead.lean` and, for `bind`, in `Store/Domain/Word.lean`. -/
private theorem except_map_ok {ε α β : Type} {e : Except ε α} {f : α → β} {b : β}
    (h : e.map f = .ok b) : ∃ a, e = .ok a ∧ f a = b := by
  cases e with
  | error x => cases h
  | ok a =>
    cases h
    exact ⟨a, rfl, rfl⟩

/-- A bound `Except` that answers read its first step. A step of the length lemmas below. -/
private theorem except_bind_ok {ε α β : Type} {e : Except ε α} {f : α → Except ε β} {b : β}
    (h : e.bind f = .ok b) : ∃ a, e = .ok a ∧ f a = .ok b := by
  cases e with
  | error x => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem skipSpace_length : ∀ bs : List Nat, (skipSpace bs).length ≤ bs.length
  | [] => Nat.le_refl _
  | c :: rest => by
    unfold skipSpace
    split
    · have := skipSpace_length rest
      simp only [List.length_cons]
      omega
    · exact Nat.le_refl _

theorem spanDigits_split : ∀ bs : List Nat, (spanDigits bs).1 ++ (spanDigits bs).2 = bs
  | [] => rfl
  | c :: rest => by
    unfold spanDigits
    split
    · have := spanDigits_split rest
      revert this
      cases spanDigits rest
      intro h
      simp only [List.cons_append, h]
    · rfl

theorem digits1_split {bs ds r : List Nat} (h : digits1 bs = .ok (ds, r)) :
    ds ++ r = bs ∧ ds ≠ [] := by
  unfold digits1 at h
  have hs := spanDigits_split bs
  split at h
  · cases h
  · rename_i d ds' r' heq
    cases h
    rw [heq] at hs
    exact ⟨hs, List.cons_ne_nil _ _⟩

theorem exponentPart_split {bs es r : List Nat} (h : exponentPart bs = .ok (es, r)) :
    es ++ r = bs := by
  unfold exponentPart at h
  split at h
  · cases h
    rfl
  · rename_i e rest
    split at h
    · split at h
      · cases h
      · rename_i s rest'
        split at h
        · obtain ⟨⟨ds, r'⟩, hd, he⟩ := except_map_ok h
          cases he
          rw [List.cons_append, List.cons_append, (digits1_split hd).1]
        · obtain ⟨⟨ds, r'⟩, hd, he⟩ := except_map_ok h
          cases he
          rw [List.cons_append, (digits1_split hd).1]
    · cases h
      rfl

theorem fractionPart_split {bs fe r : List Nat} (h : fractionPart bs = .ok (fe, r)) :
    fe ++ r = bs := by
  unfold fractionPart at h
  split at h
  · rename_i rest
    obtain ⟨⟨ds, r1⟩, hd, h2⟩ := except_bind_ok h
    obtain ⟨⟨es, r2⟩, he, h3⟩ := except_map_ok h2
    cases h3
    simp only [List.cons_append, List.append_assoc, exponentPart_split he, (digits1_split hd).1]
  · exact exponentPart_split h

theorem unsignedText_split {bs t r : List Nat} (h : unsignedText bs = .ok (t, r)) :
    t ++ r = bs ∧ t ≠ [] := by
  unfold unsignedText at h
  split at h
  · rename_i rest
    split at h
    · rename_i c rest'
      split at h
      · cases h
      · obtain ⟨⟨fe, r1⟩, hf, h2⟩ := except_map_ok h
        cases h2
        exact ⟨by rw [List.cons_append, fractionPart_split hf], List.cons_ne_nil _ _⟩
    · cases h
      exact ⟨rfl, List.cons_ne_nil _ _⟩
  · obtain ⟨⟨ds, r1⟩, hd, h2⟩ := except_bind_ok h
    obtain ⟨⟨fe, r2⟩, hf, h3⟩ := except_map_ok h2
    cases h3
    obtain ⟨hds, hne⟩ := digits1_split hd
    refine ⟨?_, ?_⟩
    · rw [List.append_assoc, fractionPart_split hf, hds]
    · cases ds with
      | nil => exact absurd rfl hne
      | cons d ds' => exact List.cons_ne_nil _ _

theorem numberText_split {bs t r : List Nat} (h : numberText bs = .ok (t, r)) :
    t ++ r = bs ∧ t ≠ [] := by
  unfold numberText at h
  split at h
  · rename_i rest
    obtain ⟨⟨t', r'⟩, hu, h2⟩ := except_map_ok h
    cases h2
    exact ⟨by rw [List.cons_append, (unsignedText_split hu).1], List.cons_ne_nil _ _⟩
  · exact unsignedText_split h

/-- A number's text is shorter than what it was read from. A termination step of `readText`. -/
theorem numberText_length {bs t r : List Nat} (h : numberText bs = .ok (t, r)) :
    r.length < bs.length := by
  obtain ⟨hsplit, hne⟩ := numberText_split h
  rw [← hsplit, List.length_append]
  cases t with
  | nil => exact absurd rfl hne
  | cons _ _ =>
    simp only [List.length_cons]
    omega

/-- A string's rest is shorter than what it was read from. A termination step of `readText`. -/
theorem stringBytes_length {bs acc content r : List Nat}
    (h : stringBytes bs acc = .ok (content, r)) : r.length < bs.length := by
  fun_induction stringBytes bs acc
  next => cases h
  next =>
    cases h
    simp only [List.length_cons]
    omega
  next => cases h
  next ih =>
    have := ih h
    simp only [List.length_cons]
    omega
  next ih =>
    have := ih h
    simp only [List.length_cons]
    omega
  next ih =>
    have := ih h
    simp only [List.length_cons]
    omega
  next ih =>
    have := ih h
    simp only [List.length_cons]
    omega
  next ih =>
    have := ih h
    simp only [List.length_cons]
    omega
  next ih =>
    have := ih h
    simp only [List.length_cons]
    omega
  next ih =>
    have := ih h
    simp only [List.length_cons]
    omega
  next ih =>
    have := ih h
    simp only [List.length_cons]
    omega
  next => cases h
  next => cases h
  next ih =>
    have := ih h
    simp only [List.length_cons]
    omega
  next => cases h
  next => cases h
  next => cases h
  next ih =>
    have := ih h
    simp only [List.length_cons]
    omega
  next => cases h
  next => cases h
  next => cases h
  next ih =>
    have := ih h
    simp only [List.length_cons]
    omega

/-- A string literal's rest is shorter than what it was read from. A termination step of
`readText`. -/
theorem stringText_length {bs r : List Nat} {s : String} (h : stringText bs = .ok (s, r)) :
    r.length < bs.length := by
  unfold stringText at h
  split at h
  · cases h
  · rename_i content rest hb
    split at h
    · cases h
      exact stringBytes_length hb
    · cases h

/-- What the start of a value leaves is no longer than the text after its first byte. A
termination step of `readText`. -/
theorem startValue_length {ctx : TextCtx} {c : Nat} {rest r : List Nat} {m : TextMode}
    (h : startValue ctx c rest = .ok (m, r)) : r.length ≤ rest.length := by
  unfold startValue at h
  split at h
  · cases h
    exact Nat.le_refl _
  · split at h
    · cases h
      exact Nat.le_refl _
    · split at h
      · obtain ⟨⟨s, r'⟩, hs, he⟩ := except_map_ok h
        cases he
        exact Nat.le_of_lt (stringText_length hs)
      · split at h
        · split at h
          · cases h
            simp only [List.length_cons]
            omega
          · cases h
        · split at h
          · split at h
            · cases h
              simp only [List.length_cons]
              omega
            · cases h
          · split at h
            · split at h
              · cases h
                simp only [List.length_cons]
                omega
              · cases h
            · split at h
              · obtain ⟨⟨text, r'⟩, hn, he⟩ := except_map_ok h
                cases he
                have := numberText_length hn
                simp only [List.length_cons] at this
                omega
              · cases h

/-- The text after a byte the white space left is shorter than the text. -/
theorem lt_of_skipSpace {bs rest : List Nat} {c : Nat} (h : skipSpace bs = c :: rest) :
    rest.length < bs.length := by
  have := skipSpace_length bs
  rw [h, List.length_cons] at this
  omega

/-! ### The reader -/

/-- **The end of the text** in a mode: the value read, or what the mode still expects. -/
def endOf : TextMode → Except TextStop NatJson
  | .done v => .ok v
  | .value _ => .error (.value, [])
  | .firstItem _ => .error (.value, [])
  | .firstKey _ => .error (.key, [])
  | .key _ _ => .error (.key, [])
  | .colon _ _ _ => .error (.colon, [])
  | .afterItem _ _ => .error (.separator, [])
  | .afterMember _ _ => .error (.separator, [])

/-- **The reader**: the mode, over the text from its next byte. Each step takes one byte at least
(`lt_of_skipSpace`, `startValue_length`, `stringText_length`), so it recurses on the text's length,
and no budget bounds it. -/
def readText (bs : List Nat) (m : TextMode) : Except TextStop NatJson :=
  match _h : skipSpace bs with
  | [] => endOf m
  | c :: rest =>
    match m with
    | .done _ => .error (.end_, c :: rest)
    | .value ctx =>
      match _hv : startValue ctx c rest with
      | .ok (m', r) => readText r m'
      | .error e => .error e
    | .firstItem ctx =>
      if c = 93 then readText rest (ctx.put (.arr []))
      else
        match _hv : startValue (.item [] ctx) c rest with
        | .ok (m', r) => readText r m'
        | .error e => .error e
    | .firstKey ctx =>
      if c = 125 then readText rest (ctx.put (.obj []))
      else if c = 34 then
        match _hk : stringText rest with
        | .ok (k, r) => readText r (.colon [] k ctx)
        | .error e => .error e
      else .error (.key, c :: rest)
    | .key entries ctx =>
      if c = 34 then
        match _hk : stringText rest with
        | .ok (k, r) => readText r (.colon entries k ctx)
        | .error e => .error e
      else .error (.key, c :: rest)
    | .colon entries k ctx =>
      if c = 58 then readText rest (.value (.member entries k ctx))
      else .error (.colon, c :: rest)
    | .afterItem items ctx =>
      if c = 44 then readText rest (.value (.item items ctx))
      else if c = 93 then readText rest (ctx.put (.arr items.reverse))
      else .error (.separator, c :: rest)
    | .afterMember entries ctx =>
      if c = 44 then readText rest (.key entries ctx)
      else if c = 125 then readText rest (ctx.put (.obj entries.reverse))
      else .error (.separator, c :: rest)
termination_by bs.length
decreasing_by
  · exact Nat.lt_of_le_of_lt (startValue_length _hv) (lt_of_skipSpace _h)
  · exact lt_of_skipSpace _h
  · exact Nat.lt_of_le_of_lt (startValue_length _hv) (lt_of_skipSpace _h)
  · exact lt_of_skipSpace _h
  · exact Nat.lt_trans (stringText_length _hk) (lt_of_skipSpace _h)
  · exact Nat.lt_trans (stringText_length _hk) (lt_of_skipSpace _h)
  · exact lt_of_skipSpace _h
  · exact lt_of_skipSpace _h
  · exact lt_of_skipSpace _h
  · exact lt_of_skipSpace _h
  · exact lt_of_skipSpace _h

/-- **Read JSON text** into the profile's tree, or refuse at a byte offset with what the grammar
expects there. -/
def parse (bs : List Nat) : Except TextRefusal NatJson :=
  match readText bs (.value .top) with
  | .ok t => .ok t
  | .error (reason, rest) => .error ⟨bs.length - rest.length, reason⟩

/-- What a reason expects, in words. -/
def TextReason.words : TextReason → String
  | .value => "a value"
  | .separator => "a comma or the close of the array or object"
  | .key => "an object's key, a string"
  | .colon => "a colon after the key"
  | .digit => "a digit"
  | .leadingZero => "no digit after a leading zero"
  | .quote => "the string's closing quote"
  | .escape => "an escape: one of \\ \" / b f n r t, or u and four hexadecimal digits"
  | .control => "no control byte inside a string"
  | .surrogate => "a high surrogate's escape, then a low one's"
  | .utf8 => "UTF-8 inside the string"
  | .end_ => "the end of the text"

/-- **A text refusal in words**, the one spelling both drivers print: `JSON text at byte 12:
expected a value`. -/
def refusalText (r : TextRefusal) : String :=
  "JSON text at byte " ++ Nat.repr r.site ++ ": expected " ++ r.reason.words

end Effect4.NatJson
