/-!
# The canonical JSON printers

One JSON value model, two rendered surfaces, both total:

- `render` — the manifest printer (WGR-4 rule 1): object keys sorted at
  render time, layout fixed — objects and mixed arrays break across
  lines, scalar arrays stay inline so byte vectors read as vectors.
  Byte-identical regeneration under an unchanged model version is the
  gate's ratchet.
- `renderCompact` — the canonical value encoding (CAS-003): no
  whitespace, object keys sorted by codepoint (which is UTF-8 byte
  order), strings escaped exactly as ECMAScript `JSON.stringify`
  escapes them (the short escapes, then lowercase `\u00xx` for the
  remaining控 control range), numbers as integers in decimal — the one
  number form whose textual rendering is language-neutral, which is why
  the value encoding admits integers only.

Fields render before they sort, so both printers are structurally
recursive — the byte authority carries a termination proof, not a
`partial` waiver. Strings escape quotes, backslashes, and control
characters deterministically; nothing here is fractional or
implementation-formatted.
-/

namespace Cas.Json

/-- LAW SM-15: the value plane has no float term, which is the ceiling
every schema-plane refusal of a float is measured against.

The canonical value model: null, booleans, the two integer
constructors, strings, arrays and objects. Numbers are integers only —
the one textual rendering that is language-neutral. -/
inductive Value where
  | null
  | bool (b : Bool)
  | nat (n : Nat)
  | int (i : Int)
  | str (s : String)
  | arr (xs : List Value)
  | obj (fields : List (String × Value))

def escapeChar (c : Char) : String :=
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c.toNat ≥ 32 then String.singleton c
  else
    let hex := Nat.toDigits 16 c.toNat
    "\\u" ++ String.ofList (List.replicate (4 - hex.length) '0' ++ hex)

def escape (s : String) : String :=
  s.foldl (fun acc c => acc ++ escapeChar c) ""

/-- One lowercase hex digit. -/
def hexLower (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- The value-encoding escape: exactly the ECMAScript `JSON.stringify`
set — the two mandatory escapes, the five short escapes, lowercase
`\u00xx` for the remaining control range, every other character
literal. -/
def escapeCharCompact (c : Char) : String :=
  let n := c.toNat
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if n = 8 then "\\b"
  else if n = 9 then "\\t"
  else if n = 10 then "\\n"
  else if n = 12 then "\\f"
  else if n = 13 then "\\r"
  else if n < 32 then
    String.ofList ['\\', 'u', '0', '0', hexLower (n / 16), hexLower (n % 16)]
  else String.singleton c

def escapeCompact (s : String) : String :=
  s.foldl (fun acc c => acc ++ escapeCharCompact c) ""

def Value.isScalar : Value → Bool
  | .null | .bool _ | .nat _ | .int _ | .str _ => true
  | .arr _ | .obj _ => false

mutual

/-- Render with sorted object keys and fixed layout. `indent` is the
current indentation depth in two-space units. Fields render before
they sort — the sort key is the field name, so the output is the same
and the recursion stays structural. -/
def render (v : Value) (indent : Nat := 0) : String :=
  let pad := String.ofList (List.replicate (indent * 2) ' ')
  let padIn := String.ofList (List.replicate ((indent + 1) * 2) ' ')
  match v with
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .nat n => toString n
  | .int i => toString i
  | .str s => "\"" ++ escape s ++ "\""
  | .arr xs =>
    if xs.isEmpty then "[]"
    else if xs.all (·.isScalar) then
      "[" ++ String.intercalate ", " (renderItems xs 0) ++ "]"
    else
      "[\n" ++
        String.intercalate ",\n"
          ((renderItems xs (indent + 1)).map (padIn ++ ·)) ++
        "\n" ++ pad ++ "]"
  | .obj fields =>
    if fields.isEmpty then "{}"
    else
      let rendered := renderFields fields (indent + 1)
      let sorted := rendered.mergeSort fun a b => decide (a.1 ≤ b.1)
      "{\n" ++
        String.intercalate ",\n" (sorted.map fun (k, s) =>
          padIn ++ "\"" ++ escape k ++ "\": " ++ s) ++
        "\n" ++ pad ++ "}"

def renderItems : List Value → Nat → List String
  | [], _ => []
  | x :: rest, indent => render x indent :: renderItems rest indent

def renderFields : List (String × Value) → Nat → List (String × String)
  | [], _ => []
  | (k, v) :: rest, indent => (k, render v indent) :: renderFields rest indent

end

mutual

/-- The compact canonical value encoding (CAS-003): no whitespace,
object keys sorted by codepoint, `JSON.stringify`-exact escaping,
integer decimals. The UTF-8 bytes of this string are what a value
node's content identity is computed over. -/
def renderCompact : Value → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .nat n => toString n
  | .int i => toString i
  | .str s => "\"" ++ escapeCompact s ++ "\""
  | .arr xs => "[" ++ String.intercalate "," (renderCompactItems xs) ++ "]"
  | .obj fields =>
    let rendered := renderCompactFields fields
    let sorted := rendered.mergeSort fun a b => decide (a.1 ≤ b.1)
    "{" ++
      String.intercalate "," (sorted.map fun (k, s) =>
        "\"" ++ escapeCompact k ++ "\":" ++ s) ++
      "}"

def renderCompactItems : List Value → List String
  | [] => []
  | x :: rest => renderCompact x :: renderCompactItems rest

def renderCompactFields : List (String × Value) → List (String × String)
  | [] => []
  | (k, v) :: rest => (k, renderCompact v) :: renderCompactFields rest

end

/-- A rendered manifest document: the value plus the trailing newline. -/
def document (v : Value) : String := render v ++ "\n"

end Cas.Json

namespace Cas.Json

/-! ## Canonical spelling — sorted keys, and the sort-free rendering

`renderCompact` sorts object fields at render time, so it cannot
distinguish two spellings of one object. `Value.Canonical` names the
values on which no reordering happens — every object's keys already in
strict codepoint order — and `renderCompact_eq_renderPlain` is the
rendering theorem: on canonical values the canonical rendering IS the
purely structural fold. The schema codec's encoders emit canonical
values by construction (`Cas.Schema.encode_canonical`), which binds
the byte identity to the structural encoding with no hidden sort.

The converse direction — bytes determine the canonical value, i.e.
`renderPlain` is injective — is NOT here. It lives in
`Cas.Values.JsonInj`, which states it (`RenderPlainInjective`),
refutes its naive form (`renderPlain_not_injective`: `.nat n` and
`.int n` share a spelling), and discharges the escape half
(`escapeCompact_inj`, `renderPlain_str_inj`); and in
`Cas.Values.JsonParse`, which PROVES it (`renderPlain_injective`) from
the strict parser's left-inverse property. -/

mutual

/-- Every object node's keys strictly sorted, recursively. Strict
order subsumes duplicate-freedom. -/
def Value.Canonical : Value → Prop
  | .arr xs => CanonicalItems xs
  | .obj fields =>
    List.Pairwise (fun a b => a.1 < b.1) fields ∧ CanonicalFields fields
  | _ => True

def CanonicalItems : List Value → Prop
  | [] => True
  | x :: xs => x.Canonical ∧ CanonicalItems xs

def CanonicalFields : List (String × Value) → Prop
  | [] => True
  | (_, v) :: fields => v.Canonical ∧ CanonicalFields fields

end

/-- Strict key order gives the (non-strict, Bool-valued) order the
canonical renderer sorts by. -/
private theorem le_of_key_lt {a b : String} (h : a < b) : a ≤ b :=
  Std.le_of_not_ge fun hge => hge h

mutual

/-- The sort-free structural rendering: identical layout to
`renderCompact`, object fields taken in given order. -/
def renderPlain : Value → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .nat n => toString n
  | .int i => toString i
  | .str s => "\"" ++ escapeCompact s ++ "\""
  | .arr xs => "[" ++ String.intercalate "," (renderPlainItems xs) ++ "]"
  | .obj fields =>
    "{" ++ String.intercalate "," (renderPlainFields fields) ++ "}"

def renderPlainItems : List Value → List String
  | [] => []
  | x :: rest => renderPlain x :: renderPlainItems rest

def renderPlainFields : List (String × Value) → List String
  | [] => []
  | (k, v) :: rest =>
    ("\"" ++ escapeCompact k ++ "\":" ++ renderPlain v) :: renderPlainFields rest

end

private theorem renderPlainFields_eq_map (fs : List (String × Value)) :
    renderPlainFields fs =
      fs.map (fun f => "\"" ++ escapeCompact f.1 ++ "\":" ++ renderPlain f.2) := by
  induction fs with
  | nil => rfl
  | cons f rest ih => cases f; simp [renderPlainFields, ih]

mutual

/-- THE rendering theorem: on canonical values, `renderCompact`
performs no reordering — the canonical bytes are the structural fold
of the value as spelled. -/
theorem renderCompact_eq_renderPlain :
    ∀ (v : Value), v.Canonical → renderCompact v = renderPlain v
  | .null, _ => rfl
  | .bool _, _ => rfl
  | .nat _, _ => rfl
  | .int _, _ => rfl
  | .str _, _ => rfl
  | .arr xs, h => by
    simp only [renderCompact, renderPlain]
    rw [renderCompactItems_eq_renderPlainItems xs h]
  | .obj fields, h => by
    obtain ⟨hsorted, hfields⟩ := h
    simp only [renderCompact, renderPlain]
    rw [renderCompactFields_eq_map fields hfields]
    rw [List.mergeSort_of_pairwise (by
      refine (List.pairwise_map).mpr ?_
      exact hsorted.imp fun hab => by
        simpa using le_of_key_lt hab)]
    rw [renderPlainFields_eq_map, List.map_map]
    rfl

theorem renderCompactItems_eq_renderPlainItems :
    ∀ (xs : List Value), CanonicalItems xs →
      renderCompactItems xs = renderPlainItems xs
  | [], _ => rfl
  | x :: rest, h => by
    simp only [renderCompactItems, renderPlainItems]
    rw [renderCompact_eq_renderPlain x h.1,
      renderCompactItems_eq_renderPlainItems rest h.2]

theorem renderCompactFields_eq_map :
    ∀ (fs : List (String × Value)), CanonicalFields fs →
      renderCompactFields fs = fs.map (fun f => (f.1, renderPlain f.2))
  | [], _ => rfl
  | (k, v) :: rest, h => by
    simp only [renderCompactFields, List.map_cons]
    rw [renderCompact_eq_renderPlain v h.1,
      renderCompactFields_eq_map rest h.2]

end

end Cas.Json
