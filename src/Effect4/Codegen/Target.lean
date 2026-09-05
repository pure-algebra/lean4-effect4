import Effect4.Data.Ascii
import TypeScript
import Effect4.Data.Json

/-!
# Codegen.Target — the targets, the artefact, and the one crossing to bytes

Design: `docs/research/2026-09-04-codegen-api-design.md` §3.1.

A **target** is a closed alphabet: TypeScript and JSON today, OCaml when the `lean4-ocaml`
package is pinned (§8 of the design). A target owns a syntax, and an emitter answers that
syntax and never text: `TypeScript.Module` is the pinned package's, `Json` is the estate's.
An **artefact** is one emitted value of one target, and `Artefact.render` is the one place
syntax becomes bytes. It is admitted by exact name in the axiom gate, exactly as
`Codegen.Schema.generate?` was; nothing inside the seam calls it.

## JSON text

rc.112 writes its JSON with `JSON.stringify`; the layout here is a fixed pretty layout
(two-space indent, one member per line) and the host receipt compares *parsed* values, never
bytes. Numbers follow `JSON.stringify` where it is exact and diverge where it is not, and the
divergence is stated: a non-finite datum renders `null` (`JSON.stringify(NaN)`), both zeros
render `0` (`JSON.stringify(-0)`), an integer below `2^53` renders its digits, and any other
finite datum renders its **exact** decimal expansion (`0.1` is the fifty-five-digit decimal
of the nearest binary64), which parses back to the same datum under any correct parser while
`JSON.stringify` would print the shortest round-tripping decimal. No shortest-digits
algorithm is modelled; every emitter of this tree writes naturals.

`number` traverses no `String`: it reads the bits, writes digits with `Nat.toDigits` and
`String.ofList`, so it is inside the axiom ceiling and can be `#guard`ed. `escape` and the
tree renderers fold over `String`s and reach `Classical.choice`; they are the crossing.
-/

namespace Effect4.Codegen

open Effect4

/-! ## Targets -/

/-- The targets an emitter may answer in. Closed; a new target is a plan change. -/
inductive Target where
  /-- Effect TypeScript at the host pin of `Codegen.Profile`. -/
  | ts
  /-- A JSON document: JSON Schema, OpenAPI, the MCP list payloads, wrangler. -/
  | json
deriving DecidableEq, Repr, Inhabited

namespace Target

/-- The target's spelling in a rule row and a report. -/
def name : Target → String
  | .ts => "ts"
  | .json => "json"

/-- The file extension of a target's artefact. -/
def extension : Target → String
  | .ts => "ts"
  | .json => "json"

/-- The closed target alphabet. -/
def census : List Target := [.ts, .json]

/-- The census has the alphabet's advertised size. -/
theorem census_length : census.length = 2 := by decide

/-- The census covers the alphabet. -/
theorem mem_census (target : Target) : target ∈ census := by
  cases target <;> decide

/-- The syntax a target's emitters answer: never text. -/
abbrev Syntax : Target → Type
  | .ts => TypeScript.Module
  | .json => Json

end Target

/-! ## Artefacts -/

/-- One emitted value of one target. -/
inductive Artefact where
  | ts (module : TypeScript.Module)
  | json (value : Json)

namespace Artefact

/-- An artefact of a target from that target's syntax. -/
def of : (target : Target) → target.Syntax → Artefact
  | .ts, module => .ts module
  | .json, value => .json value

/-- The target an artefact is of. -/
def target : Artefact → Target
  | .ts _ => .ts
  | .json _ => .json

/-- `of` answers in the target it was given. -/
theorem target_of (target : Target) (content : target.Syntax) :
    (Artefact.of target content).target = target := by
  cases target <;> rfl

end Artefact

/-! ## JSON text -/

namespace JsonText

/-- How many factors of two divide `m`, at most `fuel`. -/
def twos : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, m => if m % 2 = 0 ∧ m ≠ 0 then twos fuel (m / 2) + 1 else 0

/-- The decimal digits of `digits` with the point `scale` places from the right and the
trailing zeros of the fraction trimmed; at least one integer digit. -/
def decimal (digits scale : Nat) : List Char :=
  let raw := Nat.toDigits 10 digits
  let padded := List.replicate (scale + 1 - raw.length) '0' ++ raw
  let intPart := padded.take (padded.length - scale)
  let fracPart := ((padded.drop (padded.length - scale)).reverse.dropWhile (· == '0')).reverse
  if fracPart.isEmpty then intPart else intPart ++ '.' :: fracPart

/--
A binary64 datum as JSON number text, exactly.

`null` when the datum is not finite, `0` for both zeros, the digits of an integer, and the
exact decimal expansion otherwise (this module's header). The value is
`mantissa × 2^(exponent)`, read off the bits; a negative exponent `-k` is spelled through
`mantissa × 5^k` with the point `k` places from the right, after the factors of two shared by
the mantissa and the shift are cancelled.
-/
def number (value : Float64) : String :=
  if !value.isFinite then "null"
  else
    let bits := value.bits.toNat
    let negative := decide (bits / 2 ^ 63 = 1)
    let expField := bits / 2 ^ 52 % 2 ^ 11
    let frac := bits % 2 ^ 52
    let mantissa := if expField = 0 then frac else frac + 2 ^ 52
    if mantissa = 0 then "0"
    else
      let body : List Char :=
        if expField ≥ 1075 then Nat.toDigits 10 (mantissa * 2 ^ (expField - 1075))
        else
          let shift := if expField = 0 then 1074 else 1075 - expField
          let cancelled := twos shift mantissa
          let reduced := mantissa / 2 ^ cancelled
          let scale := shift - cancelled
          if scale = 0 then Nat.toDigits 10 reduced else decimal (reduced * 5 ^ scale) scale
      String.ofList ((if negative then ['-'] else []) ++ body)

/-- Two hexadecimal digits of a byte below 256. -/
private def hex2 (n : Nat) : String :=
  let digit (d : Nat) : Char := Char.ofNat (if d < 10 then 48 + d else 87 + d)
  String.ofList [digit (n / 16), digit (n % 16)]

/-- A JSON string literal: the quotes, the two escapes JSON requires, the named control
escapes, and `\u00XX` for every other control character. Other characters remain UTF-8. -/
def escape (value : String) : String :=
  "\"" ++
    value.foldl (init := "") (fun acc c =>
      acc ++
        (if c == '"' then "\\\""
         else if c == '\\' then "\\\\"
         else if c == '\n' then "\\n"
         else if c == '\r' then "\\r"
         else if c == '\t' then "\\t"
         else if c.toNat == 8 then "\\b"
         else if c.toNat == 12 then "\\f"
         else if c.toNat < 32 then "\\u00" ++ hex2 c.toNat
         else String.singleton c)) ++
    "\""

/-- Two spaces per level. -/
def indent (depth : Nat) : String := String.ofList (List.replicate (2 * depth) ' ')

@[simp] private theorem entryValue_sizeOf_lt (entry : String × Json) :
    sizeOf entry.2 < sizeOf entry := by
  cases entry
  simp +arith

mutual
/-- The fixed pretty layout: scalars inline, containers one member per line. -/
def render (depth : Nat) : Json → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .number n => number n
  | .str s => escape s
  | .arr [] => "[]"
  | .arr items =>
    "[\n" ++ renderList (depth + 1) items ++ "\n" ++ indent depth ++ "]"
  | .obj [] => "{}"
  | .obj entries =>
    "{\n" ++ renderEntries (depth + 1) entries ++ "\n" ++ indent depth ++ "}"
termination_by value => sizeOf value
decreasing_by all_goals decreasing_tactic

/-- Array members, one per line, comma-separated. -/
def renderList (depth : Nat) : List Json → String
  | [] => ""
  | [one] => indent depth ++ render depth one
  | first :: rest => indent depth ++ render depth first ++ ",\n" ++ renderList depth rest
termination_by items => sizeOf items
decreasing_by all_goals decreasing_tactic

/-- Object members, one per line, comma-separated, keys escaped. -/
def renderEntries (depth : Nat) : List (String × Json) → String
  | [] => ""
  | [(key, value)] => indent depth ++ escape key ++ ": " ++ render depth value
  | (key, value) :: rest =>
    indent depth ++ escape key ++ ": " ++ render depth value ++ ",\n" ++ renderEntries depth rest
termination_by entries => sizeOf entries
decreasing_by
  all_goals first
    | decreasing_tactic
    | exact Nat.lt_trans (entryValue_sizeOf_lt _) (by simp +arith)

end

end JsonText

/-- A JSON document as text, with a trailing newline. The crossing for the `json` target. -/
def renderJson (value : Json) : String := JsonText.render 0 value ++ "\n"

/-- The one crossing from syntax to bytes. Admitted by exact name in the axiom gate. -/
def Artefact.render : Artefact → String
  | .ts module => TypeScript.Render.module TypeScript.house0 module
  | .json value => renderJson value

/-! ## Anti-vacuity: the number spellings, decided in the kernel -/

#guard JsonText.number ⟨0⟩ = "0"
#guard JsonText.number Float64.negZero = "0"
#guard JsonText.number Float64.nan = "null"
#guard JsonText.number Float64.posInfinity = "null"
#guard JsonText.number ⟨0x3ff0000000000000⟩ = "1"
#guard JsonText.number ⟨0x4000000000000000⟩ = "2"
#guard JsonText.number ⟨0xc000000000000000⟩ = "-2"
#guard JsonText.number ⟨0x3fe0000000000000⟩ = "0.5"
#guard JsonText.number ⟨0x3fd0000000000000⟩ = "0.25"
#guard JsonText.number ⟨0x409c500000000000⟩ = "1812"
#guard JsonText.number ⟨0x433fffffffffffff⟩ = "9007199254740991"
#guard JsonText.number ⟨0x3ff8000000000000⟩ = "1.5"
#guard JsonText.number ⟨0x4004000000000000⟩ = "2.5"
-- the exact expansion of the nearest binary64 to one tenth
#guard JsonText.number ⟨0x3fb999999999999a⟩ =
  "0.1000000000000000055511151231257827021181583404541015625"
-- the smallest subnormal has 1074 fractional digits and begins as follows
#guard (JsonText.number ⟨1⟩).toUTF8.data.toList.take 6 = [48, 46, 48, 48, 48, 48]

end Effect4.Codegen
