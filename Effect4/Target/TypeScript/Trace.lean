import Effect4.Semantics.Observation

/-!
# Target.TypeScript.Trace

The wire form of the profile's trace: one tab-separated row per event, JSON
scalars and arrays in the value cells, and the header rows a golden carries.
This module renders `String`s and is admitted as an exact target-implementation
module in the axiom gate; it declares no theorem. The alphabet and its laws live
in `Effects/Trace.lean`; the agreement judgment in
`Effect4/Semantics/Observation.lean`.

Wire form of values: `unit` → `[]`, `nat n` / `int i` → a JSON integer,
`bool` → `true`/`false`, `str` → a JSON string, `pair a b` → `[a, b]`,
`none` → `{"none":true}`, `some v` → `{"some":v}`. Outcomes:
`{"success":v}`, `{"failure":e}`, `{"interrupted":true}`.

Two declared refusals of this encoder, recorded in `docs/TRACE-DAG.md`
separation 9 and in `test/counterexamples/REGISTER.md`:

- `nat n` and `int i` render identically, so equal rows do not imply equal
  events; the gate compares rows *under the declared answer-type profile*, and
  the host honours the same profile (`wireAnswer`) (`E4-TARGET-CE-016`).
- A natural above `2^53 - 1` has no host counterpart; golden emission refuses
  one (`harness/trace/Generate.lean`) and the host tracer marks such a run
  invalid (`E4-TARGET-CE-015`).
-/

namespace Effect4.Target.TypeScript.Trace

open Effects.Trace

/-- One lowercase hexadecimal digit of a nibble, as `JSON.stringify` spells it. -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + (n % 16))

/-- A code point as JSON's six-character escape, `\uXXXX` in lowercase hex.
Only C0 controls reach this, so the code point is below `0x20` and the four
digits are exact. -/
def unicodeEscape (c : Char) : String :=
  let n := c.toNat
  "\\u" ++ String.mk
    [hexDigit (n / 4096 % 16), hexDigit (n / 256 % 16), hexDigit (n / 16 % 16), hexDigit (n % 16)]

/-- JSON string escaping for the value cells, character for character what
`JSON.stringify` emits (ECMA-262 `QuoteJSONString`): the two structural
characters, the five C0 shorthands, and `\uXXXX` for every other control below
`0x20`. `DEL` and the non-ASCII planes are passed through, as `JSON.stringify`
passes them; a Lean `String` holds Unicode scalar values, so no lone surrogate
can reach here. counterexample: E4-TARGET-CE-014 -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++
      (if c == '"' then "\\\"" else if c == '\\' then "\\\\"
       else if c == '\n' then "\\n" else if c == '\r' then "\\r"
       else if c == '\t' then "\\t"
       else if c == Char.ofNat 8 then "\\b" else if c == Char.ofNat 12 then "\\f"
       else if c.toNat < 32 then unicodeEscape c else String.singleton c)

def val : Val → String
  | .unit => "[]"
  | .nat n => toString n
  | .int i => toString i
  | .bool b => if b then "true" else "false"
  | .str s => "\"" ++ escape s ++ "\""
  | .pair a b => "[" ++ val a ++ ", " ++ val b ++ "]"
  | .none => "{\"none\":true}"
  | .some v => "{\"some\":" ++ val v ++ "}"

def outcome : Outcome Val → String
  | .success v => "{\"success\":" ++ val v ++ "}"
  | .failure e => "{\"failure\":" ++ val e ++ "}"
  | .defect e => "{\"defect\":" ++ val e ++ "}"
  | .interrupted => "{\"interrupted\":true}"

/-- One event as a tab-separated row. -/
def row : Effect4.Trace.Event → String
  | .op name request => "op\t" ++ name ++ "\t" ++ val request
  | .answer name value => "answer\t" ++ name ++ "\t" ++ val value
  | .failed name error => "failed\t" ++ name ++ "\t" ++ val error
  | .decide site branch => "decide\t" ++ toString site ++ "\t" ++ (if branch then "true" else "false")
  | .enter region => "enter\t" ++ toString region
  | .leave region o => "leave\t" ++ toString region ++ "\t" ++ outcome o
  | .finalizer region o => "finalizer\t" ++ toString region ++ "\t" ++ outcome o
  | .done o => "done\t" ++ outcome o
  | .frontier => "frontier"

/-- The rows of a log, one per line, newline-terminated. -/
def rows (log : Effect4.Trace.Log) : String :=
  String.join (log.map fun event => row event ++ "\n")

/-- A mask as a row of its seven flags, in field order. -/
def maskRow (name : String) (mask : Effect4.Trace.Mask) : String :=
  let flag (b : Bool) := if b then "1" else "0"
  "mask\t" ++ name ++ "\t" ++
    String.intercalate "\t"
      [ flag mask.ops, flag mask.answers, flag mask.decisions, flag mask.regions
      , flag mask.finalizers, flag mask.outcome, flag mask.frontier ] ++ "\n"

/-- The generated mask table, from `Effect4.Trace.maskTable` only. -/
def maskTable : String :=
  "format\teffect4-trace-masks-v1\n" ++
    String.join (Effect4.Trace.maskTable.map fun entry => maskRow entry.1 entry.2)

/-- A golden: header rows, then the events. `program` and `tape` are the
golden's identity; `rules` lists the lowering rule ids the program exercises.

`budgets` is emitted only for a resource-boundary golden: one `budget` row per
named host yield setting, giving the op budget (`EFFECT4_BUDGET`) whose
`frontier` lands exactly where the Lean face's fuel ran out. There is one
budget per yield setting because the budget counts *primitives* and the yield
wrapper is itself primitives (TRACE-DAG separation 8); the rows compared are
the same rows at both settings. An empty list leaves every other golden
byte-identical. -/
def golden (program : String) (tape : List (Nat × Bool)) (rules : List String)
    (log : Effect4.Trace.Log) (face : String := "lean")
    (budgets : List (String × Nat) := []) : String :=
  "format\teffect4-trace-v1\n" ++
  "face\t" ++ face ++ "\n" ++
  "program\t" ++ program ++ "\n" ++
  "tape\t" ++ String.intercalate "," (tape.map fun entry =>
    toString entry.1 ++ ":" ++ (if entry.2 then "1" else "0")) ++ "\n" ++
  "rules\t" ++ String.intercalate "," rules ++ "\n" ++
  String.join (budgets.map fun entry => "budget\t" ++ entry.1 ++ "\t" ++ toString entry.2 ++ "\n") ++
  rows log

end Effect4.Target.TypeScript.Trace
