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
-/

namespace Effect4.Target.TypeScript.Trace

open Effects.Trace

/-- JSON string escaping for the value cells. -/
def escape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++
      (if c == '"' then "\\\"" else if c == '\\' then "\\\\"
       else if c == '\n' then "\\n" else if c == '\r' then "\\r"
       else if c == '\t' then "\\t" else String.singleton c)

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
golden's identity; `rules` lists the lowering rule ids the program exercises. -/
def golden (program : String) (tape : List (Nat × Bool)) (rules : List String)
    (log : Effect4.Trace.Log) : String :=
  "format\teffect4-trace-v1\n" ++
  "face\tlean\n" ++
  "program\t" ++ program ++ "\n" ++
  "tape\t" ++ String.intercalate "," (tape.map fun entry =>
    toString entry.1 ++ ":" ++ (if entry.2 then "1" else "0")) ++ "\n" ++
  "rules\t" ++ String.intercalate "," rules ++ "\n" ++
  rows log

end Effect4.Target.TypeScript.Trace
