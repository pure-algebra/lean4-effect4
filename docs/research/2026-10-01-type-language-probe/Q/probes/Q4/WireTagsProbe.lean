import Tools.WireTags
/-! Probe Q4: the wire-tag loader (`tools/Tools/WireTags.lean`) on the data wave's eight `Ty`
appends. Read-only on the loader; the JSON texts are local strings, never the tracked file. -/
open Lean Tools.WireTags

/-- Today's `Ty` rows (`tools/Effect4Gen/wire-tags.json`) with a caller-supplied tail. -/
def tyRows (tail : String) : String :=
  "{\"format\": \"effect4-wire-tags-v1\", \"comment\": [], \"families\": {\"Effect4.Program.Ty\": " ++
  "{\"active\": {\"never\": 0, \"unit\": 1, \"nat\": 2, \"int\": 3, \"string\": 4, \"bool\": 5, " ++
  "\"handle\": 6, \"option\": 7, \"list\": 8, \"prod\": 9, \"except\": 10, \"exitOf\": 11, " ++
  "\"causeOf\": 12, \"fiberOf\": 13, \"union\": 14, \"lit\": 15, \"refOf\": 16, \"deferredOf\": 17, " ++
  "\"var\": 18, \"unknown\": 19" ++ tail ++ "}, \"retired\": {}}}}"

def today : List String :=
  ["never", "unit", "nat", "int", "string", "bool", "handle", "option", "list", "prod", "except",
   "exitOf", "causeOf", "fiberOf", "union", "lit", "refOf", "deferredOf", "var", "unknown"]
def wave : List String := ["record", "map", "tuple", "app", "null", "undefined", "number", "bytes"]
def ctorNames (xs : List String) : List Name := xs.map (`Effect4.Program.Ty ++ ·.toName)

def tagsFor (tail : String) (ctors : List String) : Except String (List Nat) := do
  let a ← parse (tyRows tail)
  tagsOf a `Effect4.Program.Ty false (ctorNames ctors)

def waveTail : String :=
  ", \"record\": 20, \"map\": 21, \"tuple\": 22, \"app\": 23, \"null\": 24, \"undefined\": 25, " ++
  "\"number\": 26, \"bytes\": 27"

-- (1) green: the wave's tags 20-27 after today's 0-19, against a 28-constructor declaration.
#eval tagsFor waveTail (today ++ wave)
-- (2) red: a repeated tag (`map` given `record`'s 20) is refused by `parse` (WireTags.lean:88-90).
#eval tagsFor ", \"record\": 20, \"map\": 20" (today ++ ["record", "map"])
-- (3) a repeated name inside one JSON object: `Json.parse` keeps one key (the last), so the
-- loader's name check (WireTags.lean:91-93) never sees the repetition.
#eval tagsFor ", \"record\": 20, \"record\": 21" (today ++ ["record"])
#eval (Json.parse "{\"a\": 1, \"a\": 2}").map (·.compress)
-- (4) red: a declared constructor with no active row (`tuple` declared, not listed).
#eval tagsFor ", \"record\": 20" (today ++ ["record", "tuple"])
-- (5) red: a listed row with no declared constructor (`map` listed, not declared).
#eval tagsFor ", \"record\": 20, \"map\": 21" (today ++ ["record"])
-- (6) a tag gap (21 skipped) is accepted: the loader does not require density.
#eval tagsFor ", \"record\": 20, \"map\": 22" (today ++ ["record", "map"])
-- (7) a reused retired tag: `record` given 3 while `yieldError`-style retired row holds 3.
#eval (do
  let a ← parse ("{\"format\": \"effect4-wire-tags-v1\", \"comment\": [], \"families\": " ++
    "{\"F\": {\"active\": {\"a\": 0, \"record\": 3}, \"retired\": {\"old\": 3}}}}")
  tagsOf a `F false [`F.a, `F.record] : Except String (List Nat))
