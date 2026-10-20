import Effect4.Laws.Schema.Codec

/-! Finite JSON boundary controls for decisions rows 195 and 197.
The general raw and public codec laws remain in `Laws/Schema/Codec.lean`.
These controls distinguish type support, membership and value-level codec admission. -/

namespace Effect4.Test.DataCodec
open Effect4 Effect4.Program Effect4.Machine

def personTy : Ty := .record [("name", false, .string), ("nickname", true, .option .string)]
def absent : Val := Record.frame [("name", .str "Ada")]
def present : Val := Record.frame [("name", .str "Ada"), ("nickname", .none)]
def presentJson : Json := .obj [("name", .str "Ada"),
  ("nickname", .obj [("_tag", .str "None")])]

#guard Schema.encode [] personTy absent = some (.obj [("name", .str "Ada")])
#guard Schema.decode [] personTy (.obj [("name", .str "Ada")]) = some absent
#guard Schema.encode [] personTy present = some presentJson
#guard Schema.decode [] personTy presentJson = some present
#guard absent != present
#guard Schema.decode [] personTy (.obj []) = none
#guard Schema.decode [] personTy (.obj [("name", .str "Ada"), ("extra", .bool true)]) = none
#guard Schema.decode [] personTy (.obj [("name", .str "Ada"), ("name", .str "Grace")]) = none
#guard Schema.Codec.decodeRaw [] personTy (.obj [("name", .str "Ada"), ("name", .str "Ada")]) = none
#guard Schema.decode [] personTy (.obj [("nickname", .obj [("_tag", .str "None")]),
  ("name", .str "Ada")]) = some present

#guard Schema.encode [] (.record [("opaque", true, .handle "Remote")]) (Record.frame []) = some (.obj [])
#guard Schema.Codec.isSupported (.record [("opaque", true, .handle "Remote")]) = false
#guard Schema.decode [] (.record [("__proto__", false, .nat), ("a-b", false, .bool)])
  (.obj [("a-b", .bool true), ("__proto__", Arch.Json.ofNat 7)]) =
  some (Record.frame [("__proto__", .nat 7), ("a-b", .bool true)])

#guard Schema.encode [] (.tuple []) (.list []) = some (.arr [])
#guard Schema.decode [] (.tuple []) (.arr [Arch.Json.ofNat 7]) = none
#guard Schema.encode [] (.tuple [.nat]) (.list [.nat 7]) = some (.arr [Arch.Json.ofNat 7])
#guard Schema.decode [] (.tuple [.nat]) (.arr []) = none
#guard Schema.decode [] (.tuple [.nat]) (.arr [Arch.Json.ofNat 7, Arch.Json.ofNat 8]) = none
#guard Schema.encode [] (.tuple [.nat, .string]) (.list [.nat 7, .str "x"]) =
  Schema.encode [] (.prod .nat .string) (.list [.nat 7, .str "x"])
#guard Schema.decode [] (.tuple [.nat, .string, .bool])
  (.arr [Arch.Json.ofNat 7, .str "x", .bool true]) = some (.list [.nat 7, .str "x", .bool true])
#guard Schema.decode [] (.tuple [.nat, .string, .bool])
  (.arr [Arch.Json.ofNat 7, .str "x", .str "true"]) = none

def mapTy : Ty := .map .string personTy
def mapValue : Val := Map.write [("__proto__", absent), ("a-b", present)]
#guard Schema.encode [] mapTy mapValue = some (.obj [("__proto__", .obj [("name", .str "Ada")]),
  ("a-b", presentJson)])
#guard Schema.decode [] mapTy (.obj [("a-b", presentJson),
  ("__proto__", .obj [("name", .str "Ada")])]) = some mapValue
#guard Schema.decode [] (.map .string .nat) (.obj [("2", Arch.Json.ofNat 2), ("10", Arch.Json.ofNat 10)]) =
  some (Map.write [("10", .nat 10), ("2", .nat 2)])
#guard Schema.decode [] (.map .string .nat) (.obj [("x", Arch.Json.ofNat 1), ("x", Arch.Json.ofNat 2)]) = none
#guard Schema.Codec.decodeRaw [] (.map .nat .nat) (.obj []) = none
#guard Schema.encode [] (.map .string .never) (Map.write []) = some (.obj [])

/-- Overlapping object images select the first fitting raw branch.
The public codec additionally requires exact recovery of the original value. -/
def objectUnion : Ty := .union (.record [("x", false, .nat)]) (.map .string .nat)
#guard Schema.Codec.decodeRaw [] objectUnion (.obj [("x", Arch.Json.ofNat 7)]) =
  some (Record.frame [("x", .nat 7)])
#guard Schema.Codec.decodeRaw [] objectUnion (.obj [("y", Arch.Json.ofNat 7)]) =
  some (Map.write [("y", .nat 7)])
#guard Schema.Codec.decodeRaw [] (.union (.list .nat) (.tuple [.nat])) (.arr [Arch.Json.ofNat 7]) =
  some (.list [.nat 7])

/-! ## The error payload's JSON (decisions row 120)

A promoted defect's error has no type to direct its JSON. A record payload crosses as the
one-key object `{"payload": hex}` of its canonical bytes, apart from `{"boom": null}`, a number,
a pair and a string; the image is exact (`Schema.Codec.decodeErr_exact`). At a record error type
the type-directed codec writes the record itself. -/

def failFrame : Val := Record.frame [("_tag", .str "NotFound"), ("id", .nat 9)]
def failPayload : List Err := ((Payload.image.ofVal failFrame).map Err.payload).toList

#guard failPayload.length = 1
#guard failPayload.all fun e => Schema.Codec.decodeErr (Schema.Codec.encodeErr e) == some e
#guard failPayload.all fun e =>
  (Schema.Codec.encodeDefect [] (.error e)).bind (Schema.Codec.decodeDefect []) == some (.error e)
#guard failPayload.all fun e => match Schema.Codec.encodeErr e with
  | .obj [("payload", .str _)] => true
  | _ => false
-- a record named like `boom` stays apart from the payload-less boom
#guard ((Payload.image.ofVal (Record.frame [("boom", .unit)])).map fun p =>
  Schema.Codec.encodeErr (.payload p) != Schema.Codec.encodeErr .boom) = some true
-- red controls: an uppercase spelling, a non-frame and malformed text are refused
#guard failPayload.all fun e => match Schema.Codec.encodeErr e with
  | .obj [("payload", .str hex)] =>
    hex.toUpper != hex && Schema.Codec.decodeErr (.obj [("payload", .str hex.toUpper)]) == none
  | _ => false
#guard Schema.Codec.decodeErr (.obj [("payload", .str "")]) = none
#guard Schema.Codec.decodeErr (.obj [("payload", .str "zz")]) = none
#guard Schema.Codec.decodeErr (.obj [("payload", Arch.Json.ofNat 1)]) = none
-- at the record type, a cause's failure carries the record's own JSON
#guard (Schema.encode [] (.causeOf (.record [("_tag", false, .lit "NotFound"), ("id", false, .nat)]))
    (Val.exitErr (Cause.fail (errOf failFrame)))).isSome

/-! Prepared boundary operations reuse one source-bound wire interpretation.
These readers serve `decode-encode`, `decode-iff` and `record-codec-layout`. -/

def preparedPerson : Schema.Codec.Prepared personTy := Schema.Codec.prepare personTy

example : preparedPerson.encode [] absent = Schema.encode [] personTy absent :=
  Schema.Codec.Prepared.encode_agrees preparedPerson [] absent

example : preparedPerson.decode [] presentJson = Schema.decode [] personTy presentJson :=
  Schema.Codec.Prepared.decode_agrees preparedPerson [] presentJson

example : preparedPerson.isValue [] present = Ty.isCodecValue [] personTy present :=
  Schema.Codec.Prepared.isValue_agrees preparedPerson [] present

-- Absent optional fields and present None retain distinct exact images.
#guard preparedPerson.encode [] absent = some (.obj [("name", .str "Ada")])
#guard preparedPerson.decode [] presentJson = some present
#guard preparedPerson.decode [] (.obj [("name", .str "Ada"), ("extra", .bool true)]) = none
#guard preparedPerson.decode [] (.obj [("name", .str "Ada"), ("name", .str "Grace")]) = none

-- The wire layout alone accepts strings; the source literal still refuses a different string.
#guard (Schema.Codec.prepare (.lit "Ada")).decode [] (.str "Ada") = some (.str "Ada")
#guard (Schema.Codec.prepare (.lit "Ada")).decode [] (.str "Grace") = none
#guard (Schema.Codec.prepare (.lit "Ada")).encode [] (.str "Grace") = none

-- Overlapping object images cannot erase the original record/map distinction.
#guard (Schema.Codec.prepare objectUnion).encode [] (Record.frame [("x", .nat 7)]) =
  some (.obj [("x", Arch.Json.ofNat 7)])
#guard (Schema.Codec.prepare objectUnion).encode [] (Map.write [("x", .nat 7)]) = none
#guard (Schema.Codec.prepare objectUnion).encode [] (Map.write [("y", .nat 7)]) =
  some (.obj [("y", Arch.Json.ofNat 7)])

-- A structural-support refusal does not forbid an absent optional unsupported field.
#guard (Schema.Codec.prepare (.record [("opaque", true, .handle "Remote")])).encode []
  (Record.frame []) = some (.obj [])
#guard (Schema.Codec.prepare (.handle "Remote")).decode [] .null = none
#guard (Schema.Codec.prepare .int).encode [] (.nat (2 ^ 53)) = none
#guard (Schema.Codec.prepare .number).encode [] (.nat (2 ^ 53 + 1)) = none
#guard (Schema.Codec.prepare .number).isValue [] (.nat (2 ^ 53 + 1)) = false
#guard (Schema.Codec.prepare .int).decode [] (.number Float64.nan) = none

/-! ## One numeric bound on the nat wire (the owner's ruling R7, 2026-10-19; move J)

Codec admission of a natural is the profile's bound, `safeBound`, as at `int`. Membership does
not change: a natural past the bound stays a member of `nat` and stops being a codec value. -/

-- finite evaluation: the bound itself crosses both ways
#guard Ty.isCodecValue [] .nat (.nat (2 ^ 53 - 1)) = true
#guard Schema.decode [] .nat (Arch.Json.ofNat (2 ^ 53 - 1)) = some (.nat (2 ^ 53 - 1))
-- control: one past the bound has no image, and its datum does not read. Binary64 holds that
-- datum exactly. The admission premise of `decode_encode` stops here.
#guard Ty.isCodecValue [] .nat (.nat (2 ^ 53)) = false
#guard Schema.encode [] .nat (.nat (2 ^ 53)) = none
#guard Schema.decode [] .nat (Arch.Json.ofNat (2 ^ 53)) = none
-- control: membership stays, so membership does not give codec admission
#guard Val.hasTy (.nat (2 ^ 53)) .nat = true

/-! ## The canonical defect alphabet, encoded as Effect writes a defect (the owner's ruling R5,
2026-10-19; move G)

A defect crosses as rc.112's `Schema.Defect()` writes the thrown value
(`Schema.Codec.encodeDefect`): a user defect as its number, a represented error as its raw JSON,
and a machine defect as an `Error`'s name and message. A missing service's message spells its key
under the module's key names. The table names two keys. An unnamed key and the scope's key are
the two other keys of the forms. -/

def todoKey : ServiceKey := ⟨⟨7⟩, ⟨8⟩⟩
def clockKey : ServiceKey := ⟨⟨9⟩, ⟨4⟩⟩
def plainKey : ServiceKey := ⟨⟨5⟩, ⟨6⟩⟩
def keyNames : KeyNames := [(todoKey, "TodoRepo"), (clockKey, "Clock")]

/-- One canonical defect of each form: a user defect, the three represented errors, and the
machine defects, with a missing service at the scope's key, at each named key and at the unnamed
key. -/
def canonicalDefects : List Defect :=
  [.user 7, .error (.text "boom"), .error (.tagged "SqlError" "no such table")] ++
    failPayload.map .error ++
    [.asyncFiber, .missingService Env.scopeKey, .missingService todoKey, .missingService clockKey,
      .missingService plainKey, .notImplemented, .badName]

#guard canonicalDefects.length = 11
-- finite evaluation: each form's JSON, as rc.112's `Schema.Defect()` writes the thrown value
#guard Schema.Codec.encodeDefect keyNames (.user 7) = some (Arch.Json.ofNat 7)
#guard Schema.Codec.encodeDefect keyNames (.error (.text "boom")) = some (.str "boom")
#guard Schema.Codec.encodeDefect keyNames (.error (.tagged "SqlError" "no such table")) =
  some (.arr [.str "SqlError", .str "no such table"])
#guard Schema.Codec.encodeDefect keyNames .asyncFiber = some (.obj
  [("message", .str "An asynchronous Effect was executed with Effect.runSync"),
    ("name", .str "AsyncFiberError")])
#guard Schema.Codec.encodeDefect keyNames (.missingService Env.scopeKey) =
  some (.obj [("message", .str "Service not found: effect/Scope"), ("name", .str "Error")])
#guard Schema.Codec.encodeDefect keyNames (.missingService todoKey) =
  some (.obj [("message", .str "Service not found: TodoRepo"), ("name", .str "Error")])
#guard Schema.Codec.encodeDefect keyNames (.missingService plainKey) =
  some (.obj [("message", .str "Service not found: k5_6"), ("name", .str "Error")])
#guard Schema.Codec.encodeDefect keyNames .notImplemented =
  some (.obj [("message", .str "notImplemented"), ("name", .str "Effect4")])
#guard Schema.Codec.encodeDefect keyNames .badName =
  some (.obj [("message", .str "badName"), ("name", .str "Effect4")])
-- finite evaluation: distinct defects of the list have distinct encodings
#guard (canonicalDefects.filterMap (Schema.Codec.encodeDefect keyNames)).eraseDups.length =
  canonicalDefects.length
-- finite evaluation: each decodes back, and so through the public codec at a cause type
#guard canonicalDefects.all fun d =>
  (Schema.Codec.encodeDefect keyNames d).bind (Schema.Codec.decodeDefect keyNames) == some d
#guard canonicalDefects.all fun d =>
  (Schema.encode keyNames (.causeOf .never) (Val.exitErr (Cause.die d))).bind
    (Schema.decode keyNames (.causeOf .never)) == some (Val.exitErr (Cause.die d))
-- finite evaluation: an `Error` object reads in either order of its two entries
#guard Schema.Codec.decodeDefect keyNames
  (.obj [("name", .str "Error"), ("message", .str "Service not found: Clock")]) =
    some (.missingService clockKey)
-- finite evaluation: the defects `Defect.ofError` makes are canonical, so each has an image
#guard [Err.tag 7, .text "boom", .tagged "SqlError" "x", .boom].all fun e =>
  (Schema.Codec.encodeDefect keyNames (Defect.ofError e)).isSome

/-- RED: the first draft's raw mapping wrote `error (tag 7)` as `7`, the image of `user 7` (the
note's finding 8.9). The canonical form of `error (tag 7)` is `user 7`, and the encoder writes
no image for the other. -/
def red_tagSevenCrosses : Bool := (Schema.Codec.encodeDefect keyNames (.error (.tag 7))).isSome
/--
error: Expression
  red_tagSevenCrosses
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_tagSevenCrosses
-- control: `user 7` crosses, and `error boom`, which is `badName`, is refused like `error (tag 7)`
#guard (Schema.Codec.encodeDefect keyNames (.user 7)).isSome
#guard Schema.Codec.encodeDefect keyNames (.error .boom) = none

/-- RED: one numeric bound at the observation (the owner's ruling R7; D-J1 of move J's receipt):
a user defect past `safeBound` has no image. -/
def red_userPastBound : Bool := (Schema.Codec.encodeDefect keyNames (.user (2 ^ 53))).isSome
/--
error: Expression
  red_userPastBound
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard red_userPastBound
-- control: the bound itself crosses, and the datum past it does not read
#guard Schema.Codec.encodeDefect keyNames (.user (2 ^ 53 - 1)) = some (Arch.Json.ofNat (2 ^ 53 - 1))
#guard Schema.Codec.decodeDefect keyNames (Arch.Json.ofNat (2 ^ 53)) = none

-- control: a table that names another key `effect/Scope` makes the scope's message name two keys.
-- The decoder refuses that message, so the public codec writes neither missing service.
def scopeClash : KeyNames := [(todoKey, "effect/Scope")]
#guard Schema.Codec.decodeDefect scopeClash
  (Schema.Codec.errorJson "Error" "Service not found: effect/Scope") = none
#guard (Schema.encode scopeClash (.causeOf .never)
  (Val.exitErr (Cause.die (.missingService Env.scopeKey)))).isNone
#guard (Schema.encode scopeClash (.causeOf .never)
  (Val.exitErr (Cause.die (.missingService todoKey)))).isNone
#guard (Schema.encode [] (.causeOf .never)
  (Val.exitErr (Cause.die (.missingService Env.scopeKey)))).isSome

-- control: what is no canonical form is refused: the legacy wrapper, a boolean, `null`,
-- `{"boom": null}`, an `Error` with a stack, an `Error` the machine never throws, and the scope
-- key's runtime text, which is not its spelling
#guard [Json.obj [("user", Arch.Json.ofNat 7)], .bool true, .null, .obj [("boom", .null)],
    .obj [("message", .str "boom"), ("name", .str "Error"), ("stack", .str "at")],
    Schema.Codec.errorJson "Error" "boom",
    Schema.Codec.errorJson "Error" "Service not found: k0_0"].all fun j =>
  Schema.Codec.decodeDefect keyNames j == none

end Effect4.Test.DataCodec
