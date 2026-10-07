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

#guard Schema.encode personTy absent = some (.obj [("name", .str "Ada")])
#guard Schema.decode personTy (.obj [("name", .str "Ada")]) = some absent
#guard Schema.encode personTy present = some presentJson
#guard Schema.decode personTy presentJson = some present
#guard absent != present
#guard Schema.decode personTy (.obj []) = none
#guard Schema.decode personTy (.obj [("name", .str "Ada"), ("extra", .bool true)]) = none
#guard Schema.decode personTy (.obj [("name", .str "Ada"), ("name", .str "Grace")]) = none
#guard Schema.Codec.decodeRaw personTy (.obj [("name", .str "Ada"), ("name", .str "Ada")]) = none
#guard Schema.decode personTy (.obj [("nickname", .obj [("_tag", .str "None")]),
  ("name", .str "Ada")]) = some present

#guard Schema.encode (.record [("opaque", true, .handle "Remote")]) (Record.frame []) = some (.obj [])
#guard Schema.Codec.isSupported (.record [("opaque", true, .handle "Remote")]) = false
#guard Schema.decode (.record [("__proto__", false, .nat), ("a-b", false, .bool)])
  (.obj [("a-b", .bool true), ("__proto__", Arch.Json.ofNat 7)]) =
  some (Record.frame [("__proto__", .nat 7), ("a-b", .bool true)])

#guard Schema.encode (.tuple []) (.list []) = some (.arr [])
#guard Schema.decode (.tuple []) (.arr [Arch.Json.ofNat 7]) = none
#guard Schema.encode (.tuple [.nat]) (.list [.nat 7]) = some (.arr [Arch.Json.ofNat 7])
#guard Schema.decode (.tuple [.nat]) (.arr []) = none
#guard Schema.decode (.tuple [.nat]) (.arr [Arch.Json.ofNat 7, Arch.Json.ofNat 8]) = none
#guard Schema.encode (.tuple [.nat, .string]) (.list [.nat 7, .str "x"]) =
  Schema.encode (.prod .nat .string) (.list [.nat 7, .str "x"])
#guard Schema.decode (.tuple [.nat, .string, .bool])
  (.arr [Arch.Json.ofNat 7, .str "x", .bool true]) = some (.list [.nat 7, .str "x", .bool true])
#guard Schema.decode (.tuple [.nat, .string, .bool])
  (.arr [Arch.Json.ofNat 7, .str "x", .str "true"]) = none

def mapTy : Ty := .map .string personTy
def mapValue : Val := Map.write [("__proto__", absent), ("a-b", present)]
#guard Schema.encode mapTy mapValue = some (.obj [("__proto__", .obj [("name", .str "Ada")]),
  ("a-b", presentJson)])
#guard Schema.decode mapTy (.obj [("a-b", presentJson),
  ("__proto__", .obj [("name", .str "Ada")])]) = some mapValue
#guard Schema.decode (.map .string .nat) (.obj [("2", Arch.Json.ofNat 2), ("10", Arch.Json.ofNat 10)]) =
  some (Map.write [("10", .nat 10), ("2", .nat 2)])
#guard Schema.decode (.map .string .nat) (.obj [("x", Arch.Json.ofNat 1), ("x", Arch.Json.ofNat 2)]) = none
#guard Schema.Codec.decodeRaw (.map .nat .nat) (.obj []) = none
#guard Schema.encode (.map .string .never) (Map.write []) = some (.obj [])

/-- Overlapping object images select the first fitting raw branch.
The public codec additionally requires exact recovery of the original value. -/
def objectUnion : Ty := .union (.record [("x", false, .nat)]) (.map .string .nat)
#guard Schema.Codec.decodeRaw objectUnion (.obj [("x", Arch.Json.ofNat 7)]) =
  some (Record.frame [("x", .nat 7)])
#guard Schema.Codec.decodeRaw objectUnion (.obj [("y", Arch.Json.ofNat 7)]) =
  some (Map.write [("y", .nat 7)])
#guard Schema.Codec.decodeRaw (.union (.list .nat) (.tuple [.nat])) (.arr [Arch.Json.ofNat 7]) =
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
  Schema.Codec.decodeDefect (Schema.Codec.encodeDefect (.error e)) == some (.error e)
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
#guard (Schema.encode (.causeOf (.record [("_tag", false, .lit "NotFound"), ("id", false, .nat)]))
    (Val.exitErr (Cause.fail (errOf failFrame)))).isSome

end Effect4.Test.DataCodec
