import Effect4.Tool.Wire
import Effect4.Tool.Native
import Effect4.Laws.Tool.CodecProfile

/-!
# Test.Program.WireControls — the tool's JSON profile, codecs and wire adapter (seams S3b)

Finite controls. The JSON profile refuses `Option Unit` and a rounded natural, and keeps an
ordinary one. The Check codecs refuse unknown tags and missing fields. The wire adapter decodes a
request at the selected version and refuses an unselected method, a wrong version, a method that
disagrees with its payload, a malformed message and an invalid connection; each refusal leaves the
state as it was. An accepted request through `serveJson` appends one action.

The profile's located reader (`Store/Domain/ShapeJson.lean`, Codex's R4.1) names a site and a
reason for each refusal. Its red controls: a repeated key, a key that names no field, a misspelt
case, a natural above `natLimit` and a number that is no natural refuse, and `Option Unit` refuses
as outside the profile. Objects in any order and both spellings of a list family read the same
value, and an array's element keeps its index. Probe 1's four `unreadable` refusals
(`docs/research/2026-10-18-authoring-probe/session/locate.txt`) now name their places, relative to
the MCP tool's arguments (`Native.relativeRefusal`).
-/

set_option autoImplicit false
namespace Test.Program.WireControls
open Effect4 Effect4.Program Effect4.Program.Check Effect4.Store Effect4.Tool
open Effect4.Tool.Wire (Envelope Connection decode serveJson)

/-! ## The JSON profile -/

#guard CodecProfile.supports (Canonical.shape (Option Unit)) = false
#guard match CodecProfile.write (some () : Option Unit) with
  | .error .unsupportedProfile => true | _ => false
#guard match CodecProfile.read (α := Option Unit) .null with
  | .error (.unreadable ⟨.schema [], .unsupportedProfile⟩) => true | _ => false
-- A natural that a JSON number would round refuses rather than change.
#guard match CodecProfile.write (9007199254740993 : Nat) with
  | .error .unprintable => true | _ => false
#guard match CodecProfile.write (7 : Nat) with
  | .ok j => (CodecProfile.read (α := Nat) j).toOption = some 7 | _ => false
-- The profile carries naturals up to 2^53 - 1: 2^53 is exact in binary64, yet refuses on write,
-- and a JSON that spells it refuses on read; the native shell refuses the same trees.
#guard match CodecProfile.write (9007199254740991 : Nat) with
  | .ok j => (CodecProfile.read (α := Nat) j).toOption = some 9007199254740991 | _ => false
#guard match CodecProfile.write (9007199254740992 : Nat) with
  | .error .unprintable => true | _ => false
#guard match CodecProfile.read (α := Nat) (Canonical.print (9007199254740992 : Nat)) with
  | .error (.unreadable ⟨.value [], .naturalOutsideProfile 9007199254740991⟩) => true | _ => false
#guard !CodecProfile.carries (.list [.nat 1, .pair .unit (.nat 9007199254740992)])
#guard CodecProfile.carries (.ctor 0 [.nat 9007199254740991, .negInt 9007199254740992])

/-! ## The Check codecs -/

def program : NativeEff := .succeed (.lit (.nat 7))
def input : CheckInput := .module {} [] program
#guard Canonical.ofVal (Canonical.toVal input) = some input
#guard Canonical.ofVal (α := CheckInput) (.ctor 99 []) = none
#guard Canonical.ofVal (α := CheckInput) (.ctor 0 []) = none
#guard match CodecProfile.write input with
  | .ok j => (CodecProfile.read (α := CheckInput) j).toOption = some input
  | .error _ => false

/-! ## The wire adapter -/

def openRequest : Request := .act (.open_ "wire" {} ⟨program, []⟩)
def framed (method : String) (version : Nat) (payload : Request) : Effect4.Json :=
  match CodecProfile.write (⟨method, version, payload⟩ : Envelope Request) with
  | .ok j => j
  | .error _ => .null

-- A request reads back at the selected version.
#guard match decode Connection.v1 (framed "open" 1 openRequest) with
  | .ok envelope => envelope.method == "open" && envelope.version == 1
  | .error _ => false
-- An unselected method, a wrong version and a disagreeing method refuse.
#guard match decode ⟨[]⟩ (framed "open" 1 openRequest) with
  | .error (.unselected "open") => true | _ => false
#guard match decode Connection.v1 (framed "open" 2 openRequest) with
  | .error (.version "open" 1 2) => true | _ => false
#guard match decode Connection.v1 (framed "edit" 1 openRequest) with
  | .error (.method "edit" "open") => true | _ => false
-- A message that is not an envelope, and a connection that selects one method twice, refuse.
#guard match decode Connection.v1 (.str "open") with
  | .error (.codec (.unreadable ⟨.value [], .expected _⟩)) => true | _ => false
#guard match decode ⟨[("open", 1), ("open", 1)]⟩ (framed "open" 1 openRequest) with
  | .error .connection => true | _ => false

-- An accepted request appends one action; a refused message leaves the state.
def served := (serveJson Oracle.uncached Connection.v1 empty (framed "open" 1 openRequest)).value
#guard served.1.transcript.length = 1
#guard served.2.toOption.isSome
def refused := (serveJson Oracle.uncached ⟨[]⟩ empty (framed "open" 1 openRequest)).value
#guard refused.1.transcript.isEmpty
#guard refused.2.toOption.isNone


/-! ## The located reader: sites and reasons -/

/-- A document with a structure, a list family of naturals, a sum with a field and a sum of
names. -/
def sampleDoc : ShapeDoc :=
  { root := .struct "Root" [("xs", .named "L"), ("e", .named "E"), ("k", .named "K")]
    defs := [("L", .sum "L" [("nil", 0, []), ("cons", 1, [("head", .nat), ("tail", .named "L")])]),
      ("E", .sum "E" [("a", 0, [("n", .nat)]), ("b", 1, [])]),
      ("K", .sum "K" [("x", 0, []), ("y", 1, [])])] }

/-- `sampleDoc`'s value with the list `[1]`, the case `b` and the name `x`. -/
def sampleValue : Val := .ctor 0 [.ctor 1 [.nat 1, .ctor 0 []], .ctor 1 [], .ctor 0 []]

/-- `sampleDoc`'s root object with `xs` given, and the rest valid. -/
def withXs (xs : NatJson) : NatJson :=
  .obj [("xs", xs), ("e", .obj [("_tag", .str "b")]), ("k", .str "x")]

/-- The refusal the reader answers, if it refuses. -/
def refusalOf (doc : ShapeDoc) (t : NatJson) : Option JsonRefusal :=
  match doc.readLocated t with
  | .ok _ => none
  | .error r => some r

-- tested: objects in any order, and a list family as an array or as its cells, read one value
#guard (sampleDoc.readAny (.obj [("k", .str "x"), ("e", .obj [("n", .nat 3), ("_tag", .str "a")]),
    ("xs", .arr [.nat 1, .nat 2])])).map Val.encode =
  (sampleDoc.readAny (.obj [("xs", .obj [("_tag", .str "cons"), ("head", .nat 1),
    ("tail", .obj [("tail", .obj [("_tag", .str "nil")]), ("_tag", .str "cons"),
      ("head", .nat 2)])]), ("e", .obj [("_tag", .str "a"), ("n", .nat 3)]),
    ("k", .str "x")])).map Val.encode
#guard (sampleDoc.readAny (withXs (.arr [.nat 1]))).map Val.encode = some sampleValue.encode
-- tested: the printer writes the list family as an array, and the reader reads its print
#guard NatJson.render (sampleDoc.printTree sampleValue) =
  NatJson.codes "{\"xs\":[1],\"e\":{\"_tag\":\"b\"},\"k\":\"x\"}"
#guard (sampleDoc.readAny (sampleDoc.printTree sampleValue)).map Val.encode =
  some sampleValue.encode
-- tested: a negative integer prints as the binary64 printer's `toString` writes it, with no
-- `Int.add` (which the lowered route lacks)
#guard NatJson.render ((ShapeDoc.mk .unit []).printTree (.negInt 4)) = NatJson.codes "{\"int\":\"-5\"}"
#guard (ShapeDoc.mk .unit []).print (.negInt 4) = .obj [("int", .str "-5")]
-- control: an array's element keeps its index inside a list family's array
#guard match refusalOf sampleDoc (withXs (.arr [.nat 1, .str "x"])) with
  | some ⟨.value [.key "xs", .index 1], .expected _⟩ => true | _ => false
-- control: a missing field names its present parent
#guard match refusalOf sampleDoc (.obj [("xs", .arr []), ("e", .obj [("_tag", .str "a")]),
    ("k", .str "x")]) with
  | some ⟨.missing [.key "e"] "n", .expected .nat⟩ => true | _ => false
-- control: a key that names no field, a repeated key, and a misspelt case, by name and by tag
#guard match refusalOf sampleDoc (.obj [("xs", .arr []), ("e", .obj [("_tag", .str "b")]),
    ("k", .str "x"), ("z", .null)]) with
  | some ⟨.value [], .unknownField "z"⟩ => true | _ => false
#guard match refusalOf sampleDoc (.obj [("xs", .arr []), ("xs", .arr []),
    ("e", .obj [("_tag", .str "b")]), ("k", .str "x")]) with
  | some ⟨.value [], .duplicateField "xs"⟩ => true | _ => false
#guard match refusalOf sampleDoc (.obj [("xs", .arr []), ("e", .obj [("_tag", .str "b")]),
    ("k", .str "w")]) with
  | some ⟨.value [.key "k"], .unknownCase "w"⟩ => true | _ => false
#guard match refusalOf sampleDoc (.obj [("xs", .arr []), ("e", .obj [("_tag", .str "c")]),
    ("k", .str "x")]) with
  | some ⟨.value [.key "e"], .unknownCase "c"⟩ => true | _ => false
-- control: a natural above the profile's limit, a natural past the host's integers, and a
-- number that is no natural; the limit itself reads
#guard match refusalOf sampleDoc (withXs (.arr [.nat 9007199254740992])) with
  | some ⟨.value [.key "xs", .index 0], .naturalOutsideProfile 9007199254740991⟩ => true
  | _ => false
#guard match refusalOf sampleDoc (withXs (.arr [.numeral "18446744073709551616"])) with
  | some ⟨.value [.key "xs", .index 0], .naturalOutsideProfile _⟩ => true | _ => false
#guard match refusalOf sampleDoc (withXs (.arr [.numeral "-1"])) with
  | some ⟨.value [.key "xs", .index 0], .expected .nat⟩ => true | _ => false
#guard (refusalOf sampleDoc (withXs (.arr [.nat 9007199254740991]))).isNone
-- control: the profile refuses `Option Unit` at the shape's root, whatever the JSON
#guard match CodecProfile.readLocated (α := Option Unit) .null with
  | .error ⟨.schema [], .unsupportedProfile⟩ => true | _ => false
-- control: a tree that fits the shape and that the carrier refuses (a digest of one byte) is
-- refused at the root; a case the shape lacks is refused by the shape, at its place
#guard match Canonical.readLocated (α := Digest) (.str "00") with
  | .error ⟨.value [], .carrierValue⟩ => true | _ => false
#guard (Canonical.readLocated (α := Digest) (.str (String.ofList (List.replicate 64 '0')))).toOption.isSome
#guard match Canonical.readLocated (α := Program.Check.CheckInput) (.obj [("_tag", .str "nope")]) with
  | .error ⟨.value [], .unknownCase "nope"⟩ => true | _ => false

/-! ## No budget: every refusal is the input's

The reader recurses on the tree, then on the names unfolded since the last node, then on the
shape (`optionLayer?`, `Store/Domain/ShapeRead.lean`), with no budget. The base's reader refused
with the reason `budget` at eight steps a node and 64 more; each control below names what it
refused, and what the reader answers now. -/

/-- A name whose definition returns to it through options alone. -/
def loopDoc : ShapeDoc := ⟨.named "A", [("A", .option (.named "A"))]⟩

/-- Two names that return to each other through options alone. -/
def loopPairDoc : ShapeDoc :=
  ⟨.named "A", [("A", .option (.named "B")), ("B", .option (.named "A"))]⟩

/-- A shape under `n` options. -/
def underOptions : Nat → Shape → Shape
  | 0, s => s
  | n + 1, s => .option (underOptions n s)

/-- A hundred options over a natural: one node takes a hundred and one steps. -/
def deepDoc : ShapeDoc := ⟨underOptions 100 .nat, []⟩

/-- A structure with a hundred fields of one name. -/
def sameNamesDoc : ShapeDoc := ⟨.struct "S" (List.replicate 100 ("a", .nat)), []⟩

/-- A name under an option and a pair: each pair is a node, so the names unfolded start again. -/
def nodeDoc : ShapeDoc := ⟨.named "T", [("T", .option (.pair (.named "T") (.named "T")))]⟩

-- control: a value under a loop of options refuses as `expected` at its place, where the base
-- refused with `budget`; `null` reads as the option's `none`
#guard match refusalOf loopDoc (.nat 5) with
  | some ⟨.value [], .expected (.named "A")⟩ => true | _ => false
#guard (loopDoc.readAny .null).map Val.encode = some Val.none.encode
-- control: a loop through two names refuses at the name it returns to
#guard match refusalOf loopPairDoc (.str "x") with
  | some ⟨.value [], .expected (.named "A")⟩ => true | _ => false
-- control: inside an array, the refusal keeps the element's place
#guard match refusalOf ⟨.list (.named "A"), [("A", .option (.named "A"))]⟩ (.arr [.null, .bool true])
    with
  | some ⟨.value [.index 1], .expected (.named "A")⟩ => true | _ => false
-- tested: a natural under a hundred options reads, where the base refused with `budget` (72
-- steps for one node), and its print is the natural
#guard ((deepDoc.readAny (.nat 5)).map fun v => NatJson.render (deepDoc.printTree v)) =
  some (NatJson.codes "5")
-- control: an object with one of a hundred fields of one name refuses as `expected` at the
-- object, where the base refused with `budget` (80 steps)
#guard match refusalOf sameNamesDoc (.obj [("a", .nat 1)]) with
  | some ⟨.value [], .expected (.struct "S" _)⟩ => true | _ => false
-- tested: a name met again below a node reads
#guard (nodeDoc.readAny (.arr [.null, .arr [.null, .null]])).map Val.encode =
  some (Val.some (.pair .none (.some (.pair .none .none)))).encode
-- control: the strict reader refuses the loop and reads the deep option, as the located one does
#guard readIn loopDoc.defs [] loopDoc.root (Canonical.print (5 : Nat)) = none
#guard (readIn deepDoc.defs [] deepDoc.root (Canonical.print (5 : Nat))).isSome

/-! ## Probe 1's four `unreadable` refusals, relative to the MCP tool's arguments -/

/-- An object with its `_tag`. -/
def tagged (tag : String) (fields : List (String × NatJson)) : NatJson :=
  .obj (("_tag", .str tag) :: fields)

/-- **The refusal an MCP tool's arguments get**: the MCP server writes them as the case object at
`payload.<field>` of a request envelope (`ocaml/engine/kit/kit_mcp.ml`), the native shell reads
the envelope (`Native.serveTree`), and the refusal is placed relative to the arguments
(`Native.relativeRefusal`). -/
def argumentsRefusal (tool : String) (args : List (String × NatJson)) : Option Wire.Refusal :=
  match Native.methods.find? fun e => decide (e.listing.name = tool) with
  | none => none
  | some e =>
    let envelope : NatJson := .obj [("method", .str tool), ("version", .nat 1),
      ("payload", tagged e.kind [(e.field, tagged e.caseName args)])]
    match Native.serveTree Native.start envelope with
    | .ok _ => none
    | .error why => some (Native.relativeRefusal [.key "payload", .key e.field] why)

-- session step 9, a misnamed field: the fill item at `a.items[0][1]` has no `q`
#guard match argumentsRefusal "edit"
    [("at_", .obj [("doc", .obj [("name", .str "demo"), ("generation", .nat 0)]),
      ("revision", .nat 0)]),
     ("a", tagged "commit" [("items", .arr [.arr [tagged "hole" [("index", .nat 0)],
       tagged "fill" [("program", tagged "succeed" [("value", tagged "var" [("index", .nat 0)])])]]]),
       ("policy", .str "keepExact")])] with
  | some (.codec (.unreadable ⟨.missing [.key "a", .key "items", .index 0, .index 1] "q", _⟩)) =>
    true
  | _ => false
-- F4, a misspelt tag: `sketch.program` names no case `succed`
#guard match argumentsRefusal "open"
    [("name", .str "f4"), ("app", .obj [("rows", .arr []), ("services", .arr []), ("types", .arr [])]),
     ("sketch", .obj [("program", tagged "succed" [("value", tagged "lit"
        [("value", tagged "nat" [("value", .nat 1)])])]), ("holes", .arr [])])] with
  | some (.codec (.unreadable ⟨.value [.key "sketch", .key "program"], .unknownCase "succed"⟩)) =>
    true
  | _ => false
-- F5b, a value in a literal's spelling: under `q`, the reply's value has no field `n`
#guard match argumentsRefusal "preview"
    [("q", tagged "settle" [("tape", .arr [tagged "success" [("value", tagged "nat"
        [("value", .nat 7)])]]), ("limit", .nat 8)])] with
  | some (.codec (.unreadable
      ⟨.missing [.key "q", .key "tape", .index 0, .key "value"] "n", .expected .nat⟩)) => true
  | _ => false
-- F12, an address past 2^53: `at_[0]` is a natural above the profile's limit
#guard match argumentsRefusal "doc" [("at_", .arr [.nat 9007199254740993])] with
  | some (.codec (.unreadable
      ⟨.value [.key "at_", .index 0], .naturalOutsideProfile 9007199254740991⟩)) => true
  | _ => false

end Test.Program.WireControls
