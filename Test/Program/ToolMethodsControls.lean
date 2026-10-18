import Effect4.Tool.Methods

/-!
# The tool table's controls (`Tool/Methods.lean`)

Finite evaluations of the derived table at the real `Request` shape: it lists every method key
once, in the order of `supportedMethods`; each method's name is its case's wire name (`open_` is
`open`); every method has a description, its four hints and the reply's closed schema; an argument
schema reads as the profile prints; it says a thing once (a shared shape under `$defs`, the grammar
left to `describe`, `dry`'s action left to the action tools); and `describe` spells what the
schemas leave to it, under its own schemas and hints. Readers of the JSON text itself stay inside
the guards.

Two red controls show where the table refuses to be built: a description that misses a key, and
a wire name that two cases write. A third, green, declares a small request with the same command.
-/

namespace Test.Program.ToolMethodsControls
open Effect4.Tool Effect4.Tool.Methods

-- every supported method, once, in order, each with a description
#guard entries.map (·.listing.name) = supportedMethods.map Prod.fst
#guard entries.all fun e => !e.listing.description.isEmpty
#guard (entries.map (·.listing.name)).eraseDups.length = entries.length
#guard entries.length = MethodKey.all.length
-- the request case each method builds
#guard (entries.filter (·.kind == "act")).map (·.listing.name) =
  ["open", "edit", "fill", "publish", "reset", "start", "restore", "play"]
#guard entries.all fun e => (e.kind == "act" && e.field == "a") || (e.kind == "ask" && e.field == "q")
-- the wire name of each case is its key's (open_ is "open")
#guard (entries.find? (·.caseName == "open_")).map (·.listing.name) = some "open"
#guard (entries.find? (·.caseName == "slots")).map (·.listing.name) = some "slots"
#guard MethodKey.all.map MethodKey.caseName = ["open_", "edit", "fill", "publish", "reset", "start",
  "restore", "play", "doc", "history", "fills", "suggest", "run", "preview", "dry", "discover",
  "table", "addresses", "slots"]
-- the wire's methods and versions, which `discover` answers, are the hand list they replace
#guard supportedMethods = ["open", "edit", "fill", "publish", "reset", "start", "restore", "play",
  "doc", "history", "fills", "suggest", "run", "preview", "dry", "discover", "table", "addresses",
  "slots"].map fun name => (name, [1])
-- the table quotes text without escaping it, so no quoted text may need an escape
#guard ([describeText, onDemandText, toolCallText, describe.listing.name] ++
    MethodKey.all.map MethodKey.description ++ entries.map (·.caseName) ++
    entries.map (·.listing.name)).all fun t =>
  t.all fun c => c != '"' && c != '\\' && c.toNat ≥ 32
-- the hints: the queries are read-only and the actions are not; `open` and `reset` discard what
-- the state held; every method but `open`, `start`, `restore` and `play` is idempotent; none
-- reaches outside the tool's state
#guard entries.all fun e => e.listing.readOnly == (e.kind == "ask")
#guard (entries.filter (·.listing.destructive)).map (·.listing.name) = ["open", "reset"]
#guard (entries.filter (!·.listing.idempotent)).map (·.listing.name) =
  ["open", "start", "restore", "play"]
#guard entries.all fun e => !e.listing.openWorld
#guard describe.listing.readOnly && !describe.listing.destructive && describe.listing.idempotent &&
  !describe.listing.openWorld
-- every method answers the reply in its envelope, closed: no definition is left to `describe`
#guard entries.all fun e => e.listing.outputSchema == replySchema
#guard (replySchema.splitOn onDemandText).length == 1
#guard (replySchema.splitOn "\"required\":[\"method\",\"version\",\"payload\"]").length == 2
#guard (replySchema.splitOn "\"required\":[\"result\",\"now\"]").length == 2
#guard (replySchema.splitOn "withFiber").length ≥ 2
-- `describe` answers a schema document: a pointer and its definitions
#guard (describe.listing.outputSchema.splitOn "\"required\":[\"$ref\",\"$defs\"]").length == 2
-- a document whose root is no structure is an object only under `allOf`
#guard docSchema [] false ⟨.nat, []⟩ =
  "{\"type\":\"object\",\"allOf\":[{\"type\":\"integer\",\"minimum\":0,\"maximum\":9007199254740991}]}"
#guard (Effect4.Store.shape Request).defs.all fun d => d.1.all fun c => c != '"' && c != '\\' && c != '~' && c != '/'
-- a shared structure or sum is a `$defs` key by its name, so its name needs no escape either
#guard (((Effect4.Store.shape Request).root :: (Effect4.Store.shape Request).defs.map (·.2)).flatMap
    (nested [])).all fun d => d.1.all fun c => c != '"' && c != '\\' && c != '~' && c != '/'
#guard toString Effect4.Tool.CodecProfile.natLimit = "9007199254740991"
-- schemas: an object of the case's fields, with what they reach under $defs
#guard (entries.find? (·.listing.name == "reset")).map (·.listing.inputSchema) =
  some "{\"type\":\"object\",\"properties\":{},\"required\":[],\"additionalProperties\":false}"
#guard (entries.find? (·.listing.name == "slots")).any fun e =>
  (e.listing.inputSchema.splitOn "\"required\":[\"at_\",\"slot\"]").length == 2
#guard (entries.find? (·.listing.name == "open")).any fun e =>
  (e.listing.inputSchema.splitOn "\"$defs\"").length == 2 &&
    (e.listing.inputSchema.splitOn "\"required\":[\"name\",\"app\",\"sketch\"]").length == 2
-- the profile's naturals and nullary sums
#guard schemaIn {} .nat = "{\"type\":\"integer\",\"minimum\":0,\"maximum\":9007199254740991}"
#guard schemaIn {} (.sum "E" [("a", 0, []), ("b", 1, [])]) = "{\"enum\":[\"a\",\"b\"]}"
-- a sum with a field is an object; its cases with no field share one branch
#guard schemaIn {} (.sum "E" [("a", 0, []), ("b", 1, []), ("c", 2, [("x", .bool)])]) =
  "{\"type\":\"object\",\"oneOf\":[{\"properties\":{\"_tag\":{\"enum\":[\"a\",\"b\"]}},\"required\":[\"_tag\"],\
\"additionalProperties\":false},{\"properties\":{\"_tag\":{\"const\":\"c\"},\"x\":{\"type\":\"boolean\"}},\
\"required\":[\"_tag\",\"x\"],\"additionalProperties\":false}]}"
-- a structure met in two places is written once, by its name; met in one place, it stays there
#guard fieldsSchema [] [] true [("x", .struct "P" [("v", .bool)]), ("y", .option (.struct "P" [("v", .bool)]))] =
  "{\"type\":\"object\",\"properties\":{\"x\":{\"$ref\":\"#/$defs/P\"},\"y\":{\"anyOf\":[{\"type\":\"null\"},\
{\"$ref\":\"#/$defs/P\"}]}},\"required\":[\"x\",\"y\"],\"additionalProperties\":false,\"$defs\":{\"P\":\
{\"type\":\"object\",\"properties\":{\"v\":{\"type\":\"boolean\"}},\"required\":[\"v\"],\"additionalProperties\":false}}}"
#guard fieldsSchema [] [] true [("x", .struct "P" [("v", .bool)])] =
  "{\"type\":\"object\",\"properties\":{\"x\":{\"type\":\"object\",\"properties\":{\"v\":{\"type\":\"boolean\"}},\
\"required\":[\"v\"],\"additionalProperties\":false}},\"required\":[\"x\"],\"additionalProperties\":false}"
-- a table definition written as an object is left to `describe`, which spells it
#guard fieldsSchema [("T", .struct "T" [("v", .option (.named "T"))])] [] true [("x", .named "T")] =
  "{\"type\":\"object\",\"properties\":{\"x\":{\"$ref\":\"#/$defs/T\"}},\"required\":[\"x\"],\
\"additionalProperties\":false,\"$defs\":{\"T\":{\"type\":\"object\",\"description\":\"" ++ onDemandText ++ "\"}}}"
#guard definitionSchema [("T", .struct "T" [("v", .option (.named "T"))])] "T" =
  "{\"$ref\":\"#/$defs/T\",\"$defs\":{\"T\":{\"type\":\"object\",\"properties\":{\"v\":{\"anyOf\":\
[{\"type\":\"null\"},{\"$ref\":\"#/$defs/T\"}]}},\"required\":[\"v\"],\"additionalProperties\":false}}}"
-- a list family is spelled where it is named
#guard !onDemand (.sum "L" [("nil", 0, []), ("cons", 1, [("head", .nat), ("tail", .named "L")])])
-- at the real table: the grammar is `describe`'s, and no method's schema spells it
#guard describe.answers.map (·.1) = ["Ty", "Eff", "Stmt", "ActionTerm", "LayerTerm", "Term", "CauseTerm", "Val"]
#guard entries.all fun e => (e.listing.inputSchema.splitOn "withFiber").length == 1
#guard (describe.answers.lookup "Eff").any fun s => (s.splitOn "withFiber").length == 2
#guard describe.answers.all fun a => (a.2.splitOn onDemandText).length == 1
-- `dry`'s action names the action tools' cases and leaves their arguments to them
#guard (entries.find? (·.listing.name == "dry")).any fun e =>
  (e.listing.inputSchema.splitOn toolCallText).length == 2 &&
    (e.listing.inputSchema.splitOn "\"$defs\"").length == 1
#guard quote "abc" = "\"abc\""

/-! ## Red: the table refuses a method without a description, and a wire name written twice -/

-- A description that misses a key does not elaborate, and the error names the key.
/--
error: Missing cases:
MethodKey.slots
-/
#guard_msgs in
example : MethodKey → String
  | .open_ | .edit | .fill | .publish | .reset | .start | .restore | .play => ""
  | .doc | .history | .fills | .suggest | .run | .preview | .dry | .discover | .table
  | .addresses => ""

-- Two cases that write one wire name refuse the whole declaration, at the case that repeats it.
namespace TwoWireNames
/-- error: this case's wire name is another method's: two methods would share it -/
#guard_msgs in
tool_requests
  actions [
    | go (n : Nat) wire "go"
    | stop
  ]
  queries [
    | look wire "go"
  ]
end TwoWireNames

/-! ## Green: the same command declares a small request -/

namespace OneWireName
tool_requests
  actions [
    | go (n : Nat)
  ]
  queries [
    | look wire "peek"
  ]
#guard MethodKey.all.map MethodKey.name = ["go", "peek"]
#guard MethodKey.all.map MethodKey.caseName = ["go", "look"]
#guard MethodKey.all.map MethodKey.kind = [.action, .query]
#guard (Request.ask .look).methodKey == .look
end OneWireName

end Test.Program.ToolMethodsControls
