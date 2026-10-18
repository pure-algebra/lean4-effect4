import Effect4.Tool.Methods

/-!
# The tool table's controls (`Tool/Methods.lean`)

Finite evaluations of the derived table at the real `Request` shape: it lists every supported
method once, in the order of `supportedMethods`; each method's name is `Request.method`'s for its
case; every method has a description; a schema reads as the profile prints; it says a thing once
(a shared shape under `$defs`, the grammar left to `describe`, `dry`'s action left to the action
tools); and `describe` spells what the schemas leave to it. Readers of the JSON text itself stay
inside the guards.
-/

namespace Test.Program.ToolMethodsControls
open Effect4.Tool Effect4.Tool.Methods

-- every supported method, once, in order, each with a description
#guard entries.map (·.name) = supportedMethods.map Prod.fst
#guard entries.all fun e => !e.description.isEmpty
#guard (entries.map (·.name)).eraseDups.length = entries.length
-- the request case each method builds
#guard (entries.filter (·.kind == "act")).map (·.name) =
  ["open", "edit", "fill", "publish", "reset", "start", "restore", "play"]
#guard entries.all fun e => (e.kind == "act" && e.field == "a") || (e.kind == "ask" && e.field == "q")
-- the wire name of each case is Request.method's (open_ is "open")
#guard (entries.find? (·.caseName == "open_")).map (·.name) = some "open"
#guard (entries.find? (·.caseName == "slots")).map (·.name) = some "slots"
-- red (tested): a description keyed by a case the Request shape lacks would leave its method out
#guard descriptions.length = entries.length
-- the table quotes text without escaping it, so no quoted text may need an escape
#guard ([describeText, onDemandText, toolCallText, describe.name] ++ descriptions.map (·.2.2) ++
    entries.map (·.caseName) ++ entries.map (·.name)).all fun t =>
  t.all fun c => c != '"' && c != '\\' && c.toNat ≥ 32
#guard (Effect4.Store.shape Request).defs.all fun d => d.1.all fun c => c != '"' && c != '\\' && c != '~' && c != '/'
-- a shared structure or sum is a `$defs` key by its name, so its name needs no escape either
#guard (((Effect4.Store.shape Request).root :: (Effect4.Store.shape Request).defs.map (·.2)).flatMap
    (nested [])).all fun d => d.1.all fun c => c != '"' && c != '\\' && c != '~' && c != '/'
#guard toString Effect4.Tool.CodecProfile.natLimit = "9007199254740991"
-- schemas: an object of the case's fields, with what they reach under $defs
#guard (entries.find? (·.name == "reset")).map (·.schema) =
  some "{\"type\":\"object\",\"properties\":{},\"required\":[],\"additionalProperties\":false}"
#guard (entries.find? (·.name == "slots")).any fun e =>
  (e.schema.splitOn "\"required\":[\"at_\",\"slot\"]").length == 2
#guard (entries.find? (·.name == "open")).any fun e =>
  (e.schema.splitOn "\"$defs\"").length == 2 && (e.schema.splitOn "\"required\":[\"name\",\"app\",\"sketch\"]").length == 2
-- the profile's naturals and nullary sums
#guard schemaIn {} .nat = "{\"type\":\"integer\",\"minimum\":0,\"maximum\":9007199254740991}"
#guard schemaIn {} (.sum "E" [("a", 0, []), ("b", 1, [])]) = "{\"enum\":[\"a\",\"b\"]}"
-- a sum with a field is an object; its cases with no field share one branch
#guard schemaIn {} (.sum "E" [("a", 0, []), ("b", 1, []), ("c", 2, [("x", .bool)])]) =
  "{\"type\":\"object\",\"oneOf\":[{\"properties\":{\"_tag\":{\"enum\":[\"a\",\"b\"]}},\"required\":[\"_tag\"],\
\"additionalProperties\":false},{\"properties\":{\"_tag\":{\"const\":\"c\"},\"x\":{\"type\":\"boolean\"}},\
\"required\":[\"_tag\",\"x\"],\"additionalProperties\":false}]}"
-- a structure met in two places is written once, by its name; met in one place, it stays there
#guard argumentSchema [] [] [("x", .struct "P" [("v", .bool)]), ("y", .option (.struct "P" [("v", .bool)]))] =
  "{\"type\":\"object\",\"properties\":{\"x\":{\"$ref\":\"#/$defs/P\"},\"y\":{\"anyOf\":[{\"type\":\"null\"},\
{\"$ref\":\"#/$defs/P\"}]}},\"required\":[\"x\",\"y\"],\"additionalProperties\":false,\"$defs\":{\"P\":\
{\"type\":\"object\",\"properties\":{\"v\":{\"type\":\"boolean\"}},\"required\":[\"v\"],\"additionalProperties\":false}}}"
#guard argumentSchema [] [] [("x", .struct "P" [("v", .bool)])] =
  "{\"type\":\"object\",\"properties\":{\"x\":{\"type\":\"object\",\"properties\":{\"v\":{\"type\":\"boolean\"}},\
\"required\":[\"v\"],\"additionalProperties\":false}},\"required\":[\"x\"],\"additionalProperties\":false}"
-- a table definition written as an object is left to `describe`, which spells it
#guard argumentSchema [("T", .struct "T" [("v", .option (.named "T"))])] [] [("x", .named "T")] =
  "{\"type\":\"object\",\"properties\":{\"x\":{\"$ref\":\"#/$defs/T\"}},\"required\":[\"x\"],\
\"additionalProperties\":false,\"$defs\":{\"T\":{\"type\":\"object\",\"description\":\"" ++ onDemandText ++ "\"}}}"
#guard definitionSchema [("T", .struct "T" [("v", .option (.named "T"))])] "T" =
  "{\"$ref\":\"#/$defs/T\",\"$defs\":{\"T\":{\"type\":\"object\",\"properties\":{\"v\":{\"anyOf\":\
[{\"type\":\"null\"},{\"$ref\":\"#/$defs/T\"}]}},\"required\":[\"v\"],\"additionalProperties\":false}}}"
-- a list family is spelled where it is named
#guard !onDemand (.sum "L" [("nil", 0, []), ("cons", 1, [("head", .nat), ("tail", .named "L")])])
-- at the real table: the grammar is `describe`'s, and no method's schema spells it
#guard describe.answers.map (·.1) = ["Ty", "Eff", "Stmt", "ActionTerm", "LayerTerm", "Term", "CauseTerm", "Val"]
#guard entries.all fun e => (e.schema.splitOn "withFiber").length == 1
#guard (describe.answers.lookup "Eff").any fun s => (s.splitOn "withFiber").length == 2
#guard describe.answers.all fun a => (a.2.splitOn onDemandText).length == 1
-- `dry`'s action names the action tools' cases and leaves their arguments to them
#guard (entries.find? (·.name == "dry")).any fun e =>
  (e.schema.splitOn toolCallText).length == 2 && (e.schema.splitOn "\"$defs\"").length == 1
#guard quote "abc" = "\"abc\""

end Test.Program.ToolMethodsControls
