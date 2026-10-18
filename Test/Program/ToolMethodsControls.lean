import Effect4.Tool.Methods

/-!
# The tool table's controls (`Tool/Methods.lean`)

Finite evaluations of the derived table at the real `Request` shape: it lists every supported
method once, in the order of `supportedMethods`; each method's name is `Request.method`'s for its
case; every method has a description; and a schema reads as the profile prints. Readers of the
JSON text itself stay inside the guards.
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
#guard (descriptions.map (·.2.2) ++ entries.map (·.caseName) ++ entries.map (·.name)).all fun t =>
  t.all fun c => c != '"' && c != '\\' && c.toNat ≥ 32
#guard (Effect4.Store.shape Request).defs.all fun d => d.1.all fun c => c != '"' && c != '\\' && c != '~' && c != '/'
#guard toString Effect4.Tool.CodecProfile.natLimit = "9007199254740991"
-- schemas: an object of the case's fields, with what they reach under $defs
#guard (entries.find? (·.name == "reset")).map (·.schema) =
  some "{\"type\":\"object\",\"properties\":{},\"required\":[],\"additionalProperties\":false}"
#guard (entries.find? (·.name == "slots")).any fun e =>
  (e.schema.splitOn "\"required\":[\"at_\",\"slot\"]").length == 2
#guard (entries.find? (·.name == "open")).any fun e =>
  (e.schema.splitOn "\"$defs\"").length == 2 && (e.schema.splitOn "\"required\":[\"name\",\"app\",\"sketch\"]").length == 2
-- the profile's naturals and nullary sums
#guard schemaIn .nat = "{\"type\":\"integer\",\"minimum\":0,\"maximum\":9007199254740991}"
#guard schemaIn (.sum "E" [("a", 0, []), ("b", 1, [])]) = "{\"enum\":[\"a\",\"b\"]}"
#guard quote "abc" = "\"abc\""

end Test.Program.ToolMethodsControls
