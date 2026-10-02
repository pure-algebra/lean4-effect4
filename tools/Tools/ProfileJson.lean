import Effect4.Program.Eff
import Lean.Data.Json

/-!
# JSON views of the existing type and row data

Shared by the TypeScript profile writer and truth metadata. This is tooling, not a new
stored type or program representation. Constructor/field names follow the generated
Program schemas. JSON escaping and numeric spelling belong to Lean.Json.
Properties: total constructor coverage by construction; target schema acceptance tested
by the TypeScript and target-diagnostic gates. No target type is inferred from a dotted name.
-/

namespace Tools.ProfileJson

open Lean Effect4.Program

def tagged (name : String) (fields : List (String × Json)) : Json :=
  Json.mkObj (("_tag", Json.str name) :: fields)

mutual
def tyJson : Ty → Json
  | .never => tagged "never" []
  | .unknown => tagged "unknown" []
  | .unit => tagged "unit" []
  | .nat => tagged "nat" []
  | .int => tagged "int" []
  | .string => tagged "string" []
  | .bool => tagged "bool" []
  | .handle target => tagged "handle" [("target", .str target)]
  | .option inner => tagged "option" [("inner", tyJson inner)]
  | .list inner => tagged "list" [("inner", tyJson inner)]
  | .prod left right => tagged "prod" [("left", tyJson left), ("right", tyJson right)]
  | .except error value => tagged "except" [("error", tyJson error), ("value", tyJson value)]
  | .exitOf value error => tagged "exitOf" [("value", tyJson value), ("error", tyJson error)]
  | .causeOf error => tagged "causeOf" [("error", tyJson error)]
  | .fiberOf value error => tagged "fiberOf" [("value", tyJson value), ("error", tyJson error)]
  | .union left right => tagged "union" [("left", tyJson left), ("right", tyJson right)]
  | .lit value => tagged "lit" [("value", .str value)]
  | .refOf value => tagged "refOf" [("value", tyJson value)]
  | .deferredOf value error => tagged "deferredOf" [("value", tyJson value), ("error", tyJson error)]
  | .var index => tagged "var" [("index", .num index)]
  | .record fields => tagged "record" [("fields", Json.arr (fieldsJson fields).toArray)]
  | .map key value => tagged "map" [("key", tyJson key), ("value", tyJson value)]
  | .tuple items => tagged "tuple" [("items", Json.arr (itemsJson items).toArray)]
  | .app name args => tagged "app" [("name", .str name), ("args", Json.arr (itemsJson args).toArray)]
  | .null => tagged "null" []
  | .undefined => tagged "undefined" []
  | .number => tagged "number" []
  | .bytes => tagged "bytes" []
/-- A record's fields: each `String × Bool × Ty` a nested pair, `[name, [optional, type]]`, the
generated codec's product spelling. -/
def fieldsJson : List (String × Bool × Ty) → List Json
  | [] => []
  | (n, o, t) :: rest => Json.arr #[.str n, Json.arr #[.bool o, tyJson t]] :: fieldsJson rest
/-- A tuple's or a reference's items. -/
def itemsJson : List Ty → List Json
  | [] => []
  | t :: rest => tyJson t :: itemsJson rest
end

def shapeJson : RowShape → Json
  | .call => .str "call"
  | .value => .str "value"
  | .tupleCall => .str "tupleCall"
  | .method => .str "method"

def registrationJson : Registration → Json
  | .deferred => .str "deferred"
  | .external => .str "external"

def kindJson : RowKind → Json
  | .sync => .str "sync"
  | .async => .str "async"
  | .program => .str "program"

def keyJson (key : Effect4.ServiceKey) : Json :=
  Json.mkObj [("name", Json.mkObj [("value", toJson key.name.value)]),
    ("service", Json.mkObj [("value", toJson key.service.value)])]

def flatKeyJson (key : Effect4.ServiceKey) : Json :=
  Json.mkObj [("name", toJson key.name.value), ("service", toJson key.service.value)]

def rowJson (row : Row) : Json :=
  Json.mkObj [("name", .str row.name), ("spelling", .str row.spelling),
    ("shape", shapeJson row.shape), ("trailing", toJson row.trailing),
    ("kind", kindJson row.kind), ("request", tyJson row.request),
    ("answer", tyJson row.answer), ("error", tyJson row.error),
    ("requires", .arr (row.requires.map keyJson).toArray), ("cite", .str row.cite),
    ("typeArgs", toJson row.typeArgs), ("registration", registrationJson row.registration)]

end Tools.ProfileJson
