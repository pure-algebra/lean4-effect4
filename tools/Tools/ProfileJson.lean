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

def tyJson : Ty → Json
  | .never => tagged "never" []
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
