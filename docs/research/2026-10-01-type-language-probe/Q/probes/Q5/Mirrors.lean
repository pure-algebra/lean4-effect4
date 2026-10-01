import OCaml5.Eff.Goldens
import Tools.ProfileJson
import Conform.Effect4.LcnfMl
import Conform.Effect4.LcnfSemantics
import ProbeQW.Ty

/-!
# Seat Q, question 5: the six Lean mirrors of `Ty`, copied over the wave family

Each function below is a copy of a tree mirror (named beside it) with its twenty arms unchanged
(the namespace of the constructor names aside) and the eight arms the wave adds, so the lines
each mirror gains are measured by compiling them. The spellings of the new arms follow each
mirror's own rule for the carrier: a `List (String × Ty × Bool)` is the list of nested pairs the
rule already prints for a `List` and a `Prod` (the V tree, the OCaml literal of the EffGen type
`(string * (ty * bool)) list`, the target and mono-LCNF values). `tyJson`'s record spelling is
an assumption (seat S owns the profile's spelling).
-/

set_option autoImplicit false

namespace ProbeQ5M
open Lean ProbeQW
open OCaml5.Eff (octor ostr V)
open Tools.ProfileJson (tagged)
open Conform.Lcnf.Target (TValue)
open Conform.Lcnf (Value)

/-- `OCaml5.Eff.tyO` (`src/OCaml5/Eff/Emit.lean:366`). -/
def tyO : Ty → String
  | .never => octor "ty" "never"
  | .unknown => octor "ty" "unknown"
  | .unit => octor "ty" "unit"
  | .nat => octor "ty" "nat"
  | .int => octor "ty" "int"
  | .string => octor "ty" "string"
  | .bool => octor "ty" "bool"
  | .handle target => s!"({octor "ty" "handle"} {ostr target})"
  | .option inner => s!"({octor "ty" "option"} {tyO inner})"
  | .list inner => s!"({octor "ty" "list"} {tyO inner})"
  | .prod l r => s!"({octor "ty" "prod"} ({tyO l}, {tyO r}))"
  | .except e v => s!"({octor "ty" "except"} ({tyO e}, {tyO v}))"
  | .exitOf v e => s!"({octor "ty" "exitOf"} ({tyO v}, {tyO e}))"
  | .causeOf e => s!"({octor "ty" "causeOf"} {tyO e})"
  | .fiberOf v e => s!"({octor "ty" "fiberOf"} ({tyO v}, {tyO e}))"
  | .union l r => s!"({octor "ty" "union"} ({tyO l}, {tyO r}))"
  | .lit s => s!"({octor "ty" "lit"} {ostr s})"
  | .refOf v => s!"({octor "ty" "refOf"} {tyO v})"
  | .deferredOf v e => s!"({octor "ty" "deferredOf"} ({tyO v}, {tyO e}))"
  | .var i => s!"({octor "ty" "var"} {i})"
  -- the wave
  | .record fs => s!"({octor "ty" "record"} [{"; ".intercalate (fs.attach.map fun ⟨(n, t, o), h⟩ =>
      have : sizeOf t < 1 + sizeOf fs := by
        have h' : sizeOf t < sizeOf fs := Ty.sizeOf_field_lt h
        omega
      s!"({ostr n}, ({tyO t}, {o}))")}])"
  | .map k v => s!"({octor "ty" "map"} ({tyO k}, {tyO v}))"
  | .tuple xs => s!"({octor "ty" "tuple"} [{"; ".intercalate (xs.attach.map fun ⟨x, _⟩ => tyO x)}])"
  | .app n xs => s!"({octor "ty" "app"} ({ostr n}, [{"; ".intercalate (xs.attach.map fun ⟨x, _⟩ => tyO x)}]))"
  | .null => octor "ty" "null"
  | .undefined => octor "ty" "undefined"
  | .number => octor "ty" "number"
  | .bytes => octor "ty" "bytes"

/-- `OCaml5.Eff.tyV` (`src/OCaml5/Eff/Goldens.lean:89`). -/
def tyV : Ty → V
  | .never => .ctor ``Ty.never []
  | .unknown => .ctor ``Ty.unknown []
  | .unit => .ctor ``Ty.unit []
  | .nat => .ctor ``Ty.nat []
  | .int => .ctor ``Ty.int []
  | .string => .ctor ``Ty.string []
  | .bool => .ctor ``Ty.bool []
  | .handle target => .ctor ``Ty.handle [.str target]
  | .option inner => .ctor ``Ty.option [tyV inner]
  | .list inner => .ctor ``Ty.list [tyV inner]
  | .prod l r => .ctor ``Ty.prod [tyV l, tyV r]
  | .except e v => .ctor ``Ty.except [tyV e, tyV v]
  | .exitOf v e => .ctor ``Ty.exitOf [tyV v, tyV e]
  | .causeOf e => .ctor ``Ty.causeOf [tyV e]
  | .fiberOf v e => .ctor ``Ty.fiberOf [tyV v, tyV e]
  | .union l r => .ctor ``Ty.union [tyV l, tyV r]
  | .lit s => .ctor ``Ty.lit [.str s]
  | .refOf v => .ctor ``Ty.refOf [tyV v]
  | .deferredOf v e => .ctor ``Ty.deferredOf [tyV v, tyV e]
  | .var i => .ctor ``Ty.var [.nat i]
  -- the wave
  | .record fs => .ctor ``Ty.record [.list (fs.attach.map fun ⟨(n, t, o), h⟩ =>
      have : sizeOf t < 1 + sizeOf fs := by
        have h' : sizeOf t < sizeOf fs := Ty.sizeOf_field_lt h
        omega
      .pair (.str n) (.pair (tyV t) (.bool o)))]
  | .map k v => .ctor ``Ty.map [tyV k, tyV v]
  | .tuple xs => .ctor ``Ty.tuple [.list (xs.attach.map fun ⟨x, _⟩ => tyV x)]
  | .app n xs => .ctor ``Ty.app [.str n, .list (xs.attach.map fun ⟨x, _⟩ => tyV x)]
  | .null => .ctor ``Ty.null []
  | .undefined => .ctor ``Ty.undefined []
  | .number => .ctor ``Ty.number []
  | .bytes => .ctor ``Ty.bytes []

/-- `Tools.ProfileJson.tyJson` (`tools/Tools/ProfileJson.lean:21`). -/
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
  -- the wave (the record's spelling is an assumption: seat S owns the profile)
  | .record fields => tagged "record" [("fields", .arr (fields.attach.map fun ⟨(n, t, o), h⟩ =>
      have : sizeOf t < 1 + sizeOf fields := by
        have h' : sizeOf t < sizeOf fields := Ty.sizeOf_field_lt h
        omega
      Json.mkObj [("name", .str n), ("type", tyJson t), ("optional", .bool o)]).toArray)]
  | .map key value => tagged "map" [("key", tyJson key), ("value", tyJson value)]
  | .tuple items => tagged "tuple" [("items", .arr (items.attach.map fun ⟨x, _⟩ => tyJson x).toArray)]
  | .app name args => tagged "app" [("name", .str name), ("args", .arr (args.attach.map fun ⟨x, _⟩ => tyJson x).toArray)]
  | .null => tagged "null" []
  | .undefined => tagged "undefined" []
  | .number => tagged "number" []
  | .bytes => tagged "bytes" []

/-- `Conform.Effect4.LcnfMl.tyCtor`, over the wave family. -/
def tyCtor (c : String) : String := OCaml5.Lcnf.ctorName ``Ty c

/-- `Conform.Effect4.LcnfMl.tyT` (`tools/Conform/Effect4/LcnfMl.lean:164`). -/
def tyT : Ty → TValue
  | .never => .ctorV (tyCtor "never") #[]
  | .unit => .ctorV (tyCtor "unit") #[]
  | .nat => .ctorV (tyCtor "nat") #[]
  | .int => .ctorV (tyCtor "int") #[]
  | .string => .ctorV (tyCtor "string") #[]
  | .bool => .ctorV (tyCtor "bool") #[]
  | .handle t => .ctorV (tyCtor "handle") #[.str t]
  | .option i => .ctorV (tyCtor "option") #[tyT i]
  | .list i => .ctorV (tyCtor "list") #[tyT i]
  | .prod l r => .ctorV (tyCtor "prod") #[tyT l, tyT r]
  | .except e v => .ctorV (tyCtor "except") #[tyT e, tyT v]
  | .exitOf v e => .ctorV (tyCtor "exitOf") #[tyT v, tyT e]
  | .causeOf e => .ctorV (tyCtor "causeOf") #[tyT e]
  | .fiberOf v e => .ctorV (tyCtor "fiberOf") #[tyT v, tyT e]
  | .union l r => .ctorV (tyCtor "union") #[tyT l, tyT r]
  | .lit s => .ctorV (tyCtor "lit") #[.str s]
  | .refOf v => .ctorV (tyCtor "refOf") #[tyT v]
  | .deferredOf v e => .ctorV (tyCtor "deferredOf") #[tyT v, tyT e]
  | .var i => .ctorV (tyCtor "var") #[.int i]
  | .unknown => .ctorV (tyCtor "unknown") #[]
  -- the wave
  | .record fs => .ctorV (tyCtor "record") #[TValue.ofList (fs.attach.map fun ⟨(n, t, o), h⟩ =>
      have : sizeOf t < 1 + sizeOf fs := by
        have h' : sizeOf t < sizeOf fs := Ty.sizeOf_field_lt h
        omega
      .tupleV #[.str n, .tupleV #[tyT t, .bool o]])]
  | .map k v => .ctorV (tyCtor "map") #[tyT k, tyT v]
  | .tuple xs => .ctorV (tyCtor "tuple") #[TValue.ofList (xs.attach.map fun ⟨x, _⟩ => tyT x)]
  | .app n xs => .ctorV (tyCtor "app") #[.str n, TValue.ofList (xs.attach.map fun ⟨x, _⟩ => tyT x)]
  | .null => .ctorV (tyCtor "null") #[]
  | .undefined => .ctorV (tyCtor "undefined") #[]
  | .number => .ctorV (tyCtor "number") #[]
  | .bytes => .ctorV (tyCtor "bytes") #[]

/-- `Conform.Effect4.LcnfMl.tyOcaml` (`tools/Conform/Effect4/LcnfMl.lean:270`). The string
arms keep the tree's form (no escaping), so a field name with a quote is the same open defect
as `handle`'s and `lit`'s. -/
def tyOcaml : Ty → String
  | .never => tyCtor "never"
  | .unit => tyCtor "unit"
  | .nat => tyCtor "nat"
  | .int => tyCtor "int"
  | .string => tyCtor "string"
  | .bool => tyCtor "bool"
  | .handle t => tyCtor "handle" ++ " (\"" ++ t ++ "\")"
  | .option i => tyCtor "option" ++ " (" ++ tyOcaml i ++ ")"
  | .list i => tyCtor "list" ++ " (" ++ tyOcaml i ++ ")"
  | .causeOf e => tyCtor "causeOf" ++ " (" ++ tyOcaml e ++ ")"
  | .prod l r => tyCtor "prod" ++ " (" ++ tyOcaml l ++ ", " ++ tyOcaml r ++ ")"
  | .except e v => tyCtor "except" ++ " (" ++ tyOcaml e ++ ", " ++ tyOcaml v ++ ")"
  | .exitOf v e => tyCtor "exitOf" ++ " (" ++ tyOcaml v ++ ", " ++ tyOcaml e ++ ")"
  | .fiberOf v e => tyCtor "fiberOf" ++ " (" ++ tyOcaml v ++ ", " ++ tyOcaml e ++ ")"
  | .union l r => tyCtor "union" ++ " (" ++ tyOcaml l ++ ", " ++ tyOcaml r ++ ")"
  | .lit s => tyCtor "lit" ++ " (\"" ++ s ++ "\")"
  | .refOf v => tyCtor "refOf" ++ " (" ++ tyOcaml v ++ ")"
  | .deferredOf v e => tyCtor "deferredOf" ++ " (" ++ tyOcaml v ++ ", " ++ tyOcaml e ++ ")"
  | .var i => tyCtor "var" ++ " (" ++ toString i ++ ")"
  | .unknown => tyCtor "unknown"
  -- the wave
  | .record fs => tyCtor "record" ++ " ([" ++ "; ".intercalate (fs.attach.map fun ⟨(n, t, o), h⟩ =>
      have : sizeOf t < 1 + sizeOf fs := by
        have h' : sizeOf t < sizeOf fs := Ty.sizeOf_field_lt h
        omega
      "(\"" ++ n ++ "\", (" ++ tyOcaml t ++ ", " ++ toString o ++ "))") ++ "])"
  | .map k v => tyCtor "map" ++ " (" ++ tyOcaml k ++ ", " ++ tyOcaml v ++ ")"
  | .tuple xs => tyCtor "tuple" ++ " ([" ++ "; ".intercalate (xs.attach.map fun ⟨x, _⟩ => tyOcaml x) ++ "])"
  | .app n xs => tyCtor "app" ++ " (\"" ++ n ++ "\", [" ++ "; ".intercalate (xs.attach.map fun ⟨x, _⟩ => tyOcaml x) ++ "])"
  | .null => tyCtor "null"
  | .undefined => tyCtor "undefined"
  | .number => tyCtor "number"
  | .bytes => tyCtor "bytes"

/-- `Conform.Effect4.LcnfSemantics.tyValue` (`tools/Conform/Effect4/LcnfSemantics.lean:40`). -/
def tyValue : Ty → Value
  | .never => .ctor ``Ty.never #[]
  | .unit => .ctor ``Ty.unit #[]
  | .nat => .ctor ``Ty.nat #[]
  | .int => .ctor ``Ty.int #[]
  | .string => .ctor ``Ty.string #[]
  | .bool => .ctor ``Ty.bool #[]
  | .handle t => .ctor ``Ty.handle #[.str t]
  | .option i => .ctor ``Ty.option #[tyValue i]
  | .list i => .ctor ``Ty.list #[tyValue i]
  | .prod l r => .ctor ``Ty.prod #[tyValue l, tyValue r]
  | .except e v => .ctor ``Ty.except #[tyValue e, tyValue v]
  | .exitOf v e => .ctor ``Ty.exitOf #[tyValue v, tyValue e]
  | .causeOf e => .ctor ``Ty.causeOf #[tyValue e]
  | .fiberOf v e => .ctor ``Ty.fiberOf #[tyValue v, tyValue e]
  | .union l r => .ctor ``Ty.union #[tyValue l, tyValue r]
  | .lit s => .ctor ``Ty.lit #[.str s]
  | .refOf v => .ctor ``Ty.refOf #[tyValue v]
  | .deferredOf v e => .ctor ``Ty.deferredOf #[tyValue v, tyValue e]
  | .var i => .ctor ``Ty.var #[.nat i]
  | .unknown => .ctor ``Ty.unknown #[]
  -- the wave
  | .record fs => .ctor ``Ty.record #[Value.ofList (fs.attach.map fun ⟨(n, t, o), h⟩ =>
      have : sizeOf t < 1 + sizeOf fs := by
        have h' : sizeOf t < sizeOf fs := Ty.sizeOf_field_lt h
        omega
      .ctor ``Prod.mk #[.str n, .ctor ``Prod.mk #[tyValue t, Value.bool o]])]
  | .map k v => .ctor ``Ty.map #[tyValue k, tyValue v]
  | .tuple xs => .ctor ``Ty.tuple #[Value.ofList (xs.attach.map fun ⟨x, _⟩ => tyValue x)]
  | .app n xs => .ctor ``Ty.app #[.str n, Value.ofList (xs.attach.map fun ⟨x, _⟩ => tyValue x)]
  | .null => .ctor ``Ty.null #[]
  | .undefined => .ctor ``Ty.undefined #[]
  | .number => .ctor ``Ty.number #[]
  | .bytes => .ctor ``Ty.bytes #[]

def sample : Ty :=
  .record [("b", .tuple [.nat, .null], true), ("a", .app "Ref.Ref" [.map .string .number], false)]

#eval IO.println (tyO sample)
#eval IO.println (tyOcaml sample)
#eval IO.println (tyJson sample).compress

end ProbeQ5M
