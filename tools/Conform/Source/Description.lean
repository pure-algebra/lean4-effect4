import Lean

/-!
Ground source descriptions shared by program generators and inspection tools. The caller
supplies the finite nominal registry and types whose instance parameter denotes a canonical
row constraint. Unsupported dependent/function/value arguments refuse at the field path.
No target carrier or Effect4 declaration is selected here.
-/
namespace Conform.Source
open Lean Meta

inductive Shape where
  | nat | bool | string | unit
  | option (inner : Shape)
  | list (inner : Shape)
  | prod (left right : Shape)
  | nominal (name : Name) (parameters : List Shape)
  | canonicalRow (inner : Shape)
  deriving BEq, Repr, Inhabited

structure Spec where
  leanName : Name
  label : String
  parameters : List Name := []
  deriving BEq, Inhabited

structure Config where
  specs : List Spec
  canonicalRows : List Name := []

def groundType (spec : Spec) : Expr :=
  mkAppN (mkConst spec.leanName) (spec.parameters.map mkConst).toArray

/-- Bounded source extraction refuses function/dependent/free-variable fields explicitly. -/
def readShape (cfg : Config) : Nat → String → Expr → MetaM Shape
  | 0, path, _ => throwError "ProgramStructure: depth limit at {path}"
  | fuel + 1, path, raw => do
    let e ← whnfR raw
    let .const n _ := e.getAppFn | throwError "ProgramStructure: unsupported field {path}: {e}"
    let args := e.getAppArgs
    if n == ``Nat then return .nat
    if n == ``Bool then return .bool
    if n == ``String then return .string
    if n == ``Unit || n == ``PUnit then return .unit
    if n == ``Option && args.size == 1 then return .option (← readShape cfg fuel path args[0]!)
    if n == ``List && args.size == 1 then return .list (← readShape cfg fuel path args[0]!)
    if n == ``Prod && args.size == 2 then
      return .prod (← readShape cfg fuel path args[0]!) (← readShape cfg fuel path args[1]!)
    if cfg.canonicalRows.contains n then return .canonicalRow (← readShape cfg fuel path args[0]!)
    let some spec := cfg.specs.find? (·.leanName == n)
      | throwError "ProgramStructure: unsupported nominal at {path}: {e}"
    unless args.toList == spec.parameters.map mkConst do
      throwError "ProgramStructure: unsupported instantiation at {path}: {e}"
    return .nominal n (← args.toList.mapM (readShape cfg fuel path))

structure Field where
  name : String
  shape : Shape
  deriving BEq, Inhabited
structure Ctor where
  name : Name
  fields : List Field
  index : Nat
  deriving BEq, Inhabited
structure Family where
  spec : Spec
  isStruct : Bool
  constructors : List Ctor
  deriving BEq, Inhabited

/-- One constructor telescope, shared by source and layout readers. -/
def withConstructor {α : Type} (name : Name)
    (read : ConstructorVal → Array Expr → MetaM α) : MetaM α := do
  let ci ← getConstInfoCtor name
  forallBoundedTelescope ci.type (ci.numParams + ci.numFields) fun xs _ => read ci xs

def readFamily (cfg : Config) (spec : Spec) : MetaM Family := do
  let env ← getEnv
  let info ← getConstInfoInduct spec.leanName
  unless info.numParams == spec.parameters.length do
    throwError "ProgramStructure: wrong parameter count at {spec.leanName}"
  let constructors ← info.ctors.mapM fun name => do
    withConstructor name fun ci xs => do
      let parameters := xs[0:info.numParams].toArray
      let mut fields := []
      for x in xs[info.numParams:] do
        let raw ← inferType x
        if ← isProp raw then continue
        let fieldName ← x.fvarId!.getUserName
        let instantiated := raw.replaceFVars parameters (spec.parameters.map mkConst).toArray
        let shape ← readShape cfg 128 s!"{spec.leanName}.{fieldName}" instantiated
        fields := fields ++ [⟨fieldName.toString, shape⟩]
      return ⟨name, fields, ci.cidx⟩
  return ⟨spec, isStructure env spec.leanName, constructors⟩

def shapeJson : Nat → Shape → Except String Json
  | 0, _ => .error "ProgramStructure: JSON depth exceeded"
  | fuel + 1, shape => do
    let tag (name : String) (fields : List (String × Json) := []) :=
      Json.mkObj (("kind", Json.str name) :: fields)
    match shape with
    | .nat => return tag "nat"
    | .bool => return tag "bool"
    | .string => return tag "string"
    | .unit => return tag "unit"
    | .option a => return tag "option" [("inner", ← shapeJson fuel a)]
    | .list a => return tag "list" [("inner", ← shapeJson fuel a)]
    | .prod a b => return tag "prod" [("left", ← shapeJson fuel a), ("right", ← shapeJson fuel b)]
    | .canonicalRow a => return tag "canonicalRow" [("inner", ← shapeJson fuel a)]
    | .nominal name args => return tag "nominal" [("name", .str name.toString),
        ("parameters", .arr (← args.mapM (shapeJson fuel)).toArray)]

def familyJson (family : Family) : Except String Json := do
  let constructors ← family.constructors.mapM fun ctor => do
    let fields ← ctor.fields.mapM fun field => do
      return Json.mkObj [("name", .str field.name), ("shape", ← shapeJson 256 field.shape)]
    return Json.mkObj [("name", .str ctor.name.toString), ("ordinal", toJson ctor.index),
      ("fields", .arr fields.toArray)]
  return Json.mkObj [("name", .str family.spec.leanName.toString),
    ("label", .str family.spec.label),
    ("parameters", toJson (family.spec.parameters.map Name.toString)),
    ("structure", toJson family.isStruct), ("constructors", .arr constructors.toArray)]

def descriptorJson (format : String) (families : List (List Family)) : Except String Json := do
  let bs ← families.mapM fun block => return Json.arr (← block.mapM familyJson).toArray
  return Json.mkObj [("format", .str format),
    ("phase", .str "ground-source-declaration"), ("blocks", .arr bs.toArray)]

end Conform.Source
