import Cas.Schema.Described

/-!
# Foreign-language type representations

`Described α` says what a Lean type means on the schema plane. This
module records the corresponding type and codec surface in another
language without reducing either side to an unstructured string.

TypeScript is the first target. Its codec record models the important
Effect v4 distinction between decoded type, encoded type, decoding
services, and encoding services.
-/

namespace Cas.Schema.Foreign

namespace TypeScript

/-- A dotted TypeScript name such as `Schema.Schema` or
`Cas.ConformanceVector.VectorIndex`. -/
structure QualifiedName where
  parts : List String
  nonempty : parts ≠ []

namespace QualifiedName

def render (name : QualifiedName) : String :=
  String.intercalate "." name.parts

end QualifiedName

/-- The small, structural TypeScript type-expression language needed
to name public types and their generic codec surfaces. -/
inductive TypeExpr where
  | named (name : QualifiedName)
  | typeQueryMember (value : QualifiedName) (member : String)
  | apply (constructor : QualifiedName) (arguments : List TypeExpr)
  | array (element : TypeExpr)
  | union (alternatives : List TypeExpr)
  | stringLiteral (value : String)
  | numberLiteral (value : Int)
  | never
  | unknown
  /-- `(name: T, …) => R` — admitted for operation signatures (the
  consumer-gated fragment rule). -/
  | func (params : List (String × TypeExpr)) (result : TypeExpr)

namespace TypeExpr

mutual

def render : TypeExpr → String
  | .named name => name.render
  | .typeQueryMember value member =>
    "typeof " ++ value.render ++ "." ++ member
  | .apply constructor arguments =>
    constructor.render ++ "<" ++
      String.intercalate ", " (renderAll arguments) ++ ">"
  | .array element => "ReadonlyArray<" ++ render element ++ ">"
  | .union alternatives => String.intercalate " | " (renderAll alternatives)
  | .stringLiteral value => "\"" ++ value ++ "\""
  | .numberLiteral value => toString value
  | .never => "never"
  | .unknown => "unknown"
  | .func params result =>
    "(" ++ String.intercalate ", " (renderParams params) ++ ") => " ++
      render result

def renderAll : List TypeExpr → List String
  | [] => []
  | expression :: rest => render expression :: renderAll rest

def renderParams : List (String × TypeExpr) → List String
  | [] => []
  | (name, ty) :: rest => (name ++ ": " ++ render ty) :: renderParams rest

end

end TypeExpr

/-- The term-level Effect Schema value and its two service channels.
Decoded and encoded types live on the enclosing foreign representation
so the same pair can also describe non-Effect codecs later. -/
structure EffectSchemaRef where
  value : QualifiedName
  decodingServices : TypeExpr := .never
  encodingServices : TypeExpr := .never

/-- Render Effect v4's full
`Schema.Codec<Decoded, Encoded, DecodingServices, EncodingServices>`. -/
def EffectSchemaRef.schemaType (schema : EffectSchemaRef)
    (decoded encoded : TypeExpr) : TypeExpr :=
  .apply ⟨["Schema", "Codec"], by simp⟩
    [decoded, encoded, schema.decodingServices, schema.encodingServices]

end TypeScript

/-- Languages with a structured representation model. -/
inductive Language where
  | typeScript

def Language.TypeExpr : Language → Type
  | .typeScript => TypeScript.TypeExpr

def Language.CodecRef : Language → Type
  | .typeScript => TypeScript.EffectSchemaRef

/-- One language's decoded type, encoded type, and codec value. -/
structure Representation (language : Language) where
  decoded : language.TypeExpr
  encoded : language.TypeExpr
  codec : language.CodecRef

/-- Attach a foreign representation to a described Lean carrier. -/
class RepresentedIn (α : Type u) (language : Language) [Described α] where
  representation : Representation language

/-- The complete correspondence surface: canonical schema code plus
the typed foreign-language representation. -/
structure TypeRepresentation (language : Language) where
  schema : Ast
  foreign : Representation language

def representationOf (α : Type u) (language : Language)
    [Described α] [represented : RepresentedIn α language] :
    TypeRepresentation language where
  schema := Described.code (α := α)
  foreign := represented.representation

namespace TypeScript

abbrev Represented (α : Type u) [Described α] :=
  RepresentedIn α .typeScript

def representation (α : Type u) [Described α] [Represented α] :
    Representation .typeScript :=
  RepresentedIn.representation (α := α) (language := .typeScript)

def effectSchemaType (α : Type u) [Described α] [Represented α] : TypeExpr :=
  let rep := representation α
  rep.codec.schemaType rep.decoded rep.encoded

end TypeScript

end Cas.Schema.Foreign
