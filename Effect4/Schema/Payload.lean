import Effect4.Data.Json

/-!
# Schema payload leaves

This module owns the non-recursive scalar, key, entry, annotation, and
parameterized child-record carriers used by the rc.112 persisted Schema
representation.  It deliberately imports only `Effect4.Data.Json`: tag
alphabets, recursive representation nodes, documents, admission, denotation,
and wire spellings all live above this boundary.

The carriers are permissive raw data.  Non-empty reference keys and annotation
identifiers, finite retained JSON payloads, and the other persisted field
constraints are checked later by `Effect4.Schema.Check`; they are not hidden
inside constructors here.
-/

namespace Effect4

/-- A raw `$ref` spelling. Persisted-field admission requires it non-empty. -/
structure ReferenceKey where
  value : String
deriving DecidableEq, Repr, Inhabited

/-- A portable registered global-symbol identity. Local symbols have no constructor. -/
structure GlobalSymbolKey where
  key : String
deriving DecidableEq, Repr, Inhabited

/-- One retained persisted annotation entry. -/
structure AnnotationEntry where
  key : String
  payload : Json
deriving DecidableEq

/-- An optional ordered annotation bag; absence and a present empty bag remain distinct. -/
abbrev Annotations := Option (List AnnotationEntry)

/-- A raw literal payload. Numeric finiteness is a later field-admission clause. -/
inductive LiteralValue where
  | string (value : String)
  | number (value : Float64)
  | bigint (value : Int)
  | boolean (value : Bool)
deriving DecidableEq

/-- A raw enum value. Its number leg preserves every binary64 datum. -/
inductive EnumValue where
  | string (value : String)
  | number (value : Float64)
deriving DecidableEq

/-- One ordered enum name/value pair; aliases and duplicate names remain representable. -/
structure EnumEntry where
  name : String
  value : EnumValue
deriving DecidableEq

/-- A portable raw property key. There is intentionally no local-symbol constructor. -/
inductive PropertyKey where
  | string (value : String)
  | number (value : Float64)
  | globalSymbol (value : GlobalSymbolKey)
deriving DecidableEq

/-- A declaration's representation annotation. It intentionally has no `schemas` field. -/
structure RepresentationAnnotation where
  id : String
  payload : Json
deriving DecidableEq

/-- A check annotation, parameterized so its referenced schemas do not force a mutual block. -/
structure CheckRepresentationAnnotationOf (α : Type) where
  id : String
  payload : Json
  schemas : Option (List α)
deriving DecidableEq

/-- One ordered tuple element. -/
structure ElementOf (α : Type) where
  isOptional : Bool
  type : α
  annotations : Annotations
deriving DecidableEq

/-- One ordered object property signature. -/
structure PropertySignatureOf (α : Type) where
  name : PropertyKey
  type : α
  isOptional : Bool
  isMutable : Bool
  annotations : Annotations
deriving DecidableEq

/-- One object index signature, with exactly its parameter and result types. -/
structure IndexSignatureOf (α : Type) where
  parameter : α
  type : α
deriving DecidableEq

end Effect4
