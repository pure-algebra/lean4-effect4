import Cas.Vectors.Schema

/-!
# Typed foreign representation

The vector wire carrier has three linked, independently inspectable
surfaces: its Lean type, canonical schema code, and public
TypeScript/Effect Schema representation.
-/

namespace CasExamples.ForeignRepresentation

open Cas.Schema.Foreign
open Cas.Vectors

example : RepresentedIn Wire.VectorDocument .typeScript := inferInstance

example :
    (representationOf Wire.VectorDocument .typeScript).schema = vectorAst := by
  rfl

example :
    (TypeScript.effectSchemaType Wire.VectorDocument).render =
      "Schema.Codec<Cas.ConformanceVector.ConformanceVector, typeof Cas.ConformanceVector.ConformanceVector.Encoded, never, never>" :=
  vector_effect_schema_type

end CasExamples.ForeignRepresentation
