/-
Contract packet: `test/contracts/schema-recursor.contract.md`

Breaker-owned red battery for
`SCHEMA-PG-PAYLOAD/SC-REP-03-RECURSOR`. The builder must make this file green
without editing it. The battery freezes one pure, two-sorted fold over the
existing `Representation`/`Check` family and the public computation law for
every constructor. It adds no syntax or denotation carrier.
-/

import Effect4.Schema.Representation

namespace Test.Schema.RepresentationFoldContract

open Effect4

/-! ## F0 — the sole algebra and the two eliminators -/

example : Type -> Type -> Type :=
  Representation.FoldAlgebra

example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    RepresentationAnnotation -> Annotations -> List rho -> List kappa -> rho :=
  algebra.declaration

example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) : ReferenceKey -> rho :=
  algebra.reference

example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> rho -> rho := algebra.suspend

example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> rho := algebra.null
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> rho := algebra.undefined
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> rho := algebra.void
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> rho := algebra.never
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> rho := algebra.unknown
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> rho := algebra.any
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> rho := algebra.string
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> rho := algebra.number
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> rho := algebra.boolean
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> rho := algebra.bigint
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> rho := algebra.symbol

example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> LiteralValue -> rho := algebra.literal
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> GlobalSymbolKey -> rho := algebra.uniqueSymbol
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> rho := algebra.objectKeyword
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> List EnumEntry -> rho := algebra.enum
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> List rho -> rho := algebra.templateLiteral
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> List (ElementOf rho) -> List rho -> rho :=
  algebra.arrays
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> List (PropertySignatureOf rho) ->
      List (IndexSignatureOf rho) -> rho :=
  algebra.objects
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Annotations -> List kappa -> List rho -> UnionMode -> rho := algebra.union

example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    CheckRepresentationAnnotationOf rho -> Annotations -> Bool -> kappa :=
  algebra.filter
example {rho kappa : Type}
    (algebra : Representation.FoldAlgebra rho kappa) :
    Option (CheckRepresentationAnnotationOf rho) -> Annotations ->
      List kappa -> kappa :=
  algebra.filterGroup

example {rho kappa : Type} :
    Representation.FoldAlgebra rho kappa -> Representation -> rho :=
  Representation.fold

example {rho kappa : Type} :
    Representation.FoldAlgebra rho kappa -> Check -> kappa :=
  Check.fold

example : Representation.FoldAlgebra Representation Check :=
  Representation.FoldAlgebra.rebuild

example (representation : Representation) :
    Representation.fold Representation.FoldAlgebra.rebuild representation =
      representation :=
  Representation.fold_rebuild representation

example (check : Check) :
    Check.fold Representation.FoldAlgebra.rebuild check = check :=
  Check.fold_rebuild check

/-! The names below are part of the public simp surface. -/

#check @Representation.fold_declaration
#check @Representation.fold_reference
#check @Representation.fold_suspend
#check @Representation.fold_null
#check @Representation.fold_undefined
#check @Representation.fold_void
#check @Representation.fold_never
#check @Representation.fold_unknown
#check @Representation.fold_any
#check @Representation.fold_string
#check @Representation.fold_number
#check @Representation.fold_boolean
#check @Representation.fold_bigint
#check @Representation.fold_symbol
#check @Representation.fold_literal
#check @Representation.fold_uniqueSymbol
#check @Representation.fold_objectKeyword
#check @Representation.fold_enum
#check @Representation.fold_templateLiteral
#check @Representation.fold_arrays
#check @Representation.fold_objects
#check @Representation.fold_union
#check @Check.fold_filter
#check @Check.fold_filterGroup

/-! ## F1 — representation constructor equations -/

section Equations

variable {rho kappa : Type}
variable (algebra : Representation.FoldAlgebra rho kappa)

example (representation : RepresentationAnnotation) (annotations : Annotations)
    (typeParameters : List Representation) (checks : List Check) :
    Representation.fold algebra
        (.declaration representation annotations typeParameters checks) =
      algebra.declaration representation annotations
        (typeParameters.map (Representation.fold algebra))
        (checks.map (Check.fold algebra)) := by
  simp

example (ref : ReferenceKey) :
    Representation.fold algebra (.reference ref) = algebra.reference ref := by
  simp

example (annotations : Annotations) (checks : List Check)
    (thunk : Representation) :
    Representation.fold algebra (.suspend annotations checks thunk) =
      algebra.suspend annotations (checks.map (Check.fold algebra))
        (Representation.fold algebra thunk) := by
  simp

example (annotations : Annotations) (checks : List Check) :
    Representation.fold algebra (.null annotations checks) =
      algebra.null annotations (checks.map (Check.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check) :
    Representation.fold algebra (.undefined annotations checks) =
      algebra.undefined annotations (checks.map (Check.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check) :
    Representation.fold algebra (.void annotations checks) =
      algebra.void annotations (checks.map (Check.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check) :
    Representation.fold algebra (.never annotations checks) =
      algebra.never annotations (checks.map (Check.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check) :
    Representation.fold algebra (.unknown annotations checks) =
      algebra.unknown annotations (checks.map (Check.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check) :
    Representation.fold algebra (.any annotations checks) =
      algebra.any annotations (checks.map (Check.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check) :
    Representation.fold algebra (.string annotations checks) =
      algebra.string annotations (checks.map (Check.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check) :
    Representation.fold algebra (.number annotations checks) =
      algebra.number annotations (checks.map (Check.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check) :
    Representation.fold algebra (.boolean annotations checks) =
      algebra.boolean annotations (checks.map (Check.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check) :
    Representation.fold algebra (.bigint annotations checks) =
      algebra.bigint annotations (checks.map (Check.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check) :
    Representation.fold algebra (.symbol annotations checks) =
      algebra.symbol annotations (checks.map (Check.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check)
    (value : LiteralValue) :
    Representation.fold algebra (.literal annotations checks value) =
      algebra.literal annotations (checks.map (Check.fold algebra)) value := by
  simp

example (annotations : Annotations) (checks : List Check)
    (key : GlobalSymbolKey) :
    Representation.fold algebra (.uniqueSymbol annotations checks key) =
      algebra.uniqueSymbol annotations (checks.map (Check.fold algebra)) key := by
  simp

example (annotations : Annotations) (checks : List Check) :
    Representation.fold algebra (.objectKeyword annotations checks) =
      algebra.objectKeyword annotations (checks.map (Check.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check)
    (entries : List EnumEntry) :
    Representation.fold algebra (.enum annotations checks entries) =
      algebra.enum annotations (checks.map (Check.fold algebra)) entries := by
  simp

example (annotations : Annotations) (checks : List Check)
    (parts : List Representation) :
    Representation.fold algebra (.templateLiteral annotations checks parts) =
      algebra.templateLiteral annotations (checks.map (Check.fold algebra))
        (parts.map (Representation.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check)
    (elements : List (ElementOf Representation)) (rest : List Representation) :
    Representation.fold algebra (.arrays annotations checks elements rest) =
      algebra.arrays annotations (checks.map (Check.fold algebra))
        (elements.map fun element =>
          { isOptional := element.isOptional
            type := Representation.fold algebra element.type
            annotations := element.annotations })
        (rest.map (Representation.fold algebra)) := by
  simp

example (annotations : Annotations) (checks : List Check)
    (properties : List (PropertySignatureOf Representation))
    (indexes : List (IndexSignatureOf Representation)) :
    Representation.fold algebra (.objects annotations checks properties indexes) =
      algebra.objects annotations (checks.map (Check.fold algebra))
        (properties.map fun property =>
          { name := property.name
            type := Representation.fold algebra property.type
            isOptional := property.isOptional
            isMutable := property.isMutable
            annotations := property.annotations })
        (indexes.map fun index =>
          { parameter := Representation.fold algebra index.parameter
            type := Representation.fold algebra index.type }) := by
  simp

example (annotations : Annotations) (checks : List Check)
    (types : List Representation) (mode : UnionMode) :
    Representation.fold algebra (.union annotations checks types mode) =
      algebra.union annotations (checks.map (Check.fold algebra))
        (types.map (Representation.fold algebra)) mode := by
  simp

/-! ## F2 — check equations, including both nested-schema routes -/

example (representation : CheckRepresentationAnnotationOf Representation)
    (annotations : Annotations) (aborted : Bool) :
    Check.fold algebra (.filter representation annotations aborted) =
      algebra.filter
        { id := representation.id
          payload := representation.payload
          schemas := representation.schemas.map
            (List.map (Representation.fold algebra)) }
        annotations aborted := by
  simp

example
    (representation : Option (CheckRepresentationAnnotationOf Representation))
    (annotations : Annotations) (checks : List Check) :
    Check.fold algebra (.filterGroup representation annotations checks) =
      algebra.filterGroup
        (representation.map fun value =>
          { id := value.id
            payload := value.payload
            schemas := value.schemas.map
              (List.map (Representation.fold algebra)) })
        annotations (checks.map (Check.fold algebra)) := by
  simp

end Equations

/-!
No law above assigns meaning to a folded result. They state only exhaustive
structural substitution and are therefore the exact reusable boundary needed
by later analyzers and denotational algebras.
-/

end Test.Schema.RepresentationFoldContract
