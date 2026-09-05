import Effect4.Data.Json
import Effect4.Schema.Representation
import Effect4.Schema.Document
import Effect4.Schema.Check
import Effect4.Schema.Annotations
import Effect4.Schema.EffectfulField

/-!
Fresh kernel dependency report for all six Schema representation alphabets.
-/

#print axioms Effect4.RepresentationTag.census_length
#print axioms Effect4.RepresentationTag.census_nodup
#print axioms Effect4.RepresentationTag.mem_census
#print axioms Effect4.RepresentationTag.ofTagName_tagName
#print axioms Effect4.RepresentationTag.tagName_injective
#print axioms Effect4.RepresentationTag.tagName_ofTagName

#print axioms Effect4.UnionMode.census_length
#print axioms Effect4.UnionMode.census_nodup
#print axioms Effect4.UnionMode.mem_census
#print axioms Effect4.UnionMode.ofModeName_modeName
#print axioms Effect4.UnionMode.modeName_injective
#print axioms Effect4.UnionMode.modeName_ofModeName

#print axioms Effect4.CheckTag.census_length
#print axioms Effect4.CheckTag.census_nodup
#print axioms Effect4.CheckTag.mem_census
#print axioms Effect4.CheckTag.ofTagName_tagName
#print axioms Effect4.CheckTag.tagName_injective
#print axioms Effect4.CheckTag.tagName_ofTagName

#print axioms Effect4.LiteralKind.census_length
#print axioms Effect4.LiteralKind.census_nodup
#print axioms Effect4.LiteralKind.mem_census

#print axioms Effect4.EnumValueKind.census_length
#print axioms Effect4.EnumValueKind.census_nodup
#print axioms Effect4.EnumValueKind.mem_census
#print axioms Effect4.EnumValueKind.toLiteralKind_injective
#print axioms Effect4.EnumValueKind.toLiteralKind_ne_bigint
#print axioms Effect4.EnumValueKind.toLiteralKind_ne_boolean

#print axioms Effect4.PropertyKeyKind.census_length
#print axioms Effect4.PropertyKeyKind.census_nodup
#print axioms Effect4.PropertyKeyKind.mem_census

/-!
Payload carrier, sections D0 and D1 of
`Test/contracts/schema-payload.contract.md`: the binary64 payload datum and
the raw JSON tree. Private recursive scaffolding is intentionally absent; the
report covers the exported graph obligations and leaf receipts.
-/

#print axioms Effect4.Float64.toBits_ofBits
#print axioms Effect4.Float64.ofBits_toBits
#print axioms Effect4.Float64.toBits_nan
#print axioms Effect4.Float64.toBits_posInfinity
#print axioms Effect4.Float64.toBits_negInfinity
#print axioms Effect4.Float64.toBits_zero
#print axioms Effect4.Float64.toBits_negZero
#print axioms Effect4.Float64.isFinite_nan
#print axioms Effect4.Float64.isFinite_posInfinity
#print axioms Effect4.Float64.isFinite_negInfinity
#print axioms Effect4.Float64.isFinite_zero
#print axioms Effect4.Float64.isFinite_negZero
#print axioms Effect4.Float64.negZero_ne_zero
#print axioms Effect4.Float64.isFinite_ofBits_iff
#print axioms Effect4.Float64.not_isFinite_ofBits_iff

#print axioms Effect4.Json.cases_census
#print axioms Effect4.Json.numbersFinite_null
#print axioms Effect4.Json.numbersFinite_bool
#print axioms Effect4.Json.numbersFinite_str
#print axioms Effect4.Json.numbersFinite_number_iff
#print axioms Effect4.Json.numbersFinite_arr_iff
#print axioms Effect4.Json.numbersFinite_obj_iff
#print axioms Effect4.Json.numbersFinite_iff
#print axioms Effect4.Json.not_numbersFinite_nan
#print axioms Effect4.Json.numbersFinite_zero
#print axioms Effect4.Json.numbersFinite_nested
#print axioms Effect4.Json.not_numbersFinite_nested_nan

/-!
Payload carrier, sections D2 through D5: the scalar and record types, the
mutual `Representation`/`Check` tree, its decidable structural equality, the
tag projection, and the constructor caps.
-/

#print axioms Effect4.LiteralValue.kind_surjective
#print axioms Effect4.EnumValue.kind_surjective
#print axioms Effect4.PropertyKey.kind_surjective
#print axioms Effect4.LiteralValue.cases_census
#print axioms Effect4.EnumValue.cases_census
#print axioms Effect4.PropertyKey.cases_census
#print axioms Effect4.EnumValue.toLiteralValue_string
#print axioms Effect4.EnumValue.toLiteralValue_number
#print axioms Effect4.EnumValue.toLiteralValue_injective
#print axioms Effect4.EnumValue.toLiteralValue_kind
#print axioms Effect4.Representation.fieldAdmissible_toLiteralValue_iff
#print axioms Effect4.Representation.fieldAdmissible_toLiteralValue_of_finite
#print axioms Effect4.Representation.tag_surjective
#print axioms Effect4.Check.tag_surjective
#print axioms Effect4.Representation.cases_census
#print axioms Effect4.Check.cases_census
#print axioms Effect4.Representation.absent_ne_empty_annotations

/-!
Payload carrier, general structural elimination: the two-sorted algebra, both
folds, every public constructor equation, and reconstruction.
-/

#print axioms Effect4.Representation.FoldAlgebra
#print axioms Effect4.Representation.fold
#print axioms Effect4.Check.fold
#print axioms Effect4.Representation.FoldAlgebra.rebuild
#print axioms Effect4.Representation.fold_declaration
#print axioms Effect4.Representation.fold_reference
#print axioms Effect4.Representation.fold_suspend
#print axioms Effect4.Representation.fold_null
#print axioms Effect4.Representation.fold_undefined
#print axioms Effect4.Representation.fold_void
#print axioms Effect4.Representation.fold_never
#print axioms Effect4.Representation.fold_unknown
#print axioms Effect4.Representation.fold_any
#print axioms Effect4.Representation.fold_string
#print axioms Effect4.Representation.fold_number
#print axioms Effect4.Representation.fold_boolean
#print axioms Effect4.Representation.fold_bigint
#print axioms Effect4.Representation.fold_symbol
#print axioms Effect4.Representation.fold_literal
#print axioms Effect4.Representation.fold_uniqueSymbol
#print axioms Effect4.Representation.fold_objectKeyword
#print axioms Effect4.Representation.fold_enum
#print axioms Effect4.Representation.fold_templateLiteral
#print axioms Effect4.Representation.fold_arrays
#print axioms Effect4.Representation.fold_objects
#print axioms Effect4.Representation.fold_union
#print axioms Effect4.Check.fold_filter
#print axioms Effect4.Check.fold_filterGroup
#print axioms Effect4.Representation.fold_rebuild
#print axioms Effect4.Check.fold_rebuild

/-!
Typed annotation dimensions, local optics, and recursive data-plane traversals.
-/

#print axioms Effect4.AnnotationKey.decodeEntry_entry
#print axioms Effect4.AnnotationKey.entry_of_decodeEntry
#print axioms Effect4.Annotations.payloadsAt_lawful
#print axioms Effect4.AnnotationKey.values_lawful
#print axioms Effect4.AnnotationKey.inTraversal_lawful
#print axioms Effect4.Representation.nodeAnnotations_lawful
#print axioms Effect4.Check.annotationsLens_lawful
#print axioms Effect4.ElementOf.annotationsLens_lawful
#print axioms Effect4.PropertySignatureOf.annotationsLens_lawful
#print axioms Effect4.Representation.annotationBags_lawful
#print axioms Effect4.Check.annotationBags_lawful
#print axioms Effect4.Document.annotationBags_lawful
#print axioms Effect4.MultiDocument.annotationBags_lawful

/-!
Exact effectful-field annotation admission and generated-program semantics.
-/

#print axioms Effect4.EffectfulFieldSpec.annotationKey_lawful
#print axioms Effect4.EffectfulFieldSpec.check_eq_some_iff
#print axioms Effect4.EffectfulFieldSpec.rawAdmissible_iff_exists_check
#print axioms Effect4.EffectfulField.resolvable_iff_resolve_isSome
#print axioms Effect4.EffectfulField.interpret_set
#print axioms Effect4.EffectfulField.interpret_modify

/-!
Payload carrier, section D6: the two document containers and the single-root
embedding.
-/

#print axioms Effect4.Document.toMulti_mk
#print axioms Effect4.Document.toMulti_injective
#print axioms Effect4.Document.toMulti_two_roots_not_image

/-!
Payload carrier, section D7: annotation-bag admission, the field-admission
predicate and its decision procedure, the compositional per-constructor
specification, and the refusal and acceptance witnesses.
-/

#print axioms Effect4.Annotations.fieldAdmissible_iff
#print axioms Effect4.Annotations.fieldAdmissible_none
#print axioms Effect4.Annotations.fieldAdmissible_some_iff
#print axioms Effect4.Representation.fieldAdmissible_iff
#print axioms Effect4.Check.fieldAdmissible_iff
#print axioms Effect4.Representation.fieldAdmissible_declaration_iff
#print axioms Effect4.Representation.fieldAdmissible_reference_iff
#print axioms Effect4.Representation.fieldAdmissible_suspend_iff
#print axioms Effect4.Representation.fieldAdmissible_null_iff
#print axioms Effect4.Representation.fieldAdmissible_undefined_iff
#print axioms Effect4.Representation.fieldAdmissible_void_iff
#print axioms Effect4.Representation.fieldAdmissible_never_iff
#print axioms Effect4.Representation.fieldAdmissible_unknown_iff
#print axioms Effect4.Representation.fieldAdmissible_any_iff
#print axioms Effect4.Representation.fieldAdmissible_string_iff
#print axioms Effect4.Representation.fieldAdmissible_number_iff
#print axioms Effect4.Representation.fieldAdmissible_boolean_iff
#print axioms Effect4.Representation.fieldAdmissible_bigint_iff
#print axioms Effect4.Representation.fieldAdmissible_symbol_iff
#print axioms Effect4.Representation.fieldAdmissible_literal_string_iff
#print axioms Effect4.Representation.fieldAdmissible_literal_number_iff
#print axioms Effect4.Representation.fieldAdmissible_literal_bigint_iff
#print axioms Effect4.Representation.fieldAdmissible_literal_boolean_iff
#print axioms Effect4.Representation.fieldAdmissible_uniqueSymbol_iff
#print axioms Effect4.Representation.fieldAdmissible_objectKeyword_iff
#print axioms Effect4.Representation.fieldAdmissible_enum_iff
#print axioms Effect4.Representation.fieldAdmissible_templateLiteral_iff
#print axioms Effect4.Representation.fieldAdmissible_arrays_iff
#print axioms Effect4.Representation.fieldAdmissible_objects_iff
#print axioms Effect4.Representation.fieldAdmissible_union_iff
#print axioms Effect4.Check.fieldAdmissible_filter_iff
#print axioms Effect4.Check.fieldAdmissible_filterGroup_iff
#print axioms Effect4.Document.fieldAdmissible_iff
#print axioms Effect4.Document.fieldAdmissible_mk_iff
#print axioms Effect4.MultiDocument.fieldAdmissible_iff
#print axioms Effect4.MultiDocument.fieldAdmissible_mk_iff
#print axioms Effect4.Annotations.not_fieldAdmissible_nonFinite
#print axioms Effect4.Representation.not_fieldAdmissible_nonFiniteAnnotations
#print axioms Effect4.Representation.not_fieldAdmissible_nonFiniteElementAnnotations
#print axioms Effect4.Representation.not_fieldAdmissible_nonFinitePropertyAnnotations
#print axioms Effect4.Check.not_fieldAdmissible_nonFiniteAnnotations
#print axioms Effect4.Representation.not_fieldAdmissible_emptyReferenceKey
#print axioms Effect4.Representation.not_fieldAdmissible_emptyAnnotationId
#print axioms Effect4.Representation.not_fieldAdmissible_nonFiniteAnnotationPayload
#print axioms Effect4.Representation.not_fieldAdmissible_nonFiniteLiteral
#print axioms Effect4.Representation.not_fieldAdmissible_suspendChecks
#print axioms Effect4.Check.not_fieldAdmissible_emptyFilterGroup
#print axioms Effect4.MultiDocument.not_fieldAdmissible_emptyRoots
#print axioms Effect4.Representation.not_fieldAdmissible_throughFilterSchemas
#print axioms Effect4.Representation.fieldAdmissible_nonEmptyReferenceKey
#print axioms Effect4.Representation.fieldAdmissible_finiteLiteral
#print axioms Effect4.Representation.fieldAdmissible_suspendEmptyChecks
#print axioms Effect4.Representation.fieldAdmissible_nonFiniteEnumValue
#print axioms Effect4.Representation.fieldAdmissible_nonFinitePropertyKey
#print axioms Effect4.Representation.fieldAdmissible_aliasedEnum
#print axioms Effect4.Representation.fieldAdmissible_optionalBeforeRequiredElement
#print axioms Effect4.Representation.fieldAdmissible_duplicatePropertyKeys
#print axioms Effect4.Document.fieldAdmissible_danglingReference
#print axioms Effect4.Document.fieldAdmissible_deadReferenceEntry
#print axioms Effect4.Document.fieldAdmissible_emptyTableKey
#print axioms Effect4.MultiDocument.fieldAdmissible_emptyTableKey
#print axioms Effect4.MultiDocument.fieldAdmissible_two_roots
