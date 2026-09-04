import Effect4.Schema.Authoring
import Effect4.Codegen.Schema
import Test.Codegen.SchemaGenerationCoverage

/-!
Kernel dependency receipt for the Schema authoring laws and recursive
Schema-to-TypeScript generation boundary.
-/

#print axioms Effect4.Schema.Predicate.decide_iff
#print axioms Effect4.Schema.Predicate.and_eq_true
#print axioms Effect4.Schema.Predicate.or_eq_true
#print axioms Effect4.Schema.Predicate.not_eq_true
#print axioms Effect4.Schema.Predicate.contramap_id
#print axioms Effect4.Schema.Predicate.contramap_comp
#print axioms Effect4.Schema.Predicate.all_eq_true
#print axioms Effect4.Schema.Predicate.any_eq_true
#print axioms Effect4.Schema.Predicate.each_eq_true
#print axioms Effect4.Schema.withCheck_reference
#print axioms Effect4.Schema.withCheck_suspend
#print axioms Effect4.Schema.withCheck_string
#print axioms Test.Codegen.SchemaGenerationCoverage.allRepresentations_tags

#print axioms Effect4.Codegen.Schema.json
#print axioms Effect4.Codegen.Schema.reifyJson?
#print axioms Effect4.Codegen.Schema.reifyJson?_json
#print axioms Effect4.Codegen.Schema.json_injective
#print axioms Effect4.Codegen.Schema.representation
#print axioms Effect4.Codegen.Schema.check
#print axioms Effect4.Codegen.Schema.documentExpr
#print axioms Effect4.Codegen.Schema.multiDocumentExpr
#print axioms Effect4.Codegen.Schema.jsonSource
#print axioms Effect4.Codegen.Schema.representationSource
#print axioms Effect4.Codegen.Schema.documentSource
#print axioms Effect4.Codegen.Schema.multiDocumentSource
#print axioms Effect4.Codegen.Schema.targetIdentifier
#print axioms Effect4.Codegen.Schema.documentReady
#print axioms Effect4.Codegen.Schema.generationReady
#print axioms Effect4.Codegen.Schema.generationReady_iff
#print axioms Effect4.Codegen.Schema.moduleSyntax
#print axioms Effect4.Codegen.Schema.module?
#print axioms TypeScript.Render.escapeString
#print axioms TypeScript.Render.quoted
#print axioms TypeScript.Render.float64Bits
#print axioms TypeScript.Render.expr
#print axioms TypeScript.Render.module
#print axioms Effect4.Codegen.Schema.source?
#print axioms Effect4.Codegen.Schema.generate?
