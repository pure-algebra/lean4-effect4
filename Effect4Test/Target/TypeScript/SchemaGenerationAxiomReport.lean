import Effect4.Schema.Authoring
import Effect4.Target.TypeScript.Schema
import Effect4Test.Target.TypeScript.SchemaGenerationCoverage

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
#print axioms Effect4Test.Target.TypeScript.SchemaGenerationCoverage.allRepresentations_tags

#print axioms Effect4.Target.TypeScript.Schema.json
#print axioms Effect4.Target.TypeScript.Schema.representation
#print axioms Effect4.Target.TypeScript.Schema.check
#print axioms Effect4.Target.TypeScript.Schema.documentExpr
#print axioms Effect4.Target.TypeScript.Schema.multiDocumentExpr
#print axioms Effect4.Target.TypeScript.Schema.jsonSource
#print axioms Effect4.Target.TypeScript.Schema.representationSource
#print axioms Effect4.Target.TypeScript.Schema.documentSource
#print axioms Effect4.Target.TypeScript.Schema.multiDocumentSource
#print axioms Effect4.Target.TypeScript.Schema.targetIdentifier
#print axioms Effect4.Target.TypeScript.Schema.documentReady
#print axioms Effect4.Target.TypeScript.Schema.generationReady
#print axioms Effect4.Target.TypeScript.Schema.generationReady_iff
#print axioms Effect4.Target.TypeScript.Schema.moduleSyntax
#print axioms Effect4.Target.TypeScript.Schema.module?
#print axioms Effect4.Target.TypeScript.Render.escapeString
#print axioms Effect4.Target.TypeScript.Render.quoted
#print axioms Effect4.Target.TypeScript.Render.float64Bits
#print axioms Effect4.Target.TypeScript.Render.expr
#print axioms Effect4.Target.TypeScript.Render.module
#print axioms Effect4.Target.TypeScript.Schema.source?
#print axioms Effect4.Target.TypeScript.Schema.generate?
