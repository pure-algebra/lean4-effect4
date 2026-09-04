import Effect4.Codegen.Layer

/-!
Fresh kernel dependency report for the layer printer (`Effect4/Codegen/Layer.lean`; plan
`docs/research/2026-09-04-provision-algebra.md` §9, R9). The printer's receipts are the
`#guard`s in the module itself, on `TypeScript.Expr`/`ConstDecl` syntax; this file is the
axiom receipt. The three `String`-building definitions (`unionType`, `rowType`, `layerType`)
concatenate only and are expected at the ceiling like everything else.
-/

#print axioms Effect4.Program.Provision.KeyNames
#print axioms Effect4.Program.Provision.KeyNames.spell?
#print axioms Effect4.Program.Provision.LayerPrintRefusal
#print axioms Effect4.Program.Provision.mergeOperands
#print axioms Effect4.Program.Provision.callArgs
#print axioms Effect4.Program.Provision.printLayer
#print axioms Effect4.Program.Provision.printApp
#print axioms Effect4.Program.Provision.unionType
#print axioms Effect4.Program.Provision.rowType
#print axioms Effect4.Program.Provision.layerType
#print axioms Effect4.Program.Provision.printLayerDecl
#print axioms Effect4.Program.Provision.printAppDecl
