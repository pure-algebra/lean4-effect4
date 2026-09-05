import Cas.Node
import Cas.Store
import Cas.Traits
import Cas.Derived.Schema

/-!
# Cas.Genesis

Owner: the spike's exit — the one instance that closes the loop, and the numbers it fixes.

Lane S2 wrote everything that needs `Canonical Document` under `variable [Content Document]`
(`Cas/Node.lean`, the `Genesis` section); lane G derived `Canonical Document`
(`Cas/Derived/Schema.lean`). This module supplies `Content Document` at kind `schema`, and
with it every statement of that section is an ordinary theorem: the meta-schema is the
genesis node (`nodeOf_metaSchema`), the spec of `Document` is the genesis address
(`specOf_document`), and the meta-schema fits its own shape (`metaSchema_accepts`). The
`#eval`s print the addresses the facts note's §6 could only stand in for: the genesis
address, the real spec of the census entry's document, and the entry's real node address.
They are printed, not guarded, because a kernel `decide` over a SHA-256 of tens of kilobytes
is not a receipt worth its cost; the byte-level guards live in `Cas/Probe.lean`.
-/

set_option autoImplicit false

namespace Effect4.Store

/-- The schema kind's carrier: every spec is a stored `Document`. -/
instance instContentDocument : Content Document where
  kind := .schema

/-- The census entry of the templates is `export` content. -/
instance instContentTemplatesEntry : Content Templates.Entry where
  kind := .«export»

/-- The kind the genesis rule assumes, by construction. -/
theorem kind_document : Content.kind Document = .schema := rfl

/-- The meta-schema's node is the genesis node: zero spec, kind `schema`. -/
theorem nodeOf_metaSchema' : nodeOf metaSchema = genesisNode := nodeOf_metaSchema rfl

/-- Every document's node is its schema node: the genesis for the meta-schema, a node whose
spec is the genesis address for every other document. -/
theorem nodeOf_document' (d : Document) : nodeOf d = schemaNode d := nodeOf_document rfl d

/-- The meta-schema fits its own shape: the genesis theorem, closed. -/
theorem metaSchema_fits : (shape Document).accepts (toVal metaSchema) = true := metaSchema_accepts

/-! ## The numbers -/

#eval s!"metaSchema.payload.bytes  {(Val.encode (toVal metaSchema)).length}"
#eval s!"genesis.address           {genesisAddress.hex}"
#eval s!"specOf.Document           {(specOf Document).hex}"
#eval s!"entryDoc.payload.bytes    {(Val.encode (toVal (Canonical.document Templates.Entry))).length}"
#eval s!"specOf.Entry              {(specOf Templates.Entry).hex}"
#eval s!"entry.node.bytes          {(nodeOf Templates.entry).encode.length}"
#eval s!"entry.address             {(address Templates.entry).digest.hex}"
#eval s!"specFor.metaSchema.isZero {decide (specFor metaSchema = zeroDigest)}"

/-! ## Receipts -/

#print axioms instContentDocument
#print axioms instContentTemplatesEntry
#print axioms nodeOf_metaSchema'
#print axioms nodeOf_document'
#print axioms metaSchema_fits
#print axioms specOf_document
#print axioms address_eq_or_collision
#print axioms address_inj

end Effect4.Store
