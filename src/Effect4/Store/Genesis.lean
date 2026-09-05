import Effect4.Store.Node
import Effect4.Store.Store
import Effect4.Store.Traits
import Effect4.Store.Derived.Schema

/-!
# Store.Genesis

Owner: the one instance that closes the loop — `Content Document` at kind `schema` — and the
theorems it turns from statements under a binder into facts.

`Store/Node.lean` writes everything that needs `Canonical Document` — the meta-schema, the
genesis node, `specOf`, `nodeOf`, `address` and the lattice — under `variable [Content
Document]`, and `Store/Derived/Schema.lean` derives `Canonical Document` from the carrier
itself. This module supplies the kind, and with it every statement of that section is an
ordinary theorem: the meta-schema is the genesis node (`nodeOf_metaSchema'`), the spec of
`Document` is the genesis address (`specOf_document`), every other document's node is a schema
node under the genesis (`nodeOf_document'`), and the meta-schema fits its own shape
(`metaSchema_fits`, the genesis theorem of the facts note's Q6, which is the class law `fits`
at the meta-schema and so needs no `decide`).

The numbers this fixes under version byte 0 are the facts note's §6a: the genesis address
`2794d9…2926` (`specOf Document`), the census entry's spec `268ee1…aa7c` and its address
`1c3c94…72eb`. They are guarded by the battery (`Test/Store/NodeContract.lean`), not here: a
library module prints nothing. The guard is cheap — `#guard` evaluates the compiled decision
procedure, not the kernel, so the SHA-256 of the ninety-two-kilobyte meta-schema decides in
about two seconds (lane B's measurement, 2026-09-05).
-/

set_option autoImplicit false

namespace Effect4.Store

/-- The schema kind's carrier: every spec is a stored `Document`. -/
instance instContentDocument : Content Document where
  kind := .schema

/-- The kind the genesis rule assumes, by construction. -/
theorem kind_document : Content.kind Document = .schema := rfl

/-- The meta-schema's node is the genesis node: zero spec, kind `schema`. -/
theorem nodeOf_metaSchema' : nodeOf metaSchema = genesisNode := nodeOf_metaSchema rfl

/-- Every document's node is its schema node: the genesis for the meta-schema, a node whose
spec is the genesis address for every other document. -/
theorem nodeOf_document' (d : Document) : nodeOf d = schemaNode d := nodeOf_document rfl d

/-- The meta-schema fits its own shape: the genesis theorem, closed. -/
theorem metaSchema_fits : (shape Document).accepts (toVal metaSchema) = true := metaSchema_accepts

/-! ## Receipts -/

#print axioms instContentDocument
#print axioms kind_document
#print axioms nodeOf_metaSchema'
#print axioms nodeOf_document'
#print axioms metaSchema_fits
#print axioms specOf_document
#print axioms address_eq_or_collision
#print axioms address_inj

end Effect4.Store
