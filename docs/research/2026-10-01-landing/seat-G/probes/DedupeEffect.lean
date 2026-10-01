import Effect4

/-!
Seat G probe (step 5, row 8 item ii): what deduplicating `ShapeDoc.document`'s references by key
would change, computed without touching the tree. `dedupedDocument` is the candidate repair
(keep the first binding of each key; every repeated key in the tree has equal bodies, measured by
`RepeatedDefs.lean`). The meta-schema `(shape Document).document` repeats keys, so the genesis
node's bytes and address would move, and with them the spec of every schema node and the address
of every node (`Store/Domain/Node.lean`: `genesisAddress`, `schemaNode`, `specOf`, `nodeOf`).
-/

open Effect4 Effect4.Store

namespace SeatG.DedupeEffect

/-- The candidate: references deduplicated by key, first binding kept, table order otherwise. -/
def dedupedDocument (doc : ShapeDoc) : Document :=
  { representation := render doc.root
    references := (doc.defs.map (·.1)).eraseDups.filterMap fun k =>
      (doc.defs.find? (·.1 == k)).map fun d => ⟨d.1, renderDef d.1 d.2⟩ }

def dedupedMeta : Document := dedupedDocument (shape Document)
def dedupedGenesis : Node := ⟨0, .schema, zeroDigest, toVal dedupedMeta⟩
def dedupedGenesisAddress : Digest := sha256 dedupedGenesis.encode

-- the meta-schema: references and bytes, now and deduplicated
#eval (metaSchema.references.length, dedupedMeta.references.length)
#eval ((Val.encode (toVal metaSchema)).length, (Val.encode (toVal dedupedMeta)).length)
-- the genesis address, now (pinned at `Test/Store/NodeContract.lean:142-143`) and deduplicated
#eval genesisAddress.hex
#eval dedupedGenesisAddress.hex
-- every other schema node's spec is `genesisAddress` (`schemaNode`), so it moves with it: the
-- census entry's spec and address, pinned at `Test/Store/NodeContract.lean:150-158`, are two

end SeatG.DedupeEffect
