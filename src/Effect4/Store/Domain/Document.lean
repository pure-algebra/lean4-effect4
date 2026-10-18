module

public import Effect4.Store.Domain.Node
public import Effect4.Store.Domain.Derived.Schema

/-!
# Store.Document

Owner: the one `Content Document` instance, at kind `schema`.

`src/Effect4/Store/Domain/Node.lean` states the genesis, `specOf`, `nodeOf` and `address` under
`variable [Content Document]`. This module supplies the instance below the store, so node
admission can compute a fixed specification: the result envelope's
(`src/Effect4/Store/Domain/Action.lean`). `src/Effect4/Store/Domain/Genesis.lean` keeps the theorems that
the instance closes. There is one instance and one encoding.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (Document)

/-- The schema kind's carrier: every spec is a stored `Document`. -/
instance instContentDocument : Content Document where
  kind := .schema

end Effect4.Store
