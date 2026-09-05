import Effect4.Codegen.Rule
import Effect4.Evidence.StdLib.Derived

/-!
# Surface.Views: the surface store

Implements `docs/research/2026-09-04-surface-library-plan.md` §2's `Views.lean` row: every
surface as a named `Document` plus the store they are addressed and named in. The shape is
`Effect4/Evidence/Views.lean`'s, and for the same reason: a view is a `Document`, a `Document`
is store content at kind `schema` (`Store/Genesis.lean:34`), and a name is a binding in a
`tree` node.

Wave 1a registers the two views that exist: the entity and the domain. Waves 2a-2c append
`"surface/api"`, `"surface/mcp"`, `"surface/deploy"` and `"surface/site"` to `views`, and
nothing else changes.

| | |
| --- | --- |
| Carrier | none of its own: `Document`, `Tree` and `Store` are already owned |
| Operations | `views`, `viewTree`, `viewStore` |
| Laws | `views_nodup_names`, `views_names` |
| Structure | a finite name-indexed family, folded into the one heterogeneous store |
| Payoff | a surface view is content like any other value: one address, one admission, one trait |
| Anti-vacuity | `views_names`, which fails if a name is misspelled or a view is dropped |
| Generation | none |

## Why there is no theorem about `viewStore`

A document's address is `sha256` of its node bytes, and its node's spec is the address of the
schema node of `(shape Document).document` — the meta-schema, ninety-two kilobytes of value
tree (the facts note §6a). A `decide` or a `#guard` about `viewStore`'s nodes would therefore
hash that in the kernel, and no such receipt is claimed here; `Effect4/Evidence/Views.lean`
builds its own store the same way and claims nothing about it either, and lane B measures what
a battery can afford. The receipts that do hold are about `views`, which is a plain list of
names and documents, and about the documents themselves, which `Effect4/Surface/Entity.lean`
gives `Arch.accepts` receipts for.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Store

/-- Every surface view, named. Later waves append; nothing is inserted, so a recorded name keeps
its position. The name is what the tree binds: the store keeps no paths since the trie retired
(the facts note's Q3). -/
def views : List (String × Document) :=
  [ ("surface/entity", entityDoc)
  , ("surface/domain", domainDoc) ]

/-- The names the views are registered under. -/
def viewNames : List String := views.map Prod.fst

/-- The name space of the surface views: each name bound to its document's schema node. -/
def viewTree : Tree :=
  ⟨views.map fun entry => (entry.1, ⟨.schema, (address entry.2).digest⟩)⟩

/-- The root the surface family is reached by. -/
def viewRootName : String := "surface/views"

/-- The view documents in a store of their own: the genesis, the tree's own document, each view
as a schema node under the genesis, the tree, and the root. Stated, not guarded. -/
def viewStore : Store :=
  let withGenesis := putOr Store.empty metaSchema
  let withTreeDoc := putOr withGenesis (Canonical.document Tree)
  let withViews := views.foldl (fun s entry => putOr s entry.2) withTreeDoc
  let withTree := putOr withViews viewTree
  putRootOr withTree ⟨viewRootName, .schema, .tree, (address viewTree).digest, 1⟩

/-- The views are named distinctly, so no binding of the tree overwrites another. -/
theorem views_nodup_names : viewNames.Nodup := by decide

/-- The registered names, exactly. This is the receipt a later wave's append has to keep true of
its own prefix. -/
theorem views_names : viewNames = ["surface/entity", "surface/domain"] := rfl

/-! ## Anti-vacuity -/

#guard views.length == 2
#guard viewNames == ["surface/entity", "surface/domain"]
#guard (views.find? fun entry => entry.1 == "surface/entity").isSome
#guard (views.find? fun entry => entry.1 == "surface/api").isNone
#guard viewRootName == "surface/views"

/-! ## Receipts -/

#print axioms views
#print axioms viewNames
#print axioms viewTree
#print axioms viewStore
#print axioms views_nodup_names
#print axioms views_names

end Effect4.Surface
