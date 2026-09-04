import Effect4.Surface.Emit
import Effect4.Store.Store

/-!
# Surface.Views: the surface store

Implements `docs/research/2026-09-04-surface-library-plan.md` §2's `Views.lean`
row: every surface as a `(Path × Document)` pair plus the store they are
addressed and named in. The shape is `Effect4/Arch/Views.lean`'s, and for the
same reason: a view is a `Document`, a `Document` is store content
(`Canonical Document`, `Effect4/Arch/JsonCanonical.lean`), and a path is how it
is named.

Wave 1a registers the two views that exist: the entity and the domain. Waves
2a-2c append `["surface", "api"]`, `["surface", "mcp"]`, `["surface", "deploy"]`
and `["surface", "site"]` to `views`, and nothing else changes.

| | |
| --- | --- |
| Carrier | none of its own: `Document`, `Path` and `Store` are already owned |
| Operations | `views`, `viewStore` |
| Laws | `views_nodup_paths`, `views_paths` |
| Structure | a finite path-indexed family, folded into the generic content store |
| Payoff | a surface view is addressable content like any other value, so the same digest, the same trie and the same `Canonical` instance carry it |
| Anti-vacuity | `views_paths`, which fails if a path is misspelled or a view is dropped |
| Generation | none |

## Why there is no theorem about `viewStore`

`Canonical Document` addresses a document through its *persisted* JSON form,
which is produced by `Effect4/Target/TypeScript/Schema.lean`'s `representation`.
That function is well-founded recursive on `sizeOf`, so it does not reduce in
the kernel, and neither does the SHA-256 over its output. A `decide` or a
`#guard` about `viewStore`'s entries would therefore get stuck rather than
answer, and no such receipt is claimed here. `Effect4/Arch/Views.lean` builds
its own store the same way and claims nothing about it either. The receipts
that do hold are about `views`, which is a plain list of paths and documents,
and about the documents themselves, which `Effect4/Surface/Entity.lean` gives
`Arch.accepts` receipts for.
-/

set_option autoImplicit false

namespace Effect4.Surface

open Effect4 Effect4.Store

/-- Every surface view, named. Later waves append; nothing is inserted, so a
recorded path keeps its position. -/
def views : List (Path × Document) :=
  [ (["surface", "entity"], entityDoc)
  , (["surface", "domain"], domainDoc) ]

/-- The paths the views are registered at. -/
def viewPaths : List Path := views.map Prod.fst

/-- The view documents in a store of their own: addressed by their canonical
bytes and named by their paths. -/
def viewStore : Store Document :=
  views.foldl (fun store entry => (store.putAt entry.1 entry.2).2) Store.empty

/-- The views are named at distinct paths, so no fold step overwrites another. -/
theorem views_nodup_paths : viewPaths.Nodup := by decide

/-- The registered paths, exactly. This is the receipt a later wave's append
has to keep true of its own prefix. -/
theorem views_paths : viewPaths = [["surface", "entity"], ["surface", "domain"]] := by
  rfl

/-! ## Anti-vacuity -/

#guard views.length == 2
#guard viewPaths == [["surface", "entity"], ["surface", "domain"]]
#guard (views.find? fun entry => entry.1 == ["surface", "entity"]).isSome
#guard (views.find? fun entry => entry.1 == ["surface", "api"]).isNone

end Effect4.Surface
