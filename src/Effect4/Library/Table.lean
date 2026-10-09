module
public import Effect4.Machine.Wake

/-!
# The encoding table of a composed module's relation (decisions rows 255 and 265)

A composed module's model names a request by a number. Its cell names a request by a `Deferred`
handle, and a signal by a hint. So the connector of a cell to a model is a relation, and it
reads a table. This file holds the table. It names no module.

- **The encoding table** (`Table`) gives each model identity its identity handle and its
  current hint.
- **`Table.Injective`** says that no two identities share a handle.
- **A step changes the table in one way, and frames the rest** (`Table.renew`): it sets the
  hint of the step's own request. Every other entry stays.

The table is data that a model reads (the Latch's, `src/Effect4/Library/Latch/Model.lean`), so it
stands in the core (decisions row 332). Its one fact, that an injective table's identity test
decides the identities, stands in the proof graph (`src/Effect4/Laws/Step/Table.lean`).
-/

set_option autoImplicit false

@[expose] public section

namespace Effect4.Modules

open Effect4 Effect4.Machine

/-- **The encoding table**: each model identity's `Deferred` handle, and its current hint. -/
structure Table where
  handle : Nat → DeferredKey
  hint : Nat → DeferredKey

/-- No two identities share a handle, so the identity test on two handles decides the equality
of the two identities. -/
def Table.Injective (tb : Table) : Prop := ∀ a b : Nat, tb.handle a = tb.handle b → a = b

/-- The table with the hint of the request `id` set. Every handle stays, and so does the hint of
every other request. A step enrols a fresh request so, and replaces the hint of a request that
waits already. -/
def Table.renew (tb : Table) (id : Nat) (hint : DeferredKey) : Table :=
  { tb with hint := fun n => if n = id then hint else tb.hint n }

end Effect4.Modules
