import Effect4.Machine.Wake

/-!
# The encoding table of a composed module's relation (decisions rows 255 and 265)

A composed module's model names a request by a number. Its cell names a request by a `Deferred`
handle, and a signal by a hint. So the connector of a cell to a model is a relation, and it
reads a table. This file holds the table. It names no module.

- **The encoding table** (`Table`) gives each model identity its identity handle and its
  current hint.
- **`Table.Injective`** says that no two identities share a handle. On an injective table the
  identity test on two handles decides the two identities (`Table.Injective.decides`).
- **A step changes the table in one way, and frames the rest** (`Table.renew`): it sets the
  hint of the step's own request. Every other entry stays.

A module's own function of the table stays in the module's folder: the Queue's tables after a
take and after an offer are in `src/Effect4/Laws/Modules/Queue/Relation.lean`.

Placement. Concept `translation-simulation`, requirement R10. These are the vocabulary of a
module's step statements, with one fact. Their consumers are the relations and the step
statements of the Queue (`src/Effect4/Laws/Modules/Queue/`) and of Semaphore
(`src/Effect4/Laws/Modules/Semaphore/`), and the removal pass's reading rule. The table says
nothing of a wrapper: which fiber holds which handle belongs to the wrapper's relation.
-/

set_option autoImplicit false

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

/-- On an injective table the identity test on two handles decides the two identities. -/
theorem Table.Injective.decides {tb : Table} (injective : tb.Injective) (a b : Nat) :
    decide (tb.handle a = tb.handle b) = decide (a = b) :=
  decide_eq_decide.mpr ⟨injective a b, fun same => congrArg tb.handle same⟩

end Effect4.Modules
