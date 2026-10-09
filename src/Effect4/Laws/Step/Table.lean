import Effect4.Library.Table

/-!
# The encoding table's fact (decisions rows 255 and 265)

The table itself (`Table`, `Table.Injective`, `Table.renew`) is data that a model reads, so it
stands in the core (`src/Effect4/Library/Table.lean`, decisions row 332). This file holds its one
fact: on an injective table the identity test on two handles decides the two identities
(`Table.Injective.decides`).

A module's own function of the table stays in the module's folder: the Queue's tables after a
take and after an offer are in `src/Effect4/Laws/Library/Queue/Relation.lean`.

Placement. Concept `translation-simulation`, requirement R10. These are the vocabulary of a
module's step statements, with one fact. Their consumers are the relations and the step
statements of the Queue (`src/Effect4/Laws/Library/Queue/`) and of Semaphore
(`src/Effect4/Laws/Library/Semaphore/`), and the removal pass's reading rule. The table says
nothing of a wrapper: which fiber holds which handle belongs to the wrapper's relation.
-/

set_option autoImplicit false

namespace Effect4.Modules

open Effect4 Effect4.Machine

/-- On an injective table the identity test on two handles decides the two identities. -/
theorem Table.Injective.decides {tb : Table} (injective : tb.Injective) (a b : Nat) :
    decide (tb.handle a = tb.handle b) = decide (a = b) :=
  decide_eq_decide.mpr ⟨injective a b, fun same => congrArg tb.handle same⟩

end Effect4.Modules
