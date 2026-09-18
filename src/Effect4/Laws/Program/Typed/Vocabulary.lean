/-!
# Typed/Vocabulary — what a position's typing source can be

The vocabulary of the typed-state source table (`docs/research/2026-09-18-position-census-design.md`
§2B). Rows are declared with `typed_position` (`Laws/Auto/TypedSources.lean`) and read from its
environment extension by the totality gate and the skeleton emitter. This module holds only the
data types, with no meta import, so that anything may name them.

The world is the tables plus the store: the fiber table `Γ` (every fiber ever forked, at the
type it was forked at), the promise table `Π` (every deferred cell, at the type it was made
at: the row's types for `deferredMake`, the layer's type for `memoBuild`), and the heap column
(`HeapNat` at this cut). Handles carry no type in `Val.hasTy` (DI-17, decisions row 44), so
every handle is typed by the world.
-/

namespace Effect4.Program.Typed

/-- Where a position's expected type comes from. Terms are spelled over the owner value `x`
(and, for a nested owner, its `inherited` expectation). -/
inductive Expected
  /-- The fiber table at this id. -/
  | fiber (id : String)
  /-- The promise table at this cell. -/
  | promise (cell : String)
  /-- The heap column. -/
  | refColumn
  /-- The signature row's answer and error columns. -/
  | row (op : String)
  /-- The checker at this point of the root program. -/
  | checker (point : String)
  /-- The expectation the enclosing owner passes down (`RSaved` inside `RunFiber`). -/
  | inherited
  /-- A fixed type. -/
  | const (ty : String)
deriving Repr, BEq, Inhabited

/-- What the invariant states at a position, or on a containment edge. -/
inductive Source
  /-- `TypedProg w e p`. -/
  | program (e : Expected)
  /-- `∀ w' ≥ w, ∀ ex, ExitOk e ex → TypedProg w' e' (next ex)`. -/
  | continuation (e : Expected)
  /-- `Val.hasTy ∧ validIn`. -/
  | value (e : Expected)
  /-- `ExitOk`. -/
  | exit (e : Expected)
  /-- `causeAdmits`. -/
  | cause (e : Expected)
  /-- An interpreter hook: typed at what its consumer installs it as; `none` when the reference
  never calls it (the read census checks). -/
  | hook (consumer : Option String)
  /-- A store column carried as its own clause (`HeapNat`, the promise table). -/
  | column (name : String)
  /-- Written, never read back as an answer (the read census checks). -/
  | journal
  /-- A hand predicate over a whole field: on a position, over the position's own type; on an
  edge, over the field's whole type (the stack, the pending list, the races, the context). -/
  | custom (pred : String)
  /-- Named debt: must be cited by a decisions or DI row. -/
  | refused (reason : String)
  /-- On a containment edge: the child's `Ok` at this expectation instead of the parent's. -/
  | nested (e : Expected)
deriving Repr, BEq, Inhabited

/-- One row: the position's key as the census prints it, `Owner.field`, and its source. -/
abbrev Row := String × Source

end Effect4.Program.Typed
