module

public import Effect4.Program.Authoring.Records

/-!
# Program.Authoring.Ascribe — a term at a declared type

An author sometimes needs a term at a type that is wider than the type the checker gives it.
The first case is an empty cell. The term `nil` has the type `never[]`, and a cell is invariant
(the state plan's T3a, decisions rows 42 and 43). So `Ref.make(nil)` answers `Ref<never[]>`, and
the checker refuses the cell's first append.

The language has one written term type: a record's declared field. `ascribe ty e` is that
record, with one field at `ty` that holds `e`, and a read of the field:

    ascribe ty e  :=  field (record [("v", false, ty)] [("v", e)]) "v"

**It is no cast.** The record's check decides it (`Record.check`,
`src/Effect4/Program/Record.lean`): the checker types the form at `ty` only where the type of `e`
is below `ty`, and it refuses every other use. The form adds no constructor, no atom and no row.
It prints as a record literal and a field read, and it reads back as itself.

**It is not `Ref.make<A>`.** A cell made at an ascribed term has the declared type by this form
alone. The operation-carried type argument of `Ref.make` is a later slice (the faces' part of
decisions rows 42 and 43), and nothing here states it.

The form moved here from `Test/Dogfood/P3WorkerQueue.lean`, where seat T3a measured it, with its
record form unchanged. Its first callers are the scenarios' log cells
(`Test/Dogfood/Scenario/`).

The laws are in the law graph. The scope law is `ascribe_scoped`
(`src/Effect4/Laws/Program/Authoring/Ascribe.lean`). The typing law `types_ascribe` and the
reading law `reads_ascribe` are in `src/Effect4/Laws/Step/Ascribe.lean`. The controls are in
`Test/Program/Ascribe.lean`.
-/

@[expose] public section

namespace Effect4.Program.Authoring

open Effect4.Program

/-- The declaration of an ascription's record: one required field, `v`, at the declared type. -/
def ascribeFields (ty : Ty) : List (String × Bool × Ty) := [("v", false, ty)]

/-- **`e` at the declared type `ty`**: a record with one field declared at `ty` that holds `e`,
and a read of that field. The record's check decides the form: the type of `e` is below `ty`,
or the checker refuses. -/
def ascribe (ty : Ty) (e : TermSrc) : TermSrc :=
  field (record (ascribeFields ty) [("v", e)]) "v"

end Effect4.Program.Authoring
