import GenFix.Record.Fold
import Effect4.Program.FoldOf

/-!
# GenFix.Record.FoldOfScan — `fold_of` on a nested family with a field-list position (a fixture)

The record fixture's five traversals through `fold_of` (`src/Effect4/Program/FoldOf.lean`):
`members` (a paramorphism: its record arm uses the field list as a value), `isNever` and
`isMember` (the record arm listed), and `renderRaw`/`closed`, whose record arms recurse through a
sibling over the field list `List (String × Ty)` (`renderFields`, `closedFields`).

Before seat W2's commit 2 every one of the five was refused (probe Q,
`Q/logs/probes/Q3-FoldOfScan.log`, reproduced here at the base: `W2/logs/gen/foldof-scan-base.log`):
the first three because `mapThrough` had no product case (`Prod.map` takes two functions and
`mkAppM` left a metavariable), the last two because a sibling over `List (A × M)` was not read.
With the product case (probe Q's `FoldOf-prod.patch`) and the field-list sibling (seat W2) all
five are accepted, and so is `fieldTys`, a paramorphism through the field list; each connector is
a kernel-checked theorem whose axioms are printed below.
-/

namespace GenFix.Record
fold_of GenFix.Record.Ty.members
fold_of GenFix.Record.Ty.isNever
fold_of GenFix.Record.Ty.isMember
fold_of GenFix.Record.Ty.renderRaw
fold_of GenFix.Record.Ty.closed
-- a paramorphism through the field list: the sibling keeps the field's type as a value
fold_of GenFix.Record.Ty.fieldTys

-- the connectors, evaluated: the fold of each algebra is the hand traversal on a record sample
#guard cata_ty Ty.renderRaw.alg (.record [("a", .lit "x"), ("b", .option .nat)]) =
  Ty.renderRaw (.record [("a", .lit "x"), ("b", .option .nat)])
#guard (cata_ty Ty.fieldTys.alg (.record [("a", .record [("b", .nat)]), ("c", .string)])).2 =
  [.record [("b", .nat)], .nat, .string]
#guard cata_ty Ty.closed.alg (.record [("a", .var 0)]) = false
end GenFix.Record

#print axioms GenFix.Record.Ty.members.eq_cata
#print axioms GenFix.Record.Ty.renderRaw.eq_cata
#print axioms GenFix.Record.Ty.renderFields.eq_foldr
#print axioms GenFix.Record.Ty.renderFields.eq_cata
#print axioms GenFix.Record.Ty.closedFields.eq_cata
#print axioms GenFix.Record.Ty.fieldTys.eq_cata
#print axioms GenFix.Record.Ty.fieldTysOf.eq_foldr
#print axioms GenFix.Record.Ty.fieldTysOf.eq_cata
