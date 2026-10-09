import Effect4.Modules.Step
import Effect4.Modules.Semaphore.Cell

set_option autoImplicit false
open Effect4.Program Effect4.Schema Effect4.Schema.Model Effect4.Modules

namespace Overwatch02.Positions

abbrev originalFields := Ty.canon Effect4.Semaphore.cellFields
abbrev insertedFields := ("available", false, Ty.nat) :: originalFields

-- The same positional author expression compiles for both canonical schemas.
def originalTaken : FieldRef originalFields .nat :=
  .there _ _ _ (.there _ _ _ (.here _ _ _))
def driftedTaken : FieldRef insertedFields .nat :=
  .there _ _ _ (.there _ _ _ (.here _ _ _))

#guard originalTaken.name == "taken"
#guard driftedTaken.name == "permits"
#guard originalTaken.index == driftedTaken.index

def originalRead : Step [.record originalFields] .nat :=
  .get (.var (.here _ _)) originalTaken
def driftedRead : Step [.record insertedFields] .nat :=
  .get (.var (.here _ _)) driftedTaken

-- Both are well-typed data. The changed field is an author-intent error.
#guard originalRead.canonical && originalRead.normal
#guard driftedRead.canonical && driftedRead.normal

-- Concrete states retain the same original fields and insert only the new one.
def beforeValues : Inputs Leaves.opaque [.record originalFields] :=
  (((0 : Nat), ((10 : Nat), ((3 : Nat), ([], ())))), ())
def afterValues : Inputs Leaves.opaque [.record insertedFields] :=
  (((99 : Nat), ((0 : Nat), ((10 : Nat), ((3 : Nat), ([], ()))))), ())

#guard Nat.beq (originalRead.eval Leaves.opaque beforeValues) 3
#guard Nat.beq (driftedRead.eval Leaves.opaque afterValues) 10

-- Positive control: selecting taken at its new position retains the intended value.
def correctedTaken : FieldRef insertedFields .nat :=
  .there _ _ _ (.there _ _ _ (.there _ _ _ (.here _ _ _)))
def correctedRead : Step [.record insertedFields] .nat :=
  .get (.var (.here _ _)) correctedTaken
#guard correctedTaken.name == "taken"
#guard correctedRead.normal
#guard Nat.beq (correctedRead.eval Leaves.opaque afterValues) 3

-- Proposal only: `field_ref% "taken"` elaborates against expected `FieldRef fs .nat`,
-- finds that required field by name, and emits existing here/there constructors.
-- The insertion changes its generated path, and does not change its selected name.
-- Missing, duplicate, optional, wrong-type, or unreducible schemas refuse explicitly.

end Overwatch02.Positions
