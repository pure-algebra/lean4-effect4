import Test.Dogfood.Scenario.Programs
import Effect4.Laws.Program.HeapSites

/-!
# Control: a crew member's release writes its environment's slot

Concept: scope-lifetime-finalization, R11. A control for `Workers.Assertions.logs_step` and
`QueueWorkers.Assertions.logs_history`: it shows why their log clause needs a value premise.
The Atomic cleanup writer reads each note's literal identity from the source
(`Atomic.WriterSource.bounded_census`). In both crews each member's acquisition note writes its
literal `nat i`, but its release note writes the bound acquired value: run at its level with every
bound slot holding `nat 7`, it appends `nat 7`. So a log writer ledger must read the acquired value
and the `released` cell from the environment. A finite evaluation of two built programs; it
establishes no machine property.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.ReleaseWrites

open Effect4 Effect4.Program
open Effect4.Store (Val)

/-- The update term of a `Ref.updateWith` perform site. -/
def updateTerm : NativeOp → Option Term
  | .refUpdateWith f => some f
  | _ => none

/-- Each update site under an acquisition, by its path below the acquisition, with what it
appends to an empty list when every bound slot holds `nat 7`. -/
def writes (program : NativeEff) (acquisition : List Nat) : List (List Nat × Option Val) :=
  (HeapSites.performSites program).filterMap fun site =>
    if acquisition.isPrefixOf site.1 then
      (updateTerm site.2.1).map fun f =>
        (site.1.drop acquisition.length, site.2.2.2.bind fun level =>
          evalTerm (List.replicate level (Val.nat 7) ++ [Val.list []]) f)
    else none

/-- The acquisition note appends the member's literal; the release note appends the slot. -/
def readsSlot (member : Nat) (sites : List (List Nat × Option Val)) : Bool :=
  sites == [([0, 0], some (Val.list [Val.nat member])), ([1], some (Val.list [Val.nat 7]))]

#guard readsSlot 1 (writes (Programs.workersProgram 2) (Programs.crewAcquire 1))
#guard readsSlot 2 (writes (Programs.workersProgram 2) (Programs.crewAcquire 2))
#guard readsSlot 1 (writes (Programs.queueProgram 2) (Programs.queueAcquire 1))
#guard readsSlot 2 (writes (Programs.queueProgram 2) (Programs.queueAcquire 2))
#guard readsSlot 3 (writes (Programs.queueProgram 2) (Programs.queueAcquire 3))

end Test.Dogfood.Scenario.ReleaseWrites
