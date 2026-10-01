import Effect4.Api.HostSession
import Effect4.Program.Profile
import Effect4.Program.Stream
import Effect4.Program.Packages.SqliteBun
import Effect4.Program.Packages.KeyValueStoreMemory
import TestSupport.AcquireHandle

/-!
E4-HOST-CE-007: a host cannot return an internal handle through a declared handle type or
through `unknown`. The original live-session forgery is retained from
`docs/research/2026-09-30-host-answers-evidence/Probe.lean` at `be15b062`: a checked `nat`
program used a host-returned fiber to finish with `"wrong"`. Its table now fails admission.
The `unknown` variant below reaches a real bound call before its reply is refused.

All checks here are finite execution controls, not a general host guarantee. Error values
cannot contain handles in this alphabet; the failure image laws cover that side.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Counterexamples.Machine.Runtime.HostHandleForgery
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession

def fiberRow : Row where
  name := "returnFiber"
  spelling := "Host.returnFiber"
  kind := .async
  registration := .external
  request := .unit
  answer := .fiberOf .nat .never
  error := .never
  cite := "E4-HOST-CE-007"

def fiberTable : RowTable := [fiberRow]
def opts : Supervision.ForkOptions := ⟨true, true, .interruptible⟩

/-- The original forgery: the host claims a number fiber and names the string fiber. -/
def program : Api.Program :=
  .bind (.withFiber (.fork (.succeed (.lit (.str "wrong"))) opts))
    (.bind (.perform (.external 0) (.lit .unit)) (.awaitFiber (.var 1) .joinEffect))

def fiberHeader : Header := ⟨version, "forgery", "forgery-v1", fiberTable⟩

#guard Api.typeOf program fiberTable = some (EffTy.pure .nat)
#guard findInternalHandleInTable fiberTable = some ["table", "0", "answer"]
#guard match admitProgram program fiberTable with
  | .error (.internalHandle ["table", "0", "answer"]) => true
  | _ => false
#guard match start program fiberTable "forgery-v1" fiberHeader 1000 with
  | .error (.program (.internalHandle ["table", "0", "answer"])) => true
  | _ => false

/-- Pin every internal constructor and the reserved spellings at table admission. -/
def internalTypes : List Ty :=
  [.fiberOf .nat .never, .refOf .nat, .deferredOf .nat .never,
   NativeOp.refTy, NativeOp.deferredTy, .scope, .context]
#guard internalTypes.all fun ty =>
  findInternalHandleInTable [{ fiberRow with answer := ty }] = some ["table", "0", "answer"]
#guard internalTypes.all fun ty =>
  findInternalHandleInTable [{ fiberRow with answer := .unit, error := ty }] =
    some ["table", "0", "error"]

/-- Each recursive value shape must expose its nested handle; each path is independent data. -/
def nestedTypes : List (Ty × Path) :=
  [(.option (.refOf .nat), ["inner"]),
   (.list (.refOf .nat), ["inner"]),
   (.causeOf (.refOf .nat), ["error"]),
   (.prod (.refOf .nat) .unit, ["left"]),
   (.prod .unit (.refOf .nat), ["right"]),
   (.union (.refOf .nat) .unit, ["left"]),
   (.union .unit (.refOf .nat), ["right"]),
   (.except (.refOf .nat) .unit, ["error"]),
   (.except .unit (.refOf .nat), ["value"]),
   (.exitOf (.refOf .nat) .never, ["value"]),
   (.exitOf .unit (.refOf .nat), ["error"])]
#guard nestedTypes.all fun (ty, path) =>
  findInternalHandleInTable [{ fiberRow with answer := ty }] =
    some (["table", "0", "answer"] ++ path)
-- Request types are outside this reply rule; a later row's answer is still scanned.
#guard findInternalHandleInTable
  [{ fiberRow with request := .fiberOf .nat .never, answer := .unit }] = none
#guard findInternalHandleInTable
  [{ fiberRow with answer := .unit }, fiberRow] = some ["table", "1", "answer"]

/-- An unknown answer is admitted, so value admission must still reject the live handle. -/
def unknownTable : RowTable := [{ fiberRow with answer := .unknown }]
def unknownProgram : Api.Program :=
  .bind (.withFiber (.fork (.succeed (.lit (.str "wrong"))) opts))
    (.perform (.external 0) (.lit .unit))
def unknownHeader : Header := ⟨version, "unknown", "unknown-v1", unknownTable⟩
def unknownCall : Call := ⟨version, "unknown", unknownTable, 0, Api.root, .external 0, .unit⟩
def forged : Reply :=
  ⟨version, "unknown", 0, ⟨Api.root, 0⟩, .ofExit (.success (Value.fiber 1))⟩
def honest : Reply := { forged with completion := .ofExit (.success (.nat 7)) }

def unknownParked : Option (Session unknownProgram unknownTable) :=
  match start unknownProgram unknownTable "unknown-v1" unknownHeader 1000 with
  | .error _ => none
  | .ok initial => some (advance initial 1000 Api.evaluate).session

def unknownBound : Option (Session unknownProgram unknownTable) :=
  unknownParked.map fun parked => (bindCall parked unknownCall 0).session

#guard (admitProgram unknownProgram unknownTable).toOption.isSome
#guard unknownParked.isSome
#guard unknownParked.any fun parked =>
  (bindCall parked unknownCall 0).phase = .bound
#guard unknownBound.any fun bound =>
  ((bound.machine.fiber? ⟨1⟩).bind (·.exit)) = some (.success (.str "wrong"))
#guard Val.hasTy (Value.fiber 1) .unknown
#guard unknownBound.any fun bound => preflight bound forged = .error .envelope
#guard unknownBound.any fun bound => (submit bound forged).phase = .refused .envelope
#guard unknownBound.any fun bound =>
  let refused := (submit bound forged).session
  refused.machine.state = bound.machine.state ∧
  refused.pending = bound.pending ∧ refused.applied = bound.applied ∧
  refused.consumed = bound.consumed ∧
  requestOf refused.machine Api.root 0 = some (.external 0, .unit)
-- The same live call accepts an ordinary value and finishes with it.
#guard unknownBound.any fun bound => (submit bound honest).phase = .preflight
#guard unknownBound.any fun bound =>
  let finished := (applyReply (submit bound honest).session honest.key 1000).session
  (finished.machine.fiber? Api.root).bind (·.exit) = some (.success (.nat 7)) ∧
    finished.applied = 1

/-- The fifteen real package/profile rows retain their existing reply profile. -/
def inTreeRows : RowTable :=
  Packages.sqliteBun ++ Packages.keyValueStoreMemory ++ Stream.table "Stream.Probe" .nat .never ++
    [Profile.Scalar.waitRow, Profile.Resource.acquireRow, Profile.Resource.useRow,
     Profile.Resource.releaseRow]
#guard inTreeRows.length = 15
#guard findInternalHandleInTable inTreeRows = none

/-- A fresh external allocation still passes the certified session and records the handle. -/
def allocationTable : RowTable := Test.Api.AcquireHandleContract.table
def allocationProgram : Api.Program := .perform (.external 0) (.lit .unit)
def allocationHeader : Header := ⟨version, "allocation", "allocation-v1", allocationTable⟩
def allocationCall : Call :=
  ⟨version, "allocation", allocationTable, 0, Api.root, .external 0, .unit⟩
def allocationReply : Reply :=
  ⟨version, "allocation", 0, ⟨Api.root, 0⟩, .ofExit (.success (.nat 0))⟩

def allocationBound : Option (Session allocationProgram allocationTable) :=
  match start allocationProgram allocationTable "allocation-v1" allocationHeader 1000 with
  | .error _ => none
  | .ok initial =>
    some (bindCall (advance initial 1000 Api.evaluate).session allocationCall 0).session

#guard allocationBound.isSome
#guard allocationBound.any fun bound =>
  bound.machine.state.externals.allocated = [] ∧ (submit bound allocationReply).phase = .preflight
#guard allocationBound.any fun bound =>
  let finished := (applyReply (submit bound allocationReply).session allocationReply.key 1000).session
  finished.machine.state.externals.allocated = [Test.Api.AcquireHandleContract.resource] ∧
    (finished.machine.fiber? Api.root).bind (·.exit) = some (.success (Value.external 0)) ∧
    finished.applied = 1

end Test.Counterexamples.Machine.Runtime.HostHandleForgery
