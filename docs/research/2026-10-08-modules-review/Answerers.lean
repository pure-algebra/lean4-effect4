import Effect4
import Effect4.Program.Authoring.Defs
open Effect4 Effect4.Program Effect4.Program.Authoring
namespace ModulesAnswererReview
-- Equal spelling and columns do not connect an external row to a stored body.
def operation := Def.of "sameOperation" [] .nat (succeed (nat 7) : Src NativeOp)
def row := Row.host "sameOperation" .unit .nat

def callExternal : Module NativeOp :=
  { rows := [row], defs := [operation.src], main := Row.call row unit }
def callDefinition : Module NativeOp :=
  { rows := [row], defs := [operation.src], main := operation.call }

#eval (Api.Author.build callExternal).isOk
#eval (Api.Author.build callDefinition).isOk
#eval ((Api.Author.build callExternal).toOption.map fun b =>
  (Api.run b.program 500 [] b.table).exit.isNone)
#eval ((Api.Author.build callDefinition).toOption.map fun b =>
  (Api.run b.program 500 [] b.table).exit == some (.success (.nat 7)))
#eval ((Api.Author.build callExternal).toOption.bind fun external =>
  (Api.Author.build callDefinition).toOption.map fun stored =>
    external.program == stored.program)

-- Turning an external table row into a store registration is not an admitted substitution.
def storeTableRow : RowDef := { row with row := { row.row with registration := .deferred } }
#eval (Api.Author.build { rows := [storeTableRow], main := Row.call storeTableRow unit }).isOk

-- Opaque typing does not require a value's uses to belong to its module's operations.
def latchTy : Ty := .handle "Latch.Latch"
def maker := Row.host "Latch.make" .bool latchTy
def inspectRow := Row.host "Unrelated.inspect" latchTy .nat
#eval (Api.Author.build { rows := [maker], main := eff do
  let latch ← Row.call maker (bool false)
  return latch }).isOk
#eval (Api.Author.build { rows := [maker, inspectRow], main := eff do
  let latch ← Row.call maker (bool false)
  Row.call inspectRow latch }).isOk
-- An opaque external handle cannot serve as the implementation's Ref receiver today.
def opaqueBody := Def.of "opaqueBody" [("q", latchTy)] .unit
  (fun (q : TermSrc) => andThen (Ref.get q) (succeed unit) : TermSrc → Src NativeOp)
#eval (Api.Author.build { defs := [opaqueBody.src], main := succeed unit }).isOk
end ModulesAnswererReview
