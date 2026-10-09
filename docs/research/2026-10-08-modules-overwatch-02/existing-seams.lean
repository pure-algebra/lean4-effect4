import Effect4.Laws.Modules.Step
import Effect4.Modules.Semaphore.Steps
import Effect4.Schema.Modeled.Derive
open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Modules
set_option autoImplicit false
namespace Overwatch02
-- Existing schema owner; no second handwritten copy of its type fields.
abbrev semFields := Ty.canon Effect4.Semaphore.cellFields
#guard Ty.record semFields == Effect4.Semaphore.cellTy
-- Positions remain manual even when metadata comes from its owner.
def takenF : FieldRef semFields .nat := .there _ _ _ (.there _ _ _ (.here _ _ _))
#guard takenF.name == "taken"
-- Source lists have no arity check, and an absent input becomes a unit term.
def unitInput : Input [.unit] .unit := .here _ _
def identityUnit : Step [.unit] .unit := .var unitInput
#guard identityUnit.term (fun x => Input.source [] x) { names := [] } [] ==
  unit { names := [] } []
end Overwatch02
