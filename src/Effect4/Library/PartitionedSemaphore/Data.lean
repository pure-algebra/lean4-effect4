module

public import Effect4.Library.PartitionedSemaphore.Cell
public import Effect4.Step.Inputs
meta import Effect4.Step.Elab
meta import Effect4.Step.Elab.Inputs

/-! Four scalar bookkeeping steps over the existing Step signature.
The independent model owns the arithmetic.
Reservation is branch arithmetic and performs no registration or waiting. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.PartitionedSemaphore
open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Modules

namespace Data
step_context% InitialInputs (capacity : .nat)
step_context% CellInputs (cell : countsTy)
step_context% RequestInputs (requested : .nat, cell : countsTy)

/-- Supply construction fields by name against the generated schema. -/
def initial : Step InitialInputs.types countsTy := step_inputs% InitialInputs =>
  record_step% { waiting := .nat 0, capacity := capacity, available := capacity }

def available : Step CellInputs.types .nat := step_inputs% CellInputs => .get cell availableF

def tryTake : Step RequestInputs.types (.prod .bool countsTy) := step_inputs% RequestInputs =>
  .ite (.isZero requested) (.pair (.bool true) cell)
    (.ite (.or (.lt (.get cell capacityF) requested) (.lt (.get cell availableF) requested))
      (.pair (.bool false) cell)
      (.pair (.bool true) (.set cell availableF (.sub (.get cell availableF) requested))))

def reserve : Step RequestInputs.types (.prod .nat countsTy) := step_inputs% RequestInputs =>
  let needed := Step.sub requested (.get cell availableF)
  .pair needed (.set (.set cell availableF (.nat 0)) waitingF (.add (.get cell waitingF) needed))
end Data

end Effect4.PartitionedSemaphore
