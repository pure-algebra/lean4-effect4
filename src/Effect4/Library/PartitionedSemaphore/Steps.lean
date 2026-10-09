module

public import Effect4.Library.PartitionedSemaphore.Data
meta import Effect4.Step.Elab.Inputs

/-! Source builders for the four scalar bookkeeping operations.
Each builder translates existing Step data using named inputs.
No builder allocates a cell, waits, releases permits, or executes a host effect. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.PartitionedSemaphore
open Effect4.Program Effect4.Program.Authoring Effect4.Modules

def initialStep (capacity : TermSrc) := Data.initial.term (input_sources% (Data.InitialInputs) {capacity := capacity})
def availableStep (cell : TermSrc) := Data.available.term (input_sources% (Data.CellInputs) {cell := cell})
def tryTakeStep (requested cell : TermSrc) := Data.tryTake.term
  (input_sources% (Data.RequestInputs) {cell := cell, requested := requested})
def reserveStep (requested cell : TermSrc) := Data.reserve.term
  (input_sources% (Data.RequestInputs) {requested := requested, cell := cell})

end Effect4.PartitionedSemaphore
