module

public import Effect4.Library.Stream.ArrayOps
public import Effect4.Program.Authoring.Module

/-! Array sources as stored definitions, constructed through the shared module authoring API.
The runtime arguments carry array contents and the opened cell.
A source record holds invocation builders at author time; stored bodies contain only Eff data. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Stream
open Effect4.Program Effect4.Program.Authoring

/-- The cell holding one array source's pending elements. -/
def arrayHandleTy (A : Ty) : Ty := .refOf (.list A)

/-- Declare an array source's operations once per element type and instance name. -/
eff_module ArrayDefinitions (A : Ty) where
  openArray (items : .list A) : (arrayHandleTy A) := arrayOpen A items;
  pull (receiver : arrayHandleTy A) : (Program.Stream.pulledTy A .unit) := arrayPull A receiver;
  close (receiver : arrayHandleTy A) : .unit := arrayClose receiver

end Effect4.Stream
