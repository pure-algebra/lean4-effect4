module

import all Init.Data.String.Defs

public import Effect4.Library.PartitionedSemaphore.Model
public import Effect4.Schema.Modeled
public import Effect4.Schema.FieldRef
meta import Effect4.Schema.Modeled.Derive
meta import Effect4.Schema.FieldRef.Elab

/-! The scalar record's derived type and named fields.
This record is not the full identity-bearing module state.
The derived image, membership, codec admission, and handle validity remain separate claims. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.PartitionedSemaphore
open Effect4.Schema Effect4.Program

derive_modeled Model.Counts

/-- The generated scalar type. -/
abbrev countsTy := Model.Counts.modeledTy
/-- Read the signature from deriving, without restating the field order. -/
abbrev countsFields := match countsTy with | .record fs => fs | _ => []

def capacityF : FieldRef countsFields .nat := field_ref% "capacity"
def availableF : FieldRef countsFields .nat := field_ref% "available"
def waitingF : FieldRef countsFields .nat := field_ref% "waiting"

end Effect4.PartitionedSemaphore
