import Effect4.Program.Compile

/-!
# Row admission for the host-call fragment

This module owns the row admission used by `StraightRows` and its proofs.
It admits registered data replies. A handle reply remains outside this fragment.
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- A host row that this fragment calls: the position names a row that the runner registers
(`externalRow`), and its answer column is no handle type, so a reply allocates nothing
(`externalValue`, `Program/Compile.lean`). -/
def dataRow (table : RowTable) (i : Nat) : Bool :=
  match externalRow table i with
  | some row => match row.answer with
    | .handle _ => false
    | _ => true
  | none => false

end Effect4.Program.Denote
