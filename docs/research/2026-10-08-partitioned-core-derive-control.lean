module

public import Effect4.Library.PartitionedSemaphore.Model
public import Effect4.Schema.Modeled
public import Effect4.Schema.FieldRef
meta import Effect4.Schema.Modeled.Derive
meta import Effect4.Schema.FieldRef.Elab

/-! Retained reduction control: this module omits Cell's local string definition import.
The command refuses the generated field-order proof before writing the instance. -/

@[expose] public section
namespace Effect4.PartitionedSemaphore
open Effect4.Schema Effect4.Program

/--
error: Tactic `decide` failed for proposition
  Field.Ascending Field.bytesKey
    [("available", false, Modeled.ty Nat), ("capacity", false, Modeled.ty Nat), ("waiting", false, Modeled.ty Nat)]
because its `Decidable` instance
  instDecidableAscendingBytesKey
    [("available", false, Modeled.ty Nat), ("capacity", false, Modeled.ty Nat), ("waiting", false, Modeled.ty Nat)]
did not reduce to `isTrue` or `isFalse`.

After unfolding the instances `instDecidableEqBool`, `Bool.decEq`, `List.decidableBAll`, `List.instDecidablePairwise`, `instDecidableAscendingBytesKey`, and `instDecidableAscendingBytesKey._aux_1`, reduction got stuck at the `Decidable` instance
  match
    Field.ltKey (Field.bytesKey ("capacity", false, Modeled.ty Nat).fst)
      (Field.bytesKey ("waiting", false, Modeled.ty Nat).fst),
    true with
  | false, false => isTrue ⋯
  | false, true => isFalse ⋯
  | true, false => isFalse ⋯
  | true, true => isTrue ⋯
-/
#guard_msgs (error) in
derive_modeled Model.Counts

end Effect4.PartitionedSemaphore
