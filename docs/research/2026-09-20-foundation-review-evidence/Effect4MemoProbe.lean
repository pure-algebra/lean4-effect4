import Effect4.Machine.Stores

/-! Narrow finite counterexamples for the proposed memo identity-write removal.
These are arbitrary public Stores values, not claims of reachability from loadR.
The parent review runs this scratch file; no production file is changed. -/

namespace ReviewProbe.Memo

open Effect4 Effect4.Machine

def collisionBefore : Stores :=
  { Stores.empty with memo := [⟨⟨0⟩, none, []⟩], nextName := 0 }

def collisionAfter : Stores :=
  { collisionBefore with
    memo := collisionBefore.memo ++ [⟨⟨0⟩, none, []⟩]
    nextName := 1 }

theorem ids_unique_before : (collisionBefore.memo.map MemoMap.id).Nodup := by
  decide

theorem fork_collision_step :
    syncOpStep (.memoFork none) collisionBefore =
      some (collisionAfter, Val.memoMap ⟨0⟩) := rfl

theorem ids_not_unique_after : ¬ (collisionAfter.memo.map MemoMap.id).Nodup := by
  decide

def entry : MemoEntry := ⟨1, 0, ⟨0⟩, .memoEntry [] ⟨0⟩⟩

def duplicateWorld : MemoWorld :=
  [⟨⟨0⟩, none, [([], entry)]⟩, ⟨⟨0⟩, some ⟨1⟩, []⟩]

theorem identity_write_changes_duplicate_world :
    duplicateWorld.updateEntry ⟨0⟩ [] id ≠ duplicateWorld := by
  decide

theorem identity_write_copies_first_map :
    duplicateWorld.updateEntry ⟨0⟩ [] id =
      [⟨⟨0⟩, none, [([], entry)]⟩, ⟨⟨0⟩, none, [([], entry)]⟩] := rfl

-- A bound alone is also insufficient: both duplicate IDs lie below 2.
theorem duplicate_ids_below_supply :
    ∀ m ∈ duplicateWorld, m.id.index < 2 := by
  decide

def duplicateBefore : Stores := { Stores.empty with memo := duplicateWorld }

-- This is exactly the proposed memoComplete branch after deleting its memo write.
def proposedAfter : Stores :=
  { duplicateBefore with
    deferreds :=
      (duplicateBefore.deferreds.complete entry.deferred
        (Completion.ofExit (.success Val.unit))).1 }

theorem actual_complete_differs_from_deleted_write :
    syncOpStep (.memoComplete [] ⟨0⟩ (.success Val.unit)) duplicateBefore ≠
      some (proposedAfter, Val.unit) := by
  decide

#print axioms ids_unique_before
#print axioms fork_collision_step
#print axioms ids_not_unique_after
#print axioms identity_write_changes_duplicate_world
#print axioms identity_write_copies_first_map
#print axioms duplicate_ids_below_supply
#print axioms actual_complete_differs_from_deleted_write

end ReviewProbe.Memo
