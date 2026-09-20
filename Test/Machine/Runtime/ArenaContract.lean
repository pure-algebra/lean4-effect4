import Effect4.Laws.Machine.Refinement

/-! The two red controls of the arena packet, decided: a store that inserts on an absent write
fails `poke_absent`, and a sparse keyed table fails `dense`. -/

set_option autoImplicit false
namespace Effect4.Machine

namespace ArenaRed

/-- Rejected candidate: absent writes insert at the end. -/
def insertOnAbsent (xs : List Nat) (i value : Nat) : List Nat :=
  if i < xs.length then xs.set i value else xs ++ [value]

/-- Key 2 is present, while key 0 is absent despite the one-entry extent. -/
def sparseScopes : ScopeStore := ⟨[⟨2, Effect4.Scope.make .sequential⟩]⟩

namespace Obligations

def inserting_poke_fails_absent : ProofGraph.Obligation (
    ([] : List Nat).length ≤ 0 ∧ insertOnAbsent [] 0 7 ≠ []) := ⟨⟩

def scopes_fail_dense : ProofGraph.Obligation (
    ¬ ((sparseScopes.entryAt 0).isSome = true ↔ 0 < sparseScopes.entries.length)) := ⟨⟩

end Obligations

/-- The inserting write is refused by `poke_absent`: it changes an empty store at an absent key. -/
theorem inserting_poke_fails_absent : ([] : List Nat).length ≤ 0 ∧ insertOnAbsent [] 0 7 ≠ [] := by
  decide

/-- A sparse keyed table is not dense: a present key above an absent one. -/
theorem scopes_fail_dense :
    ¬ ((sparseScopes.entryAt 0).isSome = true ↔ 0 < sparseScopes.entries.length) := by
  decide

end ArenaRed
end Effect4.Machine

#typed_state_obligations Effect4.Machine.ArenaRed.Obligations ceiling 0 using decide
