import Effect4.Laws.Machine.Refinement

/-! Phase B candidate only: unbuilt statement skeleton, no proof admission. -/

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
#proof_wanted inserting_poke_fails_absent

def scopes_fail_dense : ProofGraph.Obligation (
    ¬ ((sparseScopes.entryAt 0).isSome = true ↔ 0 < sparseScopes.entries.length)) := ⟨⟩
#proof_wanted scopes_fail_dense

end Obligations
end ArenaRed
end Effect4.Machine

#typed_state_obligations Effect4.Machine.ArenaRed.Obligations ceiling 2 using aesop (rule_sets := [Effect4.Stores])
