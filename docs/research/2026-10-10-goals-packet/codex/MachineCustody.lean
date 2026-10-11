import Effect4.Laws.Program.ReleaseCustody
import ProofGraph.AxiomAudit

open Effect4 Effect4.Machine Effect4.Program

namespace MachineCustody

/-- Reader at the real foreign-release alphabet: a fresh scope owns the credit it receives. -/
theorem fresh_entry (q : List Nat) (c : Capture) :
    ReleaseCustody.scopeCredits q
      ((Scope.makeDefault : ScopeV).addUnsafe 0 (.foreign c)) =
        ReleaseCustody.credit q (.foreign c) := by
  have h := ReleaseCustody.add_open q (Scope.makeDefault : ScopeV) 0 (.foreign c)
    rfl (by intro h; exact List.not_mem_nil h)
  rw [show ReleaseCustody.scopeCredits q (Scope.makeDefault : ScopeV) = 0 from rfl, Nat.zero_add] at h
  exact h

/-- Reader at the native response boundary: unit is store custody, closing exit is residual custody. -/
example (root : NativeEff) (q : List Nat) (a : Val) (c : Capture) (exit : ExitV) :
    ReleaseCustody.afterAddCredits q (.foreign c) Val.unit = 0 ∧
    ReleaseCustody.afterAddCredits q (.foreign c) (reifyExitVal exit) =
      ReleaseCustody.credit q (.foreign c) :=
  ⟨(ReleaseCustody.after_add_unit root q a (.foreign c)).1,
   (ReleaseCustody.after_add_exit root q a (.foreign c) exit).1⟩

#axiom_audit Effect4.Laws.Program.ReleaseCustody
end MachineCustody
