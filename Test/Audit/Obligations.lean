import Effect4.Laws.Auto.Obligations
open ProofGraph

namespace Test.Obligations.Positive
theorem closed : Obligation (∀ n : Nat, n = n) := ⟨⟩
theorem pending : Obligation (∀ n : Nat, n = n + 1) := ⟨⟩
#proof_wanted pending
end Test.Obligations.Positive

/-- info: Test.Obligations.Positive: 1 open, 1 proved, 2 total; ceiling 1 -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Positive ceiling 1 using aesop

/-- error: proof graph: 1 open obligations exceed ceiling 0 -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Positive ceiling 0 using aesop

namespace Test.Obligations.Missing
theorem pending : Obligation (∀ n : Nat, n = n + 1) := ⟨⟩
end Test.Obligations.Missing
/-- error: obligation ledger: missing proof or placeholder for [Test.Obligations.Missing.pending] -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Missing ceiling 1 using aesop

namespace Test.Obligations.Stale
def extra : ProofWanted True := ⟨⟩
theorem closed : Obligation True := ⟨⟩
end Test.Obligations.Stale
/-- error: obligation ledger: stale placeholder Test.Obligations.Stale.extra -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Stale ceiling 1 using aesop

namespace Test.Obligations.Solved
theorem closed : Obligation (∀ n : Nat, n = n) := ⟨⟩
#proof_wanted closed
end Test.Obligations.Solved
/-- error: obligation ledger: proved goals still have a placeholder: [Test.Obligations.Solved.closed] -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Solved ceiling 1 using aesop

namespace Test.Obligations.Parameterized
theorem closed : Obligation True := ⟨⟩
def leftover (n : Nat) : ProofWanted (n = n) := ⟨⟩
end Test.Obligations.Parameterized
/-- error: obligation ledger: stale placeholder Test.Obligations.Parameterized.leftover -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Parameterized ceiling 0 using aesop

#print axioms Test.Obligations.Positive.closed.checked

namespace Test.Obligations.Reference
theorem direct : Obligation (∀ n : Nat, n = n) := ⟨⟩
#obligation_proved direct := fun n => Eq.refl n
end Test.Obligations.Reference

/-- info: Test.Obligations.Reference: 0 open, 1 proved, 1 total; ceiling 0 -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Reference ceiling 0 using fail

/-- info: Test.Obligations.Reference: 0 open, 1 proved, 1 total; ceiling 0 -/
#guard_msgs in
#typed_state_obligations Test.Obligations.Reference ceiling 0 using fail

namespace Test.Obligations.ReferenceStale
theorem direct : Obligation True := ⟨⟩
#proof_wanted direct
#obligation_proved direct := True.intro
end Test.Obligations.ReferenceStale

/-- error: obligation ledger: proved goals still have a placeholder: [Test.Obligations.ReferenceStale.direct] -/
#guard_msgs in
#typed_state_obligations Test.Obligations.ReferenceStale ceiling 0 using fail

namespace Test.Obligations.WrongReference
theorem wrong : Obligation False := ⟨⟩
/-- error: Type mismatch
  True.intro
has type
  True
but is expected to have type
  False -/
#guard_msgs in
#obligation_proved wrong := True.intro
end Test.Obligations.WrongReference

namespace Test.Obligations.Included
section
variable {n : Nat} (h : n = n)
include h
set_option linter.unusedSectionVars false in
theorem statement : Obligation True := ⟨⟩
set_option linter.unusedSectionVars false in
theorem law : True := True.intro
end
open Lean Meta Elab Command
run_cmd liftTermElabM do
  let binders ← forallTelescope (← getConstInfo ``statement).type fun xs _ => pure xs.size
  unless binders == 2 do throwError "included hypothesis was lost"
#obligation_proved statement := @law
end Test.Obligations.Included

#print axioms Test.Obligations.Reference.direct.checked
#print axioms Test.Obligations.Included.statement.checked

namespace Test.Obligations.Audit
theorem target {n : Nat} (h : n = n) : n = n := h
namespace Wanted
theorem target {n : Nat} (_h : n = n) : Obligation (n = n) := ⟨⟩
end Wanted
end Test.Obligations.Audit

/-- info: Test.Obligations.Audit.Wanted.target: 2/2 binders; law Test.Obligations.Audit.target; exact true; adapter false
---
info: Test.Obligations.Audit.Wanted: 1 paired, 0 without a namesake, 0 mismatches -/
#guard_msgs in
#obligation_audit Test.Obligations.Audit.Wanted

namespace Test.Obligations.BadAudit
theorem target {n : Nat} (h : n = n) : n = n := h
namespace Wanted
theorem target {n : Nat} : Obligation (n = n) := ⟨⟩
end Wanted
end Test.Obligations.BadAudit

/-- error: obligation audit: statement mismatch for [Test.Obligations.BadAudit.Wanted.target] -/
#guard_msgs (error) in
#obligation_audit Test.Obligations.BadAudit.Wanted

namespace Test.Obligations.ForeignAxioms
theorem target : Obligation (∀ p : Prop, p ∨ ¬p) := ⟨⟩
/-- error: proof graph: Test.Obligations.ForeignAxioms.target.checked reaches disallowed axioms [Classical.choice] -/
#guard_msgs in
#obligation_proved target := Classical.em
end Test.Obligations.ForeignAxioms

namespace Test.Obligations.ChangedReference
theorem target : Obligation (∀ n : Nat, n = n) := ⟨⟩
theorem target.checked : True := True.intro
end Test.Obligations.ChangedReference
/-- error: Test.Obligations.ChangedReference.target.checked: proposition changed -/
#guard_msgs in
#typed_state_obligations Test.Obligations.ChangedReference ceiling 0 using aesop

namespace Test.Obligations.LegacyDefinition
set_option linter.defProp false in
def target : Obligation True := ⟨⟩
end Test.Obligations.LegacyDefinition
/-- error: obligation ledger: Test.Obligations.LegacyDefinition.target must be declared as a theorem -/
#guard_msgs in
#typed_state_obligations Test.Obligations.LegacyDefinition ceiling 0 using aesop
