import Effect4.Laws.Program.ReleaseCustody.Lift
import Effect4.Laws.Program.ReleaseCustody.Pop

/-!
Concept: scope-lifetime-finalization, R11, at most once per registration counted by source identity.
Question: the native command obligation consumed by `Workers.Assertions.releases_step`.
Reach: native programs, row tables, command budgets and admitted decision histories.
The assertion and checked outside-loop lift live in `ReleaseCustody.Lift`.
The command obligation remains planned. These assemblies prove no progress or source uniqueness.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.Execution
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control

/-- Every native command keeps the concrete custody and native continuation shapes.
The full case census is retained in MachineCommandCensus.md.
Consumer: `decision`, then `Workers.Assertions.releases_step`.
The obligation includes remaining evaluator, scope allocation, fork, observer and dispatcher cases. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal command_custody : ∀ root table q, CommandContract root table q

/-- Whole decisions consume the actual command and outside-loop contracts.
Consumer: `history`, then `Workers.Assertions.releases_step`.
This assembly remains modulo the explicitly placed command obligation. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem decision (b : Api.Built) (q : List Nat) (m : NativeMachine) (x : Nat × NativeDecision)
    (held : Ready q m)
    (accepted : Run.Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2) :
    Ready q (Run.stepBy b m x) := by
  letI := evaluatorFor b.program b.table
  have lift := outer_custody b.program b.table q (command_custody b.program b.table q)
  obtain ⟨_, _, kept⟩ := Lift.stepDecisionState_lift lift x.1 () m x.2 held accepted
  exact kept

/-- Actual load has empty scopes, pending continuations and dispatcher buckets.
Consumer: `history`; initial custody uses the universal checked compile projection. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem load (root : NativeEff) (fuel : Nat) (q : List Nat) : Ready q (Api.load root fuel) := by
  refine ⟨?_, ?_, ?_, ?_, load_funded q root fuel⟩
  · refine ⟨?_, List.nodup_nil, ?_, ?_, ?_⟩
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · intro id member
      change id ∈ [⟨0⟩] at member
      have same := List.mem_singleton.mp member
      subst id
      exact Nat.zero_lt_one
    · intro id member
      change id ∈ ([] : List FiberId) at member
      cases member
    · intro id member
      change id ∈ ([] : List FiberId) at member
      cases member
  · refine ⟨List.nodup_nil, ?_, Stores.scopeKeysFresh_empty⟩
    intro entry member
    change entry ∈ ([] : List ScopeEntry) at member
    cases member
  · intro fiber member pending present
    change fiber ∈ [RunFiber.make ⟨0⟩ (Api.compile root fuel) true (2048, false) emptyCtx] at member
    have same := List.mem_singleton.mp member
    subst fiber
    cases present
  · intro fiber member bucket present
    change fiber ∈ [RunFiber.make ⟨0⟩ (Api.compile root fuel) true (2048, false) emptyCtx] at member
    have same := List.mem_singleton.mp member
    subst fiber
    cases present

/-- Every admitted history consumes the existing Machine.Lift and Run.HistoryOf interfaces.
Consumer: `Workers.Assertions.releases_step`; the release bound reads only actual source identities. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem history (b : Api.Built) (fuel : Nat) (q : List Nat) (m : NativeMachine)
    (held : Run.HistoryOf b fuel m) : Ready q m :=
  Run.history_keeps b fuel (Ready q) (load b.program fuel q) (decision b q) m held

end Effect4.Program.ReleaseCustody.Execution
