import Effect4.Laws.Program.ReleaseCustody.Lift
import Effect4.Laws.Program.ReleaseCustody.ScopeRows
import Effect4.Laws.Program.ReleaseCustody.OuterFrames
import Effect4.Laws.Program.ReleaseCustody.NativeAccounting
import Effect4.Laws.Program.ReleaseCustody.NativeScopeDebit
import Effect4.Laws.Program.ReleaseCustody.CommandFunding
import Effect4.Laws.Program.ReleaseCustody.NativeStacks
import Effect4.Laws.Program.ReleaseCustody.IterationDebit
import Effect4.Laws.Program.ReleaseCustody.ReplySequencing
import Effect4.Laws.Program.ReleaseCustody.AdministrativeKept
import Effect4.Laws.Program.ReleaseCustody.AdministrativeQueue
import Effect4.Laws.Program.ReleaseCustody.NativeMachineShape
import Effect4.Laws.Program.ReleaseCustody.CommandSequencing
import Effect4.Laws.Program.ReleaseCustody.NativeIterationDebit

/-!
Concept: scope-lifetime-finalization, R11, at most once per registration counted by source identity.
Question: the native command obligation consumed by `Workers.Assertions.releases_step`.
Reach: native programs, row tables, command budgets and admitted decision histories.
The assertion and checked outside-loop lift live in `ReleaseCustody.Lift`.
The admitted-history obligation remains planned. These assemblies prove no progress or source uniqueness.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.Execution
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control

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

/-- Custody on sequential direct-source admitted histories is the remaining R11 obligation.
Consumer: `Workers.Assertions.releases_step`; the source identities and original application scope are unchanged.
The unrestricted internal command contract is refuted by `CustodyCommandControl.lean`.
Its repair must retain actual command ownership, saved-frame positions and resume-token correlation.
This planned endpoint assumes neither an arbitrary command contract nor the desired release bound. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal history (b : Api.Built) (fuel : Nat) (q : List Nat) (m : NativeMachine)
    (fragment : SourceScope.Fragment b.program) (sequential : SourceScope.SequentialSource b.program)
    (raceFree : SourceScope.RaceFreeSource b.program)
    (held : Run.HistoryOf b fuel m) : Ready q m

end Effect4.Program.ReleaseCustody.Execution
