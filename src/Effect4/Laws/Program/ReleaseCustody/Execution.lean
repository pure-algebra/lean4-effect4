import Effect4.Laws.Program.ReleaseCustody.Control
import Effect4.Laws.Machine.ForkLedgerInvariant
import Effect4.Laws.Run.Frame
import ProofGraph.Registry

/-!
Concept: scope-lifetime-finalization, R11, at most once per registration counted by source identity.
Question: command and decision obligations consumed by `Workers.Assertions.releases_step`.
Reach: the actual native evaluator, scope allocation, native pending continuations, task snapshots and admitted decisions.
Limit: the command and outside-loop obligations remain planned; the assemblies prove no progress or host behavior.
Unlock: existing Machine.Lift transports the concrete custody assertion to whole admitted histories.
No execution carrier is added; each predicate reads existing machine fields.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.Execution
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control

/-- Existing scope rows have unique keys below the actual allocation supply.
Consumer: `command_custody`, including scope creation and keyed scope credit transfer. -/
def ScopeRows (m : NativeMachine) : Prop :=
  (m.state.scopes.entries.map ScopeEntry.key).Nodup ∧
    (∀ entry ∈ m.state.scopes.entries, entry.key < m.state.nextName) ∧ m.state.ScopeKeysFresh

/-- Native countdowns resume with exits, void, or the saved exit's restore continuation.
Consumer: `command_custody`, at the actual countdown observer transfer. -/
def PendingShape (m : NativeMachine) : Prop :=
  ∀ fiber ∈ m.fibers, ∀ pending ∈ fiber.pending,
    pending.resumeWith = .exitsValue ∨ pending.resumeWith = .void ∨
      ∃ exit, pending.resumeWith = .continueWith (.restore exit)

/-- Drained tasks carry no foreign cleanup credit in their answer code.
Consumer: the existing Lift task-snapshot premise in `outer_custody`. -/
def TasksZero (q : List Nat) (tasks : List (Task EffName EffThunk Val Err Defect FiberId Ann)) : Prop :=
  ∀ task ∈ tasks, taskCredits q task = 0

/-- The dispatcher stores the same zero-credit native resumes before a task snapshot is drained.
Consumer: `outer_custody`, at the actual dispatcher drain. -/
def DispatcherZero (q : List Nat) (m : NativeMachine) : Prop :=
  ∀ fiber ∈ m.fibers, ∀ bucket ∈ fiber.dispatcher.buckets, TasksZero q bucket.tasks

/-- Concrete custody and the allocation and continuation shapes needed by every command.
Consumer: the existing Lift decision theorem and `Workers.Assertions.releases_step`. -/
structure Ready (q : List Nat) (m : NativeMachine) : Prop where
  fibers : ForkLedger.Invariant.Ok m
  scopes : ScopeRows m
  pending : PendingShape m
  dispatcher : DispatcherZero q m
  funded : Funded q m []

/-- The exact command interface already carried by Machine.Lift, with its actual drained snapshot.
Consumer: `outer_custody`. -/
def CommandContract (root : NativeEff) (table : RowTable) (q : List Nat) : Prop :=
  letI := evaluatorFor root table
  ∀ tasks, Lift.StepKeeps Lift.unitOrder (interpOf root table)
    (Lift.Guarded (fun _ m => Ready q m) (fun _ m commands => Funded q m commands)
      (fun _ _ => TasksZero q) tasks)

/-- Every native command keeps the concrete custody and native continuation shapes.
The full case census is retained in MachineCommandCensus.md.
Consumer: `decision`, then `Workers.Assertions.releases_step`.
The obligation includes remaining evaluator, scope allocation, fork, observer and dispatcher cases. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal command_custody : ∀ root table q, CommandContract root table q

/-- The actual edits outside the command loop provide the existing decision-lift fields.
Consumer: `decision`, then the admitted-history custody assembly.
The command premise is explicit; no reachability predicate assumes a release bound. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal outer_custody : ∀ (root : NativeEff) (table : RowTable) (q : List Nat),
  letI := evaluatorFor root table
  CommandContract root table q →
  Lift.DecisionLift Lift.unitOrder (interpOf root table)
    (fun _ m => Ready q m) (fun _ m commands => Funded q m commands)
    (fun _ _ => TasksZero q)
    (fun _ m decision => Run.Accepted table (Api.HostSession.callTable root table) m decision)

/-- Whole decisions consume the actual command and outside-loop contracts.
Consumer: `history`, then `Workers.Assertions.releases_step`.
This assembly remains modulo the two explicitly placed custody obligations. -/
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
