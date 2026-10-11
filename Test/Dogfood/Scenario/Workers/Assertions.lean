import Test.Dogfood.Scenario.Programs
import Test.Dogfood.Scenario.Frame
import Effect4.Laws.Program.ReleaseCustody.Control
import Effect4.Laws.Program.Guard.Decision

/-!
# Workers cleanup assertions at every command boundary

Concept: scope-lifetime-finalization, R11, at most once per registration counted by identity.
Question: each helper serves `Workers.releases_once`, consumed by the workers claim.
Reach: the actual built crew, all totals, budgets and session-admitted decision histories.
Each counted trace event names the acquisition source path, rather than a fiber number.
These assertions retain unfinished commands, yields and interruption through `HistoryOf`.
They establish neither progress nor release order, and leave the host boundary unchanged.
Unlock: the R11 whole-run observation follows from three named preservation obligations.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.Workers.Assertions

open Effect4 Effect4.Machine Effect4.Program

/-- The universally certified acquisition paths, shared with the source placement facts. -/
abbrev acquirePath := Programs.crewAcquire

abbrev registeredAt := ReleaseTrace.registeredAt
abbrev releaseAt := ReleaseTrace.releaseAt

/-- The release observation reads the second allocated reference cell. -/
def log (m : NativeMachine) : List Val :=
  match (m.state.refs[1]? : Option Val) with
  | some (.list values) => values
  | _ => []

/-- Each source acquisition registers at most once. -/
def Registrations (m : NativeMachine) : Prop :=
  ∀ i ∈ [1, 2], m.trace.countP (registeredAt (acquirePath i)) ≤ 1

/-- A release start spends a registration at that same source acquisition. -/
def ReleaseDebits (m : NativeMachine) : Prop :=
  ∀ i ∈ [1, 2], m.trace.countP (releaseAt (acquirePath i)) ≤
    m.trace.countP (registeredAt (acquirePath i))

/-- Each recorded identity spends one release start at its own acquisition source. -/
def LogDebits (m : NativeMachine) : Prop :=
  (∀ v ∈ log m, v = .nat 1 ∨ v = .nat 2) ∧
    ∀ i ∈ [1, 2], (log m).count (.nat i) ≤ m.trace.countP (releaseAt (acquirePath i))

/-- Concrete trace and store assertions, restricted to the machine's actual admitted history. -/
structure Holds (b : Api.Built) (cf : Nat) (m : NativeMachine) : Prop where
  history : Run.HistoryOf b cf m
  sites : ∀ i ∈ [1, 2], Programs.acquisitionAt b.program (acquirePath i) = true
  placement : ∀ i ∈ [1, 2], OncePlaced (Node.eff b.program) (acquirePath i) = true
  registrations : Registrations m
  releases : ReleaseDebits m
  logs : LogDebits m

/-- Load obligation of `releases_once`: certified source acquisitions exist, with no trace or log entries. -/
theorem load (total cf : Nat) (b : Api.Built) (hb : Api.Author.build (crew total) = .ok b) :
    Holds b cf (Api.load b.program cf) := by
  refine ⟨⟨[], trivial, rfl⟩, ?_, Programs.crew_acquire_once_placed total b hb, ?_, ?_, ?_⟩
  · rw [Programs.workers_built_program total b hb]
    exact Programs.workers_acquisition_sites total
  · intro i _
    exact Nat.zero_le 1
  · intro i _
    exact Nat.le_refl 0
  · refine ⟨?_, ?_⟩
    · intro v hv
      change v ∈ ([] : List Val) at hv
      exact False.elim (List.not_mem_nil hv)
    · intro i _
      exact Nat.le_refl 0

/-- History extension of `releases_once`: retain the exact admission predicate and call table. -/
theorem history_step (b : Api.Built) (cf : Nat) (m : NativeMachine)
    (x : Nat × NativeDecision) (hm : Run.HistoryOf b cf m)
    (hx : Run.Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2) :
    Run.HistoryOf b cf (Run.stepBy b m x) := by
  obtain ⟨history, adm, heq⟩ := hm
  refine ⟨history ++ [x], ?_, ?_⟩
  · apply Run.admitted_snoc _ _ (Run.stepBy b) history _ x adm
    intro _ _
    rw [← heq]
    exact hx
  · rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← heq]

/-- Flag edit leaf of `releases_once`: installing middleware writes no trace or store cell.
The step assembly consumes this leaf without a planned preservation goal. -/
theorem middleware_step (b : Api.Built) (cf fuel : Nat) (m : NativeMachine)
    (hm : Holds b cf m) : Holds b cf (Run.stepBy b m (fuel, .installMiddleware)) := by
  refine ⟨history_step b cf m (fuel, .installMiddleware) hm.history trivial, hm.sites, hm.placement, ?_, ?_, ?_⟩
  · exact hm.registrations
  · exact hm.releases
  · exact hm.logs

/-- Yield edit leaf of `releases_once`: an override changes neither trace counts nor the log.
The step assembly consumes this leaf without a planned preservation goal. -/
theorem yield_step (b : Api.Built) (cf fuel : Nat) (m : NativeMachine)
    (id : FiberId) (verdict : Bool) (hm : Holds b cf m) :
    Holds b cf (Run.stepBy b m (fuel, .yieldVerdict id verdict)) := by
  have same : (Run.stepBy b m (fuel, .yieldVerdict id verdict)).trace = m.trace ∧
      (Run.stepBy b m (fuel, .yieldVerdict id verdict)).state = m.state := by
    change (m.modify id fun f => { f with yieldOverride := some verdict }).trace = m.trace ∧
      (m.modify id fun f => { f with yieldOverride := some verdict }).state = m.state
    unfold RunMachine.modify
    split <;> exact ⟨rfl, rfl⟩
  refine ⟨history_step b cf m (fuel, .yieldVerdict id verdict) hm.history trivial, hm.sites, hm.placement, ?_, ?_, ?_⟩
  · unfold Registrations
    rw [same.1]
    exact hm.registrations
  · unfold ReleaseDebits
    rw [same.1]
    exact hm.releases
  · unfold LogDebits log
    rw [same.1, same.2]
    exact hm.logs

/-- The actual crew release-start loop consumes available credits at its certified acquisition paths.
Step of `releases_step`: whole-configuration custody must supply `available` at each pending start.
This local clause keeps the native table, other fibers, stack and unfinished commands. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem release_command (b : Api.Built) (m : NativeMachine) (id : FiberId)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann)) (c : Capture) (exit : ExitV)
    (found : m.fiber? id = some f)
    (current : f.frame.current = suspendBodyAt b.program (.store (.foreign c exit)))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield)
    (available : ∀ i ∈ [1, 2], m.trace.countP (releaseAt (acquirePath i)) +
      ReleaseCustody.credit (acquirePath i) (.foreign c) ≤
      m.trace.countP (registeredAt (acquirePath i))) :
    ReleaseDebits (driveStep (evaluator := evaluatorFor b.program b.table)
      (interpOf b.program b.table) m (.loop id yielding) rest).1 := by
  intro i hi
  exact ReleaseCustody.release_loop_debit b.program b.table m id f yielding rest
    (acquirePath i) c exit found current interrupt override budget (available i hi)

/-- The actual workers load satisfies the concrete cleanup-credit assertion.
Consumer: the load clause of the command custody proof for `releases_step`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem load_custody (b : Api.Built) (cf : Nat) :
    ∀ i ∈ [1, 2], ReleaseCustody.Control.Funded (acquirePath i) (Api.load b.program cf) [] := by
  intro i _
  exact ReleaseCustody.Control.load_funded (acquirePath i) b.program cf

/-- Registration preserves cleanup custody on the actual selected worker command.
Consumer: the registration frame clause of `releases_step`.
The pending command suffix and all other fibers remain in the concrete assertion. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem registration_custody_command (b : Api.Built) (cf : Nat) (m : NativeMachine)
    (id : FiberId) (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (scope : Nat) (a : Val) (fin : FinName) (held : Holds b cf m)
    (funded : ∀ i ∈ [1, 2], ReleaseCustody.Control.Funded (acquirePath i) m (.loop id yielding :: rest))
    (found : m.fiber? id = some f)
    (current : f.frame.current = .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    ∀ i ∈ [1, 2], ReleaseCustody.Control.Funded (acquirePath i)
      (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.loop id yielding) rest).1
      (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.loop id yielding) rest).2 := by
  intro i hi
  have unique := (Guard.guardState_reachable b.program b.table cf m held.history.reachable).fiberIds
  exact ReleaseCustody.Control.registration_loop_funded b.program b.table m id f yielding rest
    (acquirePath i) scope a fin unique (funded i hi) found current interrupt override budget

/-- Starting a release preserves concrete custody and supplies the original release-debit assertion.
Consumer: the counted release-start command clause of `releases_step`.
Its credit is read from the actual configuration, without a separate available-credit premise. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem release_custody_command (b : Api.Built) (cf : Nat) (m : NativeMachine)
    (id : FiberId) (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (c : Capture) (exit : ExitV) (held : Holds b cf m)
    (funded : ∀ i ∈ [1, 2], ReleaseCustody.Control.Funded (acquirePath i) m (.loop id yielding :: rest))
    (found : m.fiber? id = some f)
    (current : f.frame.current = suspendBodyAt b.program (.store (.foreign c exit)))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    (∀ i ∈ [1, 2], ReleaseCustody.Control.Funded (acquirePath i)
      (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.loop id yielding) rest).1
      (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.loop id yielding) rest).2) ∧
    ReleaseDebits (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
      (.loop id yielding) rest).1 := by
  have unique := (Guard.guardState_reachable b.program b.table cf m held.history.reachable).fiberIds
  have allFunded : ∀ i ∈ [1, 2], ReleaseCustody.Control.Funded (acquirePath i)
      (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.loop id yielding) rest).1
      (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.loop id yielding) rest).2 := by
    intro i hi
    exact ReleaseCustody.Control.release_loop_funded b.program b.table m id f yielding rest
      (acquirePath i) c exit unique (funded i hi) found current interrupt override budget
  exact ⟨allFunded, fun i hi => ReleaseCustody.Control.Funded.read (allFunded i hi)⟩

/-- Actual scope-add transfers the registered source credit to storage or its closing response.
Consumer: the scope-add command clause of `releases_step`.
The reachable scope store must still supply distinct entries and fresh registration keys. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem scope_add_custody_command (b : Api.Built) (cf : Nat) (m : NativeMachine)
    (id : FiberId) (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (scope : Nat) (entry : ScopeEntry) (a : Val) (fin : FinName) (lower : List NCode)
    (held : Holds b cf m)
    (funded : ∀ i ∈ [1, 2], ReleaseCustody.Control.Funded (acquirePath i) m (.loop id yielding :: rest))
    (scopeUnique : (m.state.scopes.entries.map ScopeEntry.key).Nodup)
    (found : m.fiber? id = some f)
    (current : f.frame.current = .sync (.op (.scopeAdd scope fin)))
    (stack : f.frame.stack =
      .onSuccess (.sync (.op (.scopeAdd scope fin))) (.afterScopeAdd a fin) :: lower)
    (entryFound : m.state.scopes.entryAt scope = some entry)
    (status : (entry.scope.isClosed = false ∧ m.state.nextName ∉ entry.scope.finalizerKeys) ∨
      ∃ exit, entry.scope.closingExit? = some exit)
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    (∀ i ∈ [1, 2], ReleaseCustody.Control.Funded (acquirePath i)
      (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.loop id yielding) rest).1
      (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.loop id yielding) rest).2) ∧
    ReleaseDebits (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
      (.loop id yielding) rest).1 := by
  have unique := (Guard.guardState_reachable b.program b.table cf m held.history.reachable).fiberIds
  have allFunded : ∀ i ∈ [1, 2], ReleaseCustody.Control.Funded (acquirePath i)
      (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.loop id yielding) rest).1
      (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.loop id yielding) rest).2 := by
    intro i hi
    rcases status with ⟨opened, fresh⟩ | ⟨exit, closing⟩
    · exact ReleaseCustody.Control.scope_add_open_loop_funded b.program b.table m id f yielding rest
        (acquirePath i) scope entry a fin lower unique scopeUnique (funded i hi) found current stack
        entryFound opened fresh interrupt override budget
    · exact ReleaseCustody.Control.scope_add_closed_loop_funded b.program b.table m id f yielding rest
        (acquirePath i) scope entry a fin exit lower unique (funded i hi) found current stack
        entryFound closing interrupt override budget
  exact ⟨allFunded, fun i hi => ReleaseCustody.Control.Funded.read (allFunded i hi)⟩

/-- Registration preservation obligation of `releases_once`.
Reach: actual crew histories, all budgets, controls and admitted host answers.
It needs the static acquisition placement and the control-source provenance invariant.
It proves no release progress; consumer: `step` and then `history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal registrations_step :
  ∀ (total cf : Nat) (b : Api.Built) (m : NativeMachine) (x : Nat × NativeDecision),
    Api.Author.build (crew total) = .ok b → Holds b cf m →
    Run.Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2 →
    Registrations (Run.stepBy b m x)

/-- Release preservation obligation of `releases_once`.
Reach: actual crew histories, including incomplete release commands and interruption.
It needs each released closure to originate in its own registered scope entry.
It proves no release order; consumer: `step` and then `history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal releases_step :
  ∀ (total cf : Nat) (b : Api.Built) (m : NativeMachine) (x : Nat × NativeDecision),
    Api.Author.build (crew total) = .ok b → Holds b cf m →
    Run.Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2 →
    ReleaseDebits (Run.stepBy b m x)

/-- Store preservation obligation of `releases_once`.
Reach: the second allocated reference in actual crew histories at every command boundary.
It needs the cell's writer census and the value captured at each acquisition source.
It proves no host behavior; consumer: `step` and then `history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
proof_goal logs_step :
  ∀ (total cf : Nat) (b : Api.Built) (m : NativeMachine) (x : Nat × NativeDecision),
    Api.Author.build (crew total) = .ok b → Holds b cf m →
    Run.Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2 →
    LogDebits (Run.stepBy b m x)

/-- Step assembly of `releases_once`, modulo its three preservation obligations. -/
theorem step (total cf : Nat) (b : Api.Built) (hb : Api.Author.build (crew total) = .ok b)
    (m : NativeMachine) (x : Nat × NativeDecision) (hm : Holds b cf m)
    (hx : Run.Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2) :
    Holds b cf (Run.stepBy b m x) := by
  by_cases hf : x.2 = .installMiddleware
  · have heq : x = (x.1, .installMiddleware) := Prod.ext rfl hf
    rw [heq]
    exact middleware_step b cf x.1 m hm
  · cases hd : x.2 with
    | yieldVerdict id verdict =>
      have heq : x = (x.1, .yieldVerdict id verdict) := Prod.ext rfl hd
      rw [heq]
      exact yield_step b cf x.1 m id verdict hm
    | fire _ | flush | evaluate _ | answerAsync _ _ _ | interruptFrom _ _ _ |
        installMiddleware | advance _ =>
      exact ⟨history_step b cf m x hm.history hx, hm.sites, hm.placement, registrations_step total cf b m x hb hm hx,
        releases_step total cf b m x hb hm hx, logs_step total cf b m x hb hm hx⟩

/-- History assembly of `releases_once`, using the existing admitted-history lift. -/
theorem history (total cf : Nat) (b : Api.Built) (hb : Api.Author.build (crew total) = .ok b)
    (m : NativeMachine) (hm : Run.HistoryOf b cf m) : Holds b cf m :=
  Run.history_keeps b cf (Holds b cf) (load total cf b hb) (step total cf b hb) m hm

/-- Read obligation of `releases_once`: the concrete debit assertions imply no duplicate log entry. -/
theorem read (b : Api.Built) (cf : Nat) (m : NativeMachine) (hm : Holds b cf m) :
    (log m).Nodup := by
  rw [List.nodup_iff_count]
  intro v
  by_cases hv : v ∈ log m
  · rcases hm.logs.1 v hv with rfl | rfl
    · exact Nat.le_trans (hm.logs.2 1 List.mem_cons_self)
        (Nat.le_trans (hm.releases 1 List.mem_cons_self) (hm.registrations 1 List.mem_cons_self))
    · have hi : 2 ∈ [1, 2] := List.mem_cons_of_mem _ List.mem_cons_self
      exact Nat.le_trans (hm.logs.2 2 hi)
        (Nat.le_trans (hm.releases 2 hi) (hm.registrations 2 hi))
  · exact (List.count_eq_zero_of_not_mem hv).symm ▸ Nat.zero_le 1

end Test.Dogfood.Scenario.Workers.Assertions
