import Test.Dogfood.Proofs.CrewLogHistory
import Test.Dogfood.Scenario.Programs
import Test.Dogfood.Scenario.SourceFragment
import Test.Dogfood.Scenario.SourceOpportunity
import Test.Dogfood.Scenario.Frame
import Effect4.Laws.Program.ReleaseCustody.Execution
import Effect4.Laws.Program.Guard.Decision
import Test.Dogfood.Scenario.ReleaseWrites

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
    (hx : Run.Accepted b.app (Api.HostSession.callTable b.program b.app) m x.2) :
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

/-- Registration preservation obligation of `releases_once`.
Reach: actual crew histories, all budgets, controls and admitted host answers.
It needs the static acquisition placement and the control-source provenance invariant.
It proves no release progress; consumer: `step` and then `history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem registrations_step :
  ∀ (total cf : Nat) (b : Api.Built) (m : NativeMachine) (x : Nat × NativeDecision),
    Api.Author.build (crew total) = .ok b → Holds b cf m →
    Run.Accepted b.app (Api.HostSession.callTable b.program b.app) m x.2 →
    Registrations (Run.stepBy b m x) := by
  intro total cf b m x built held accepted
  exact SourceOpportunity.workers_registrations_once total cf b built (Run.stepBy b m x)
    (history_step b cf m x held.history accepted)


/-- Release preservation obligation of `releases_once`.
Reach: actual crew histories, including incomplete release commands and interruption.
The concrete custody history supplies its command and outside-loop obligations.
It proves no release order; consumer: `step` and then `history`.
The custody assertion is proved on actual sequential, race-free source histories. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem releases_step :
  ∀ (total cf : Nat) (b : Api.Built) (m : NativeMachine) (x : Nat × NativeDecision),
    Api.Author.build (crew total) = .ok b → Holds b cf m →
    Run.Accepted b.app (Api.HostSession.callTable b.program b.app) m x.2 →
    ReleaseDebits (Run.stepBy b m x) := by
  intro total cf b m x built held accepted
  intro i _
  have reached := history_step b cf m x held.history accepted
  exact ReleaseCustody.Control.Funded.read
    (ReleaseCustody.Execution.history b cf (acquirePath i) (Run.stepBy b m x)
      (Scenario.SourceFragment.workers_built_fragment total b built)
      (Scenario.SourceFragment.workers_built_sequential total b built)
      (Scenario.SourceFragment.workers_built_race_free total b built) reached).funded

/-- Store preservation obligation of `releases_once`.
Reach: the second allocated reference in actual crew histories at every command boundary.
It needs the cell's writer census and the value captured at each acquisition source: the release
note writes the acquired value bound in its environment, not a literal (the control
`ReleaseWrites.readsSlot`).
It proves no host behavior; consumer: `step` and then `history`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem logs_step :
  ∀ (total cf : Nat) (b : Api.Built) (m : NativeMachine) (x : Nat × NativeDecision),
    Api.Author.build (crew total) = .ok b → Holds b cf m →
    Run.Accepted b.app (Api.HostSession.callTable b.program b.app) m x.2 →
    LogDebits (Run.stepBy b m x) := by
  intro total cf b machine decision built held accepted
  have history := history_step b cf machine decision held.history accepted
  have observed := (Proofs.CrewLogHistory.workers total b built cf _ history).observe
    (log (Run.stepBy b machine decision)) (CrewLogs.list_observation _)
  refine ⟨?_, observed.2⟩
  intro value member
  obtain ⟨identity, inside, same⟩ := observed.1 value member
  rcases List.mem_cons.mp inside with first | rest
  · exact .inl (same.trans (congrArg Val.nat first))
  · exact .inr (same.trans (congrArg Val.nat (List.mem_singleton.mp rest)))

/-- Step assembly of `releases_once` from its three proved preservation facts. -/
theorem step (total cf : Nat) (b : Api.Built) (hb : Api.Author.build (crew total) = .ok b)
    (m : NativeMachine) (x : Nat × NativeDecision) (hm : Holds b cf m)
    (hx : Run.Accepted b.app (Api.HostSession.callTable b.program b.app) m x.2) :
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
