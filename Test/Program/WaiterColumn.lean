import Effect4.Laws.Program.Typed.Edits

/-!
# Test.Program.WaiterColumn — the repaired CE-026 wake boundary

Placement: semantics Concept 4, scheduler step preservation, with Concept 1's store columns;
`M6Ledger.step_wake`, decision 134(b). `wake_preserves` supplies the general theorem. These
controls retain seat D3's exact batched-waiter witness: a `(unit, never)` cell whose token used
to be declared `nat`. That world is now refused. Declaring the same token `unit` gives a typed
input and the real wake step stays typed. Completed and uncompleted cells exercise delivery and
rejoining respectively. Repeating the wake adds no delivery; missing cells are inert. No progress, fairness, host
reply or generated-target claim follows from these finite controls.

Historical refutation: `docs/research/2026-10-01-landing/seat-D3/probes/Wake.lean`; unchanged.
-/

set_option autoImplicit false

namespace Test.Program.WaiterColumn
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

def rootProgram : NativeEff := .succeed (.lit .unit)
def unitTy : EffTy := EffTy.pure .unit
def natTy : EffTy := EffTy.pure .nat

def code : RProgram := .pure (.success .unit)

/-- The batch the cell's list holds: the root at token 0. -/
def waiter : Waiter Unit := ⟨Api.root, 0, 0, ()⟩

/-- Deferred 0's list: no pending waiter, a scheduled batch. -/
def wakeList : WakeList Unit := { waiters := [], batch := some [waiter], phase := 1 }

/-- Deferred 0, completed with `succeed void`. -/
def cell : DeferredCell := { completion := some (.ofExit (.success .unit)), wake := wakeList }

def fiber : RFiber :=
  { RunFiber.make Api.root code true (stores.budgetOf emptyCtx) emptyCtx with running := true }

/-- One Deferred, completed, whose list holds a batch with the root at token 0. -/
def cellState : Stores :=
  { Stores.empty with deferreds := { cells := [cell], due := [] } }

def machine : RState :=
  { loadR rootProgram 20 20 with fibers := [fiber], state := cellState, nextToken := 1 }

def worldAt (tokenTy : EffTy) : W :=
  { initialWorld unitTy with
    state := cellState
    «Π» := fun key => if key.index = 0 then some (.unit, .never) else none
    Θ := fun id t => if id = Api.root ∧ t = 0 then some tokenTy else none }

abbrev world : W := worldAt unitTy
abbrev natWorld : W := worldAt natTy

theorem cellAt_some {key : DeferredKey} {c : DeferredCell}
    (h : machine.state.deferreds.cellAt key = some c) : key.index = 0 ∧ c = cell := by
  cases key with
  | mk index =>
    cases index with
    | zero => exact ⟨rfl, (Option.some.inj h).symm⟩
    | succ n => cases h

theorem waiter_keys : Guard.wakeKeys cell.wake = [(Api.root, 0)] := rfl

/-- The historical number-token witness is refused by the new waiter column. -/
theorem natWorld_refused : ¬ WorldValid unitTy natWorld machine := by
  intro valid
  have key : (Api.root, 0) ∈ Guard.wakeKeys cell.wake := by
    rw [waiter_keys]
    exact List.mem_singleton_self _
  obtain ⟨ty, declared, demand⟩ := valid.waiters ⟨0⟩ cell rfl .unit .never rfl _ key
  change (if Api.root = Api.root ∧ 0 = 0 then some natTy else none) = some ty at declared
  rw [if_pos ⟨rfl, rfl⟩] at declared
  cases declared
  exact absurd (show Ty.unit.sub Ty.nat = true from demand.1) (by decide +kernel)

theorem member_fiber {f : RFiber} (hf : f ∈ machine.fibers) : f = fiber := by
  change f ∈ [fiber] at hf
  exact List.mem_singleton.mp hf

theorem valid : WorldValid unitTy world machine := by
  have old := initial_world_valid_at unitTy nativeServiceTy rootProgram 20 20
  refine
    { ids := rfl, fibers := old.fibers, heap := old.heap, promises := ?_,
      tokens := ?_, tokenBound := ?_, tokenTargets := ?_, state := rfl, wf := ?_,
      cells := ⟨(fun i v h => nomatch h), ?_⟩, root := old.root, timers := WakeTyped.empty _ _, waiters := ?_,
      children := fun f hf c hc => by rw [member_fiber hf] at hc; cases hc }
  · intro key
    change (if key.index = 0 then some (Ty.unit, Ty.never) else none).isSome = true ↔ key.index < 1
    by_cases c : key.index = 0
    · rw [if_pos c, c]
      exact ⟨fun _ => Nat.zero_lt_one, fun _ => rfl⟩
    · rw [if_neg c]
      exact ⟨fun h => Bool.noConfusion h, fun h => absurd (Nat.lt_one_iff.mp h) c⟩
  · intro f hf token hp
    rw [member_fiber hf] at hp
    cases hp
  · intro id token ty h
    change (if id = Api.root ∧ token = 0 then some unitTy else none) = some ty at h
    by_cases c : id = Api.root ∧ token = 0
    · rw [c.2]
      decide
    · rw [if_neg c] at h
      cases h
  · intro id token ty h
    change (if id = Api.root ∧ token = 0 then some unitTy else none) = some ty at h
    by_cases c : id = Api.root ∧ token = 0
    · rw [c.1]
      rfl
    · rw [if_neg c] at h
      cases h
  · exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
      Stores.empty_wf.2.2.2⟩
  · intro i v hv types declared completion hc
    have same : v = cell := by
      cases i with
      | zero =>
        change some _ = some v at hv
        exact (Option.some.inj hv).symm
      | succ n => exact nomatch hv
    have zero : i = 0 := by
      cases i with
      | zero => rfl
      | succ n => exact nomatch hv
    subst zero
    rw [same] at hc
    cases hc
    change (if (0 : Nat) = 0 then some (Ty.unit, Ty.never) else none) = some types at declared
    rw [if_pos rfl] at declared
    cases declared
    rfl
  · intro key c hc a e hPi
    obtain ⟨zero, same⟩ := cellAt_some hc
    rw [same]
    change (if key.index = 0 then some (Ty.unit, Ty.never) else none) = some (a, e) at hPi
    rw [if_pos zero] at hPi
    cases hPi
    intro k hk
    rw [waiter_keys, List.mem_singleton] at hk
    subst hk
    exact ⟨unitTy, rfl, Ty.sub_refl _, Ty.sub_refl _⟩

theorem internalKeys_machine : Guard.internalKeys machine = [(Api.root, 0)] := rfl

theorem no_requests (id : FiberId) (token : Nat) : requestOfR machine id token = none := by
  unfold requestOfR
  cases hf : machine.fiber? id with
  | none => rfl
  | some found =>
    rw [member_fiber (List.mem_of_find?_eq_some hf)]
    rfl

theorem scheduler : SchedulerState machine := by
  constructor
  · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  · intro f hf
    rw [member_fiber hf]
    decide
  · exact List.nodup_nil
  · intro race member; cases member
  · intro race member; cases member
  · intro key member
    rw [internalKeys_machine, List.mem_singleton] at member
    rw [member]
    decide
  · intro id token request hr
    rw [no_requests] at hr
    cases hr
  · intro id token request hr
    rw [no_requests] at hr
    cases hr
  · intro f hf
    rw [member_fiber hf]
    rfl
  · intro f hf hp
    rw [member_fiber hf] at hp
    exact False.elim (hp rfl)
  · intro f hf token hp
    rw [member_fiber hf] at hp
    cases hp
  · intro f hf hx
    rw [member_fiber hf] at hx
    cases hx
  · intro f hf hx
    rw [member_fiber hf] at hx
    cases hx
  · intro f hf hd
    rw [member_fiber hf] at hd
    cases hd
  · intro raceId race hr; cases hr
  · intro raceId race hr; cases hr
  · intro f hf p hp
    rw [member_fiber hf] at hp
    cases hp
  · intro f hf o ho
    rw [member_fiber hf] at ho
    cases ho

theorem typedState : TypedState (rootProgram : ProgramSource) unitTy world machine := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_, scheduler, ⟨?_, ?_⟩, ?_⟩
  · intro f hf
    rw [member_fiber hf]
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty _
      exact ⟨ty, .nil ty, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro p hp; cases hp
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro v hv; cases hv
    · exact servicesFit_empty _
  · intro race member; cases member
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨fun i v hv a e declared c hc => ?_⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
    have same : v = cell := by
      cases i with
      | zero =>
        change some _ = some v at hv
        exact (Option.some.inj hv).symm
      | succ n => exact nomatch hv
    have zero : i = 0 := by
      cases i with
      | zero => rfl
      | succ n => exact nomatch hv
    subst zero
    rw [same] at hc
    cases hc
    change (if (0 : Nat) = 0 then some (Ty.unit, Ty.never) else none) = some (a, e) at declared
    rw [if_pos rfl] at declared
    cases declared
    exact ⟨trivial, trivial⟩
  · intro f hf token hp
    rw [member_fiber hf] at hp
    cases hp
  · intro f hf p hp
    rw [member_fiber hf] at hp
    cases hp
  · intro f hf o ho
    rw [member_fiber hf] at ho
    cases ho
  · intro f hf id marker
    rw [member_fiber hf] at marker
    cases marker

theorem machine_typed : MachineTyped (rootProgram : ProgramSource) unitTy world machine := by
  refine ⟨typedState, rfl, ?_, ⟨rfl, fun o ho => nomatch ho⟩, rfl⟩
  intro f hf _ idle
  rw [member_fiber hf] at idle
  cases idle

def key : WakeKey := WakeKey.deferred ⟨0⟩

/-- **The input is in `I`**: the queued `wake` reads no code, owns nothing and carries no key. -/
theorem config_typed : ConfigTyped (rootProgram : ProgramSource) unitTy world machine
    [.wake key 1] := by
  refine ⟨machine_typed, ?_, ?_⟩
  · intro f _ _ reads
    obtain ⟨_, r⟩ := reads
    rcases r with r | r <;> (rw [List.mem_singleton] at r; cases r)
  · refine ⟨?_, ?_, ?_, List.nodup_nil, ⟨trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro k member
      cases member
    · intro fiber token request _ member
      cases member
    · intro source exit observer member
      rw [List.mem_singleton] at member
      cases member
    · intro race child member
      rw [List.mem_singleton] at member
      cases member
    · intro host yielding race member
      rw [List.mem_singleton] at member
      cases member
    · intro mode scope target interruptor extra member
      rw [List.mem_singleton] at member
      cases member

    · intro source exit o member
      rw [List.mem_singleton] at member
      cases member

def result :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine (.wake key 1) []

/-- The owed resume the batch wake leaves: the waiter, its token, the stored completion. -/
def owed : Owed (Completion Val Err Defect FiberId Ann) :=
  ⟨Api.root, 0, .ofExit (.success .unit), .now⟩

theorem result_due : result.1.state.deferreds.due = [owed] := rfl


/-- The repaired input is inhabited, and the actual step remains in `I`. -/
theorem result_typed : ∃ w', world.leHost w' ∧
    ConfigTyped (rootProgram : ProgramSource) unitTy w' result.1 result.2 := by
  exact wake_preserves (rootProgram : ProgramSource) unitTy key 1
    world machine [] rfl config_typed

theorem completed_batch_cleared :
    (result.1.state.deferreds.cellAt ⟨0⟩).map (·.wake.batch) = some none := rfl

def pendingMachine : RState :=
  { machine with state := { cellState with deferreds :=
    { cells := [{ cell with completion := none }], due := [] } } }

def pendingResult :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) pendingMachine (.wake key 1) []

/-- An uncompleted cell owes nothing and rejoins its batch to pending waiters. -/
theorem uncompleted_rejoins :
    pendingResult.1.state.deferreds.due = [] ∧
    (pendingResult.1.state.deferreds.cellAt ⟨0⟩).map (·.wake.waiters) = some [waiter] ∧
    (pendingResult.1.state.deferreds.cellAt ⟨0⟩).map (·.wake.batch) = some none :=
  ⟨rfl, rfl, rfl⟩

/-- Deferreds complete inline and never mint schedule stamps (`Stores.wakeList`): this family
does not inspect the stamp. The finite control preserves that deliberate profile boundary. -/
theorem deferred_phase_ignored :
    (letI := termEvaluatorFor rootProgram
     driveStep (interpR rootProgram) machine (.wake key 0) []) = result := rfl

/-- The batch has been consumed: another wake does not owe the same completion twice. -/
theorem repeated_wake_no_new_due :
    (letI := termEvaluatorFor rootProgram
     driveStep (interpR rootProgram) result.1 (.wake key 1) []).1.state.deferreds.due =
      [owed] := rfl

theorem absent_cell_inert :
    (letI := termEvaluatorFor rootProgram
     driveStep (interpR rootProgram) machine (.wake (WakeKey.deferred ⟨1⟩) 1) []) =
      (machine, []) := rfl

end Test.Program.WaiterColumn

#print axioms Test.Program.WaiterColumn.natWorld_refused
#print axioms Test.Program.WaiterColumn.config_typed
#print axioms Test.Program.WaiterColumn.result_typed
#print axioms Test.Program.WaiterColumn.result_due
#print axioms Test.Program.WaiterColumn.completed_batch_cleared
#print axioms Test.Program.WaiterColumn.uncompleted_rejoins
#print axioms Test.Program.WaiterColumn.deferred_phase_ignored
#print axioms Test.Program.WaiterColumn.repeated_wake_no_new_due
#print axioms Test.Program.WaiterColumn.absent_cell_inert
