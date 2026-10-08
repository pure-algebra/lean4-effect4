import Effect4.Laws.Program.Typed.Edits

/-!
# Test.Program.TimerColumn — row 134 (a)'s timer column and the clock's firing edit

`E4-TYPED-CE-024` (seat D3's probe, `docs/research/2026-10-01-landing/seat-D3/probes/ClockSome.lean`)
refuted `EditClockSome`: a typed machine whose timer holds a sleep for the root at token 0, at a
world declaring that token `number`; the fired resume carries `void`, which `I` must type at the
token. Row 134 (a) adds the timer column to `J` (`WorldValid.timers`: every sleeper's token is
declared at a type `void` fits), and `edit_clockSome` proves the edit.

* **Refusal.** The probe's world is not valid: the column reads the sleeper's `number` declaration
  (`natWorld_refused`).
* **The edit.** The same machine and step, the token declared `void`: the edit's conclusion
  (`queued_typed`), from `edit_clockSome` alone.
* **The landing boundary** (`driveStep`'s `resume` arm, `Machine/Fibers.lean:1865-1878`, the case
  split `resume_step` proves over): the owed resume lands only at an active park on its token
  (`matching_lands`); a stale token (`stale_inert`), an unparked fiber (`unparked_inert`, the
  probe's running root) and an absent fiber (`absent_inert`) leave the machine as it was.
* **The frontier.** A sleep not yet due fires nothing: the step is `clockNone`'s, and the sleeper
  stays (`late_frontier`); the next step to its deadline fires it (`late_fires`).

The behaviours are finite checks of the reference machine (`rfl`); the typing statements are
instances of the general theorems.
-/

set_option autoImplicit false

namespace Test.Program.TimerColumn

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

def rootProgram : NativeEff := .succeed (.lit .unit)
def unitTy : EffTy := EffTy.pure .unit
def natTy : EffTy := EffTy.pure .nat

/-- The root, running, with nothing saved. -/
def fiber : RFiber :=
  { RunFiber.make Api.root (.pure (.success .unit)) true (stores.budgetOf emptyCtx) emptyCtx with
    running := true }

/-- The empty store with one sleep: the root at token 0, deadline 0. -/
def sleepState : Stores := { Stores.empty with timers := Stores.empty.timers.sleep Api.root 0 0 }

def machine : RState :=
  { loadR rootProgram 20 20 with fibers := [fiber], state := sleepState, nextToken := 1 }

/-- The token declared at `tokenTy`. -/
def worldAt (tokenTy : EffTy) : W :=
  { initialWorld unitTy with
    state := sleepState
    Θ := fun id t => if id = Api.root ∧ t = 0 then some tokenTy else none }

/-- The repaired witness: the sleeper's token declared `void`. -/
abbrev world : W := worldAt unitTy
/-- Seat D3's witness: the sleeper's token declared `number`. -/
abbrev natWorld : W := worldAt natTy

theorem member_fiber {f : RFiber} (hf : f ∈ machine.fibers) : f = fiber := by
  change f ∈ [fiber] at hf
  exact List.mem_singleton.mp hf

theorem timer_keys : Guard.wakeKeys machine.state.timers.wake = [(Api.root, 0)] := rfl

/-! ## Refusal: `E4-TYPED-CE-024`'s world -/

/-- **The probe's world is refused**: the timer column reads the sleeper's declaration, `number`,
and `void` does not fit it. -/
theorem natWorld_refused : ¬ WorldValid unitTy natWorld machine := by
  intro valid
  have member : (Api.root, 0) ∈ Guard.wakeKeys machine.state.timers.wake := by
    rw [timer_keys]
    exact List.mem_singleton_self _
  obtain ⟨ty, declared, demand⟩ := valid.timers _ member
  change (if Api.root = Api.root ∧ 0 = 0 then some natTy else none) = some ty at declared
  rw [if_pos ⟨rfl, rfl⟩] at declared
  cases declared
  exact absurd (show Ty.unit.sub Ty.nat = true from demand) (by decide +kernel)

/-! ## The edit at the repaired witness -/

theorem valid : WorldValid unitTy world machine := by
  have old := initial_world_valid_at unitTy nativeServiceTy rootProgram 20 20
  refine
    { ids := rfl, fibers := old.fibers, heap := old.heap, promises := old.promises,
      tokens := ?_, tokenBound := ?_, tokenTargets := ?_, state := rfl, wf := ?_,
      cells := old.cells, root := old.root, timers := ?_,
      waiters := (fun _ _ h => by cases h),
      children := fun f hf c hc => by rw [member_fiber hf] at hc; cases hc }
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
      TimerStore.sleep_wf Stores.empty_wf.2.2.2 Api.root 0 0⟩
  · intro k hk
    rw [timer_keys, List.mem_singleton] at hk
    subst hk
    refine ⟨unitTy, ?_, Ty.sub_refl _⟩
    change (if Api.root = Api.root ∧ (0 : Nat) = 0 then some unitTy else none) = some unitTy
    rw [if_pos ⟨rfl, rfl⟩]

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
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
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
  refine ⟨typedState, rfl, ?_, ⟨rfl, fun o ho => nomatch ho⟩, ⟨rfl, .of_nil rfl⟩⟩
  intro f hf _ idle
  rw [member_fiber hf] at idle
  cases idle

/-- The clock step of 0 fires the sleep: the root is owed `succeed void` at token 0, now. -/
def owed : Owed RProgram := ⟨Api.root, 0, .pure (.success .unit), .now⟩

/-- The machine after the step: the sleep popped. -/
def afterClock : RState := { machine with state := ((interpR rootProgram).clockStep 0 machine.state).2 }

theorem fired :
    (interpR rootProgram).clockStep 0 machine.state =
      (some owed, ((interpR rootProgram).clockStep 0 machine.state).2) := rfl

theorem drained :
    drainOwed afterClock [owed] = (afterClock, [Cmd.resume Api.root 0 (.pure (.success .unit))]) :=
  rfl

theorem popped : Guard.wakeKeys afterClock.state.timers.wake = [] := rfl

/-- **The edit at the repaired witness**: the probe's step, the token declared `void`, keeps `J`
and types the queued resume (`edit_clockSome`; the probe's `clockSome_false` read this
conclusion at `number`). -/
theorem queued_typed : ∃ w', world.leHost w' ∧
    MachineTyped (rootProgram : ProgramSource) unitTy w' afterClock ∧
    ConfigTyped (rootProgram : ProgramSource) unitTy w' afterClock
      [Cmd.resume Api.root 0 (.pure (.success .unit)), Cmd.drainDue] := by
  obtain ⟨w', ord, machine', config⟩ :=
    edit_clockSome (rootProgram : ProgramSource) unitTy world machine 0 owed _ machine_typed rfl fired
  exact ⟨w', ord, machine', config rfl⟩

/-! ## The landing boundary -/

def resumeCode : RProgram := .pure (.success .unit)

/-- The root parked at `token`. -/
def parkedAt (token : Nat) : RState :=
  { afterClock with fibers := [{ fiber with running := false, parked := .withGuard token }] }

/-- **An active park on the token**: the resume lands, the fiber unparked, its evaluation next. -/
theorem matching_lands :
    (letI := termEvaluatorFor rootProgram
     driveStep (interpR rootProgram) (parkedAt 0) (.resume Api.root 0 resumeCode) [Cmd.drainDue]).2 =
      [Cmd.evaluate Api.root, Cmd.drainDue] := rfl

theorem matching_unparks :
    ((letI := termEvaluatorFor rootProgram
      driveStep (interpR rootProgram) (parkedAt 0) (.resume Api.root 0 resumeCode)
        [Cmd.drainDue]).1.fiber? Api.root).map (·.parked) = some .notParked := rfl

/-- **A stale token**: the fiber parked at another token; the resume changes nothing. -/
theorem stale_inert :
    (letI := termEvaluatorFor rootProgram
     driveStep (interpR rootProgram) (parkedAt 1) (.resume Api.root 0 resumeCode) [Cmd.drainDue]) =
      (parkedAt 1, [Cmd.drainDue]) := rfl

/-- **An unparked fiber** (the probe's running root): the resume changes nothing. -/
theorem unparked_inert :
    (letI := termEvaluatorFor rootProgram
     driveStep (interpR rootProgram) afterClock (.resume Api.root 0 resumeCode) [Cmd.drainDue]) =
      (afterClock, [Cmd.drainDue]) := rfl

/-- **An absent fiber**: the resume changes nothing. -/
theorem absent_inert :
    (letI := termEvaluatorFor rootProgram
     driveStep (interpR rootProgram) afterClock (.resume ⟨7⟩ 0 resumeCode) [Cmd.drainDue]) =
      (afterClock, [Cmd.drainDue]) := rfl

/-! ## The frontier -/

/-- A sleep due at 5. -/
def lateState : Stores := { Stores.empty with timers := Stores.empty.timers.sleep Api.root 0 5 }

/-- **Not yet due**: the step fires nothing (`clockNone`'s case) and the sleeper stays. -/
theorem late_frontier :
    ((interpR rootProgram).clockStep 0 lateState).1 = none ∧
      Guard.wakeKeys ((interpR rootProgram).clockStep 0 lateState).2.timers.wake =
        [(Api.root, 0)] := ⟨rfl, rfl⟩

/-- **At its deadline** the sleep fires. -/
theorem late_fires : ((interpR rootProgram).clockStep 5 lateState).1 = some owed := rfl

end Test.Program.TimerColumn
