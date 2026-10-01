import Effect4.Laws.Program.Typed.Edits
import Test.Counterexamples.Machine.Semantics.M6Capstone

/-!
Seat D3 refutation probe: `EditClockSome` (`M6Edits.clockSome`) is false as stated.

A typed machine (`J`) whose timer store holds a sleep for the root at token 0, deadline 0, while
the world declares that token at `number` (`Θ root 0 = pure nat`). Nothing in `J` relates a
sleeper's token to the `void` its fire resumes it with: `StoresOk` reads no timer, and the
scheduler clauses read a sleeper only as an internal key (below the token counter, requested by
no park). A clock step of 0 fires the sleep and owes `resume root 0 (succeed void)`; `I` after the
edit types that resume's answer at the token's declaration (`QueueOk.payload`, `ResumeOk`), at
every later world, where the declaration is still `number` (`World.le`'s `Θ` extension), and
`void` is not a number. Run: `LEAN_NUM_THREADS=2 lake env lean
docs/research/2026-10-01-landing/seat-D3/probes/ClockSome.lean`.
-/

namespace Effect4.Program.Typed.SeatD3.ClockSome
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

def world : W :=
  { initialWorld unitTy with
    state := sleepState
    Θ := fun id t => if id = Api.root ∧ t = 0 then some natTy else none }

theorem member_fiber {f : RFiber} (hf : f ∈ machine.fibers) : f = fiber := by
  change f ∈ [fiber] at hf
  exact List.mem_singleton.mp hf

theorem valid : WorldValid unitTy world machine := by
  have old := initial_world_valid_at unitTy nativeServiceTy rootProgram 20 20 ⟨rfl, rfl⟩
  refine
    { ids := rfl, fibers := old.fibers, heap := old.heap, promises := old.promises,
      tokens := ?_, tokenBound := ?_, tokenTargets := ?_, state := rfl, wf := ?_,
      cells := old.cells, fiberClosed := old.fiberClosed, heapClosed := old.heapClosed,
      promiseClosed := old.promiseClosed, tokenClosed := ?_, root := old.root }
  · intro f hf token hp
    rw [member_fiber hf] at hp
    cases hp
  · intro id token ty h
    change (if id = Api.root ∧ token = 0 then some natTy else none) = some ty at h
    by_cases c : id = Api.root ∧ token = 0
    · rw [c.2]
      decide
    · rw [if_neg c] at h
      cases h
  · intro id token ty h
    change (if id = Api.root ∧ token = 0 then some natTy else none) = some ty at h
    by_cases c : id = Api.root ∧ token = 0
    · rw [c.1]
      rfl
    · rw [if_neg c] at h
      cases h
  · exact ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h),
      TimerStore.sleep_wf Stores.empty_wf.2.2.2 Api.root 0 0⟩
  · intro id token ty h
    change (if id = Api.root ∧ token = 0 then some natTy else none) = some ty at h
    by_cases c : id = Api.root ∧ token = 0
    · rw [if_pos c] at h
      cases h
      exact ⟨rfl, rfl⟩
    · rw [if_neg c] at h
      cases h

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
  · intro f hf hd
    rw [member_fiber hf] at hd
    cases hd

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
    · intro key value ty lookup
      change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
      rw [Env.Context.getV_empty] at lookup
      cases lookup
  · intro race member; cases member
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
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

/-- **The input is in `J`.** -/
theorem machine_typed : MachineTyped (rootProgram : ProgramSource) unitTy world machine := by
  refine ⟨typedState, rfl, ?_, ⟨rfl, fun o ho => nomatch ho⟩⟩
  intro f hf _ idle
  rw [member_fiber hf] at idle
  cases idle

/-- The clock step of 0 fires the sleep: the root is owed `succeed void` at token 0, now. -/
def owed : Owed RProgram := ⟨Api.root, 0, .pure (.success .unit), .now⟩

theorem fired :
    (interpR rootProgram).clockStep 0 machine.state =
      (some owed, ((interpR rootProgram).clockStep 0 machine.state).2) := rfl

theorem drained :
    drainOwed { machine with state := ((interpR rootProgram).clockStep 0 machine.state).2 } [owed] =
      ({ machine with state := ((interpR rootProgram).clockStep 0 machine.state).2 },
        [Cmd.resume Api.root 0 (.pure (.success .unit))]) := rfl

/-- **`EditClockSome` is false**: its conclusion types the owed resume's answer at the sleeper
token's declaration in every later world, and `void` is not a number. -/
theorem clockSome_false : ¬ EditClockSome (rootProgram : ProgramSource) unitTy := by
  intro edit
  obtain ⟨w', ord, _, config⟩ := edit world machine 0 owed _ machine_typed rfl fired
  rw [drained] at config
  have typed := config rfl
  have payload : Contracts.ResumeOk (TypedProg (rootProgram : ProgramSource)) w' Api.root 0
      (.pure (.success .unit)) :=
    typed.queue.payload _ List.mem_cons_self
  have declared : w'.Θ Api.root 0 = some natTy := ord.1.2.2.2.2.2.1 Api.root 0 natTy rfl
  exact (TypedProg.pure_inv (payload natTy declared)).1

end Effect4.Program.Typed.SeatD3.ClockSome

#print axioms Effect4.Program.Typed.SeatD3.ClockSome.machine_typed
#print axioms Effect4.Program.Typed.SeatD3.ClockSome.clockSome_false
