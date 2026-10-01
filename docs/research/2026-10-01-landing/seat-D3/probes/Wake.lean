import Effect4.Laws.Program.Typed.Edits
import Test.Counterexamples.Machine.Semantics.M6Capstone

/-!
Seat D3 refutation probe: `StepPreserves` for `wake` (`M6Ledger.step_wake`) is false as stated.

A typed configuration (`I`) with a queued `wake` on Deferred 0's list. The cell is completed with
`succeed void`, which its declared columns `(void, never)` type (`PromiseCell`), and its list holds
a scheduled batch with one waiter, the root at token 0, which the world declares at `number`
(`Θ root 0 = pure nat`). Nothing in `I` relates a cell's waiters (pending or batched) to the
cell's columns; the scheduler clauses read them only as internal keys. The batch wake owes the
waiter the stored completion (`DeferredStore.wakeBatch`), and after the step `StoresOk`'s
`PromiseTable` types each due resume at the waiter token's declaration, at every later world:
`void` is not a number. Run: `LEAN_NUM_THREADS=2 lake env lean
docs/research/2026-10-01-landing/seat-D3/probes/Wake.lean`.
-/

namespace Effect4.Program.Typed.SeatD3.Wake
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

def world : W :=
  { initialWorld unitTy with
    state := cellState
    «Π» := fun key => if key.index = 0 then some (.unit, .never) else none
    Θ := fun id t => if id = Api.root ∧ t = 0 then some natTy else none }

theorem member_fiber {f : RFiber} (hf : f ∈ machine.fibers) : f = fiber := by
  change f ∈ [fiber] at hf
  exact List.mem_singleton.mp hf

theorem valid : WorldValid unitTy world machine := by
  have old := initial_world_valid_at unitTy nativeServiceTy rootProgram 20 20 ⟨rfl, rfl⟩
  refine
    { ids := rfl, fibers := old.fibers, heap := old.heap, promises := ?_,
      tokens := ?_, tokenBound := ?_, tokenTargets := ?_, state := rfl, wf := ?_,
      cells := ⟨(fun i v h => nomatch h), ?_⟩, fiberClosed := old.fiberClosed,
      heapClosed := old.heapClosed, promiseClosed := ?_, tokenClosed := ?_, root := old.root }
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
  · intro key types h
    change (if key.index = 0 then some (Ty.unit, Ty.never) else none) = some types at h
    by_cases c : key.index = 0
    · rw [if_pos c] at h
      cases h
      exact ⟨rfl, rfl⟩
    · rw [if_neg c] at h
      cases h
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
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨fun i v hv a e declared c hc => ?_⟩,
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
  refine ⟨typedState, rfl, ?_, ⟨rfl, fun o ho => nomatch ho⟩⟩
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
  · refine ⟨?_, ?_, ?_, List.nodup_nil, ⟨trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
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

def result :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine (.wake key 1) []

/-- The owed resume the batch wake leaves: the waiter, its token, the stored completion. -/
def owed : Owed (Completion Val Err Defect FiberId Ann) :=
  ⟨Api.root, 0, .ofExit (.success .unit), .now⟩

theorem result_due : result.1.state.deferreds.due = [owed] := rfl

/-- After the wake, no later world types the machine: `PromiseTable` types the owed resume at the
waiter's token, a number, and the completion is `void`. -/
theorem untyped (w' : W) (ord : world.leHost w') (m : RState)
    (due : m.state.deferreds.due = [owed]) : ¬ MachineTyped (rootProgram : ProgramSource) unitTy w' m := by
  intro typed
  have table := typed.wide.stores.c0
  have member : owed ∈ m.state.deferreds.due := by
    rw [due]
    exact List.mem_singleton_self _
  have declared : w'.Θ Api.root 0 = some natTy := ord.1.2.2.2.2.2.1 Api.root 0 natTy rfl
  exact (table owed member natTy declared).1

/-- **`wake` does not keep `I`.** -/
theorem wake_false : ¬ StepPreserves (rootProgram : ProgramSource) unitTy (.wake key 1) := by
  intro step
  obtain ⟨w', ord, typed⟩ := step world machine [] rfl config_typed
  exact untyped w' ord result.1 result_due typed.machine

end Effect4.Program.Typed.SeatD3.Wake

#print axioms Effect4.Program.Typed.SeatD3.Wake.config_typed
#print axioms Effect4.Program.Typed.SeatD3.Wake.wake_false
