import Effect4.Laws.Program.Typed.Edits
import Test.Counterexamples.Machine.Semantics.M6Capstone

/-!
Seat D3 refutation probe: `StepPreserves` for `loop` and for `deliver` (`M6Ledger.step_loop`,
`M6Ledger.step_deliver`) is false as stated, at the store arm `deferredCompleteWith`.

A typed configuration (`I`) whose running root's code completes Deferred 0 with `succeed void`,
read by the queued `loop` (or `deliver`). The world declares the cell at `(void, never)`, so the
code is typed (`storePre`'s arm). The cell's wake list holds a waiter, the root at token 0, which
the world declares at `number` (`Θ root 0 = pure nat`). Nothing in `I` relates a cell's waiters
to the cell's columns: the deferred column (`PromiseCell`) reads only the stored completion, and
the scheduler clauses read a waiter only as an internal key. The completion moves the waiter to
the due list with the completion (`DeferredStore.complete`), and after the step `StoresOk`'s
`PromiseTable` types each due resume at the waiter token's declaration, at every later world:
`void` is not a number. Run: `LEAN_NUM_THREADS=2 lake env lean
docs/research/2026-10-01-landing/seat-D3/probes/LoopDeliver.lean`.
-/

namespace Effect4.Program.Typed.SeatD3.LoopDeliver
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

def rootProgram : NativeEff := .succeed (.lit .unit)
def unitTy : EffTy := EffTy.pure .unit
def natTy : EffTy := EffTy.pure .nat

/-- Complete Deferred 0 with `succeed void`, then answer `void`. -/
def code : RProgram :=
  .vis (.inl (.deferredCompleteWith ⟨0⟩ (.ofExit (.success .unit)))) fun _ => .pure (.success .unit)

def fiber : RFiber :=
  { RunFiber.make Api.root code true (stores.budgetOf emptyCtx) emptyCtx with running := true }

/-- One Deferred, not completed, whose wake list holds the root at token 0. -/
def cellState : Stores :=
  { Stores.empty with
    deferreds := { cells := [{ completion := none, wake := WakeList.empty.register Api.root 0 () }],
                   due := [] } }

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
  · intro i v hv types _ completion hc
    have cell : v = { completion := none, wake := WakeList.empty.register Api.root 0 () } := by
      cases i with
      | zero =>
        change some _ = some v at hv
        exact (Option.some.inj hv).symm
      | succ n => exact nomatch hv
    rw [cell] at hc
    cases hc
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
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨fun i v hv a e _ c hc => ?_⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
    have cell : v = { completion := none, wake := WakeList.empty.register Api.root 0 () } := by
      cases i with
      | zero =>
        change some _ = some v at hv
        exact (Option.some.inj hv).symm
      | succ n => exact nomatch hv
    rw [cell] at hc
    cases hc
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

/-- The root's code is typed at `void`: the completion fits the cell's declared columns. -/
theorem code_typed : TypedProg (rootProgram : ProgramSource) world unitTy code :=
  TypedProg.store PUnit.unit ⟨.unit, .never, rfl, ⟨trivial, trivial⟩⟩
    (fun _ _ _ _ => TypedProg.pure ⟨trivial, trivial⟩)

theorem saved : SavedOk (TypedProg (rootProgram : ProgramSource)) ExitOk
    (frameProtocols (rootProgram : ProgramSource)) world unitTy fiber.frame :=
  ⟨unitTy, code_typed, .nil unitTy, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩

/-- **The input is in `I`**, with the code read by the queued command. -/
theorem config_typed (command : RCmd) (reads : command = .loop Api.root false ∨
    command = .deliver Api.root false) :
    ConfigTyped (rootProgram : ProgramSource) unitTy world machine [command] := by
  refine ⟨machine_typed, ?_, ?_⟩
  · intro f hf _ _ _ ty declared
    rw [member_fiber hf] at declared ⊢
    have root : world.Γ fiber.id = some unitTy := rfl
    rw [root] at declared
    cases declared
    exact saved
  · refine ⟨?_, ?_, ?_, ?_, ⟨?_, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      rcases reads with rfl | rfl <;> (subst hc; trivial)
    · intro c hc
      rw [List.mem_singleton] at hc
      rcases reads with rfl | rfl <;> (subst hc; exact ⟨fiber, rfl, rfl, rfl⟩)
    · intro c hc
      rw [List.mem_singleton] at hc
      rcases reads with rfl | rfl <;> (subst hc; trivial)
    · rcases reads with rfl | rfl <;> exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · rcases reads with rfl | rfl <;> trivial
    · intro key member
      rcases reads with rfl | rfl <;> cases member
    · intro fiber token request _ member
      rcases reads with rfl | rfl <;> cases member
    · intro source exit observer member
      rw [List.mem_singleton] at member
      rcases reads with rfl | rfl <;> cases member
    · intro race child member
      rw [List.mem_singleton] at member
      rcases reads with rfl | rfl <;> cases member
    · intro host yielding race member
      rw [List.mem_singleton] at member
      rcases reads with rfl | rfl <;> cases member
    · intro mode scope target interruptor extra member
      rw [List.mem_singleton] at member
      rcases reads with rfl | rfl <;> cases member

def loopResult :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine (.loop Api.root false) []

def deliverResult :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine (.deliver Api.root false) []

/-- The owed resume the completion leaves: the waiter, its token, the completion. -/
def owed : Owed (Completion Val Err Defect FiberId Ann) :=
  ⟨Api.root, 0, .ofExit (.success .unit), .now⟩

theorem loop_due : loopResult.1.state.deferreds.due = [owed] := rfl

theorem deliver_due : deliverResult.1.state.deferreds.due = [owed] := rfl

/-- After the completion, no later world types the machine: `PromiseTable` types the owed resume
at the waiter's token, a number, and the completion is `void`. -/
theorem untyped (w' : W) (ord : world.leHost w') (m : RState)
    (due : m.state.deferreds.due = [owed]) : ¬ MachineTyped (rootProgram : ProgramSource) unitTy w' m := by
  intro typed
  have table := typed.wide.stores.c0
  have member : owed ∈ m.state.deferreds.due := by
    rw [due]
    exact List.mem_singleton_self _
  have declared : w'.Θ Api.root 0 = some natTy := ord.1.2.2.2.2.2.1 Api.root 0 natTy rfl
  exact (table owed member natTy declared).1

/-- **`loop` does not keep `I`.** -/
theorem loop_false : ¬ StepPreserves (rootProgram : ProgramSource) unitTy (.loop Api.root false) := by
  intro step
  obtain ⟨w', ord, typed⟩ := step world machine [] rfl (config_typed _ (Or.inl rfl))
  exact untyped w' ord loopResult.1 loop_due typed.machine

/-- **`deliver` does not keep `I`.** -/
theorem deliver_false :
    ¬ StepPreserves (rootProgram : ProgramSource) unitTy (.deliver Api.root false) := by
  intro step
  obtain ⟨w', ord, typed⟩ := step world machine [] rfl (config_typed _ (Or.inr rfl))
  exact untyped w' ord deliverResult.1 deliver_due typed.machine

end Effect4.Program.Typed.SeatD3.LoopDeliver

#print axioms Effect4.Program.Typed.SeatD3.LoopDeliver.config_typed
#print axioms Effect4.Program.Typed.SeatD3.LoopDeliver.loop_false
#print axioms Effect4.Program.Typed.SeatD3.LoopDeliver.deliver_false
