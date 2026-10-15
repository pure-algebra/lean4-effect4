import Effect4.Laws.Machine.Lift
import Effect4.Laws.Machine.EditWords
import Effect4.Laws.Auto.RuleSets

/-!
Concept: scope-lifetime-finalization, R11.
Question: store preservation serves ReleaseCustody.Execution.history through its ScopeRows invariant.
Reach: the actual evaluator and command runner, with one premise per interpreter store hook.
Limit: the contract proves no fiber invariant, command ownership, progress or host agreement.
Unlock: allocation invariants reuse one runner census and their existing store-operation laws.
-/
set_option autoImplicit false
namespace Effect4.Machine.StatePreservation
open Effect4
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]

/-- The actual store hooks preserve the same predicate. Consumer: command and primitive preservation. -/
structure Hooks (interp : RunInterp ν σ β ε δ ι α χ St κ) (P : St → Prop) : Prop where
  sync : ∀ name state next value, P state → interp.syncState name state = some (next, value) → P next
  async : ∀ name id token state, P state → P (interp.registerAsync name id token state).1
  link : ∀ mode scope id state next key, P state →
    interp.scopeLinkFiber mode scope id state = some (next, key) → P next
  close : ∀ scope exit mask id state next code, P state →
    interp.closeScope scope exit mask id state = some (next, code) → P next
  drop : ∀ scope key state next, P state → interp.dropFinalizer scope key state = some next → P next
  due : ∀ state, P state → P (interp.dueResumes state).2
  wake : ∀ list phase state, P state → P (interp.wakeList list phase state)

/-- Commands use only administrative store hooks. Source operations retain their own local premises.
Consumer: the crews' captured scope invariant through the coupled driver. -/
structure CommandHooks (interp : RunInterp ν σ β ε δ ι α χ St κ) (P : St → Prop) : Prop where
  link : ∀ mode scope id state next key, P state →
    interp.scopeLinkFiber mode scope id state = some (next, key) → P next
  drop : ∀ scope key state next, P state → interp.dropFinalizer scope key state = some next → P next
  due : ∀ state, P state → P (interp.dueResumes state).2
  wake : ∀ list phase state, P state → P (interp.wakeList list phase state)

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Unconditional store preservation supplies every administrative hook. -/
theorem Hooks.commands {interp : RunInterp ν σ β ε δ ι α χ St κ} {P : St → Prop}
    (hooks : Hooks interp P) : CommandHooks interp P :=
  ⟨hooks.link, hooks.drop, hooks.due, hooks.wake⟩

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] core in
/-- Keyed fiber edits leave the store untouched. Consumer: observer and scope-link steps. -/
theorem modify_state (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId)
    (edit : RunFiber ν σ β ε δ ι α χ κ φ → RunFiber ν σ β ε δ ι α χ κ φ) :
    (m.modify id edit).state = m.state := by
  unfold RunMachine.modify
  split <;> rfl

/-- Recording a list of interrupts leaves the store untouched. Consumer: countdown observers. -/
theorem interruptEach_state (interp : RunInterp ν σ β ε δ ι α χ St κ) (who : FiberId)
    (extra : ReasonAnnotations α) (ids : List FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ)) :
    (interruptEach interp who extra ids acc).1.state = acc.1.state := by
  induction ids generalizing acc with
  | nil => rfl
  | cons id ids ih =>
    simp only [interruptEach, List.foldl_cons]
    split
    · exact ih _
    · exact ih _

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] core in
/-- Scope linking uses exactly the interpreter's link hook. Consumer: native actions and commands. -/
theorem link_plan_with (interp : RunInterp ν σ β ε δ ι α χ St κ) (P : St → Prop) (hooks : CommandHooks interp P)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations α)
    (held : P m.state) : P (linkScopeEdits interp m mode scope target who extra).1.state := by
  rw [Edits.link_plan_word]
  simp only [Edits.linkWord]
  split
  · exact held
  · split
    · exact held
    · exact held
  · split
    · exact held
    · split
      · exact held
      · split
        · exact held
        · rename_i state key step
          exact hooks.link mode scope target m.state state key held step

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] core in
/-- The full store contract supplies the administrative link contract. -/
theorem link_plan (interp : RunInterp ν σ β ε δ ι α χ St κ) (P : St → Prop) (hooks : Hooks interp P)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations α)
    (held : P m.state) : P (linkScopeEdits interp m mode scope target who extra).1.state :=
  link_plan_with interp P hooks.commands m mode scope target who extra held

/-- The eager scope-link view interprets a fiber-only word after its store hook. -/
theorem link_with (interp : RunInterp ν σ β ε δ ι α χ St κ) (P : St → Prop) (hooks : CommandHooks interp P)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations α)
    (held : P m.state) : P (linkScope interp m mode scope target who extra).1.state := by
  unfold linkScope
  have shape := RunMachine.applyFiberEdits_shape
    (linkScopeEdits interp m mode scope target who extra).2
    (linkScopeEdits interp m mode scope target who extra).1
  rw [congrArg RunMachine.state shape.1]
  exact link_plan_with interp P hooks m mode scope target who extra held

/-- The full store contract supplies the eager administrative link contract. -/
theorem link (interp : RunInterp ν σ β ε δ ι α χ St κ) (P : St → Prop) (hooks : Hooks interp P)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (mode : Supervision.ScopeMode)
    (scope : Nat) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations α)
    (held : P m.state) : P (linkScope interp m mode scope target who extra).1.state :=
  link_with interp P hooks.commands m mode scope target who extra held

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Forking the parallel cleanup list leaves the store untouched. Consumer: native close actions. -/
theorem forkFinalizers_state (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (host : RunFiber ν σ β ε δ ι α χ κ φ)
    (programs : List κ) : (forkFinalizers interp m host programs).1.state = m.state := by
  induction programs generalizing m with
  | nil => rfl
  | cons program rest ih => exact ih _

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- The canonical countdown plan changes no store. Consumer: actual native parks. -/
theorem countdown_plan_state (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (f : RunFiber ν σ β ε δ ι α χ κ φ)
    (targets : List FiberId) (resume : Resume ν) (failFast : Bool) :
    (countdownParkEdits interp m f targets resume failFast).1.state = m.state := by
  rw [Edits.countdown_word]
  simp only [Edits.countdownWord, Edits.run_append, Edits.run_cons, Edits.run_nil, Edit.apply]
  split <;> rfl

/-- Countdown registration interprets only a fiber word after the canonical plan. -/
theorem countdown_state (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (f : RunFiber ν σ β ε δ ι α χ κ φ)
    (targets : List FiberId) (resume : Resume ν) (failFast : Bool) :
    (countdownPark interp m f targets resume failFast).1.state = m.state := by
  unfold countdownPark
  have shape := RunMachine.applyFiberEdits_shape
    (countdownParkEdits interp m f targets resume failFast).2.2.2
    (countdownParkEdits interp m f targets resume failFast).1
  rw [congrArg RunMachine.state shape.1]
  exact countdown_plan_state interp m f targets resume failFast

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- The disposition changes no store. Consumer: exact R2 settlement. -/
theorem settleOutcome_state (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α κ))
    (it : Iter ν σ β ε δ ι α χ St κ φ η) : (settleOutcome id rest it).1.state = it.machine.state := by
  rw [Edits.outcome_word]
  cases found : it.outcome with
  | parked =>
    simp only [Edits.outcomeWord, found]
    split <;> rfl
  | _ => simp only [Edits.outcomeWord, found]; rfl

/-- Settlement installs the local result and interprets fiber-only edits before disposition. -/
theorem settle_state (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α κ))
    (it : Iter ν σ β ε δ ι α χ St κ φ η) : (settle id rest it).1.state = it.machine.state := by
  unfold settle
  split
  · exact settleOutcome_state id rest it
  · have shape := RunMachine.applyFiberEdits_shape it.edits (it.machine.update it.fiber)
    have same := congrArg RunMachine.state shape.1
    dsimp only
    split
    · exact same
    · exact (settleOutcome_state id rest _).trans same

section Primitive
variable (interp : RunInterp ν σ β ε δ ι α χ St) (P : St → Prop) (hooks : Hooks interp P)

/-- A frame step only emits events. Consumer: primitive evaluator. -/
theorem stepFrame (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (held : P m.state) : P (evaluatePrim.stepFrame interp m f yielding).machine.state := by
  simp only [evaluatePrim.stepFrame, evaluatePrim.finishFrame]
  split <;> exact held

/-- A finalizer handoff only emits events. Consumer: primitive evaluator. -/
theorem finalizerOr (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (exit : Exit β ε δ ι α) (held : P m.state) :
    P (evaluatePrim.finalizerOr interp m f yielding exit).machine.state := by
  cases exit <;> simp only [evaluatePrim.finalizerOr]
  all_goals
    split
    · split
      · exact held
      · exact stepFrame interp P _ _ _ held
    · exact stepFrame interp P _ _ _ held

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- All fiber actions preserve the store predicate through their declared hooks.
Consumer: primitive evaluation, including source actions after native elaboration. -/
theorem withFiber_on (admin : CommandHooks interp P)
    (close : ∀ scope exit mask id state next code, P state →
      interp.closeScope scope exit mask id state = some (next, code) → P next)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (action : WithFiberAction ν σ β ε δ ι α χ) (held : P m.state) :
    P (evaluatePrim.withFiber interp m f yielding action).machine.state := by
  cases action with
  | closeScope scope exit =>
    simp only [evaluatePrim.withFiber]
    split
    · exact held
    · next state step => exact close scope exit f.frame.interruptible f.id m.state state none held step
    · next state code step =>
      exact close scope exit f.frame.interruptible f.id m.state state (some code) held step
  | runIn target scope => exact link_plan_with interp P admin m _ scope target _ _ held
  | awaitAll targets => exact (countdown_plan_state interp m f targets .exitsValue false) ▸ held
  | awaitAllFailFast targets => exact (countdown_plan_state interp m f targets .exitsValue true) ▸ held
  | awaitNewChildren snapshot => exact (countdown_plan_state interp m f _ .void false) ▸ held
  | closePar programs => exact (forkFinalizers_state interp m f programs) ▸ held
  | fork program options site =>
    simp only [evaluatePrim.withFiber, spawn, start]
    split <;> split <;> exact held
  | forkIn program options scope site =>
    simp only [evaluatePrim.withFiber, spawn, start]
    split <;> exact held
  | forkScoped program options site =>
    simp only [evaluatePrim.withFiber]
    split
    · simp only [spawn, start]
      split <;> exact held
    · exact held
  | interruptAs target who =>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
    split <;> exact held
  | ambientScope | interruptScoped | cancelRace =>
    simp only [evaluatePrim.withFiber]
    split <;> exact held
  | setInterruptible body flag => cases flag <;> exact held
  | _ => exact held

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
include hooks in
/-- The full hook contract supplies action preservation without another action classification. -/
theorem withFiber (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (action : WithFiberAction ν σ β ε δ ι α χ) (held : P m.state) :
    P (evaluatePrim.withFiber interp m f yielding action).machine.state :=
  withFiber_on interp P hooks.commands hooks.close m f yielding action held

/-- The actual current primitive supplies its own store permissions.
Consumer: source-qualified Atomic and pending-initializer store facts. -/
theorem primitive_at (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (held : P m.state)
    (sync_preserves : ∀ name state value, f.frame.current = .sync name →
      interp.syncState name m.state = some (state, value) → P state)
    (async_preserves : ∀ name signal cancel, f.frame.current = .async name signal cancel →
      P (interp.registerAsync name f.id m.nextToken m.state).1)
    (action_preserves : ∀ thunk action, f.frame.current = .withFiber thunk →
      interp.withFiberOf thunk = some action → P (evaluatePrim.withFiber interp m f yielding action).machine.state) :
    P (evaluatePrim interp m f yielding).machine.state := by
  simp only [evaluatePrim]
  split
  · exact held
  · rename_i name signal cancel current
    have changed := async_preserves name signal cancel current
    split
    · exact changed
    · exact changed
  · split
    · exact held
    · unfold registerRace
      split <;> exact held
    · exact (countdown_plan_state interp m f _ .exitsValue false) ▸ held
    · split
      · exact held
      · split <;> exact held
    · split
      · split
        · apply action_preserves
          all_goals assumption
        · exact stepFrame interp P _ _ _ held
      · split
        · rename_i state value step
          exact sync_preserves _ state value (by assumption) step
        · exact held
      · exact finalizerOr interp P _ _ _ _ held
      · exact finalizerOr interp P _ _ _ _ held
      · exact stepFrame interp P _ _ _ held

include hooks in
/-- The primitive evaluator accesses the store only through the named hooks.
Consumer: native allocation preservation and its command lift. -/
theorem primitive (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (held : P m.state) : P (evaluatePrim interp m f yielding).machine.state := by
  apply primitive_at interp P m f yielding held
  · intro name state value current produced
    exact hooks.sync name m.state state value held produced
  · intro name signal cancel current
    exact hooks.async name f.id m.nextToken m.state held
  · intro thunk action current found
    exact withFiber interp P hooks m f yielding action held
end Primitive

section Commands
variable (interp : RunInterp ν σ β ε δ ι α χ St κ) (P : St → Prop) (hooks : Hooks interp P)

/-- An observer changes the store only when it drops a scope registration.
Consumer: observation and race-enrollment commands. -/
theorem observer_with (admin : CommandHooks interp P) (id : FiberId) (exit : Exit β ε δ ι α)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ))
    (obs : Observer) (held : P acc.1.state) : P (fireObserver interp id exit acc obs).1.state := by
  cases obs with
  | resumeAwait => exact held
  | untrackChild => simpa only [fireObserver, modify_state, RunMachine.emit] using held
  | dropScopeFinalizer scope key =>
    simp only [fireObserver]
    split
    · exact held
    · rename_i state step
      exact admin.drop scope key acc.1.state state held step
  | countdown waiter token =>
    simp only [fireObserver]
    repeat' split
    all_goals simpa only [RunMachine.applyFiberEdit_state, RunMachine.update,
      interruptEach_state, RunMachine.emit] using held
  | raceCallback =>
    simp only [fireObserver]
    split
    · exact held
    · split <;> exact held
  | callback => exact held

include hooks in
/-- The full store contract supplies the observer's administrative hook. -/
theorem observer (id : FiberId) (exit : Exit β ε δ ι α)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ))
    (obs : Observer) (held : P acc.1.state) : P (fireObserver interp id exit acc obs).1.state :=
  observer_with interp P hooks.commands id exit acc obs held

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Publishing an exit changes fiber records and the trace alone. Consumer: finish commands. -/
theorem exit_state (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (f : RunFiber ν σ β ε δ ι α χ κ φ) (exit : Exit β ε δ ι α) :
    (exitFiber interp m f exit).1.state = m.state := by
  simp only [exitFiber, exitFiber.exitInterruptChildren, exitFiber.exitStore]
  split
  · rfl
  · split <;> rfl

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] core in
/-- Posting owed resumes leaves the store untouched. Consumer: the due drain. -/
theorem drain_state (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (due : List (Owed κ)) :
    (drainOwed m due).1.state = m.state := by
  induction due generalizing m with
  | nil => rfl
  | cons owed rest ih =>
    simp only [drainOwed]
    split
    · exact ih m
    · rw [ih]
      unfold RunMachine.postTask
      split <;> rfl

variable [evaluator : FiberEvaluator ν σ β ε δ ι α χ St κ φ η]

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- The charged iteration uses the evaluator after its fiber-only preparation.
Consumer: the loop command. -/
theorem iteration (evaluate : ∀ m f yielding, P m.state →
      P (evaluator.evaluate interp m f yielding).machine.state)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (f : RunFiber ν σ β ε δ ι α χ κ φ)
    (yielding : Bool) (held : P m.state) : P (Machine.iteration interp m f yielding).machine.state := by
  unfold Machine.iteration injectYield
  dsimp only
  split
  · rename_i it selected
    split at selected
    · cases selected
      exact evaluate _ _ _ held
    · cases selected
  · exact evaluate _ _ _ held

/-- A command reads the evaluator fact at its actual lookup and command kind.
Consumer: the crews' scope captures, whose sync premise comes from the typed source operation. -/
theorem command_on (admin : CommandHooks interp P)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (command : Cmd ν σ β ε δ ι α κ)
    (rest : List (Cmd ν σ β ε δ ι α κ)) (held : P m.state)
    (iterate : ∀ id yielding f, command = .loop id yielding → m.fiber? id = some f →
      P (Machine.iteration interp m f yielding).machine.state)
    (deliver : ∀ id yielding f, command = .deliver id yielding → m.fiber? id = some f →
      P (evaluator.evaluate interp m f yielding).machine.state) :
    P (driveStep interp m command rest).1.state := by
  cases command with
  | loop id yielding =>
    simp only [driveStep]
    split
    · exact held
    · rw [settle_state]
      exact iterate _ _ _ rfl (by assumption)
  | deliver id yielding =>
    simp only [driveStep]
    split
    · exact held
    · rw [settle_state]
      exact deliver _ _ _ rfl (by assumption)
  | link mode scope target who extra => exact link_with interp P admin _ mode scope target who extra held
  | observe id exit obs => exact observer_with interp P admin id exit (m, []) obs held
  | finish id exit =>
    simp only [driveStep]
    split
    · exact held
    · simpa only [exit_state] using held
  | drainDue =>
    change P (drainOwed {m with state := (interp.dueResumes m.state).2}
      (interp.dueResumes m.state).1).1.state
    rw [drain_state]
    exact admin.due m.state held
  | wake list phase => exact admin.wake list phase m.state held
  | enrollRace rid child =>
    simp only [driveStep]
    split
    · split
      · exact observer_with interp P admin _ _ _ _ held
      · simpa only [modify_state, RunMachine.updateRace] using held
    · exact held
  | registrationDone =>
    simp only [driveStep]
    repeat' split
    all_goals simpa only [settle_state, RunMachine.emit, RunMachine.updateRace] using held
  | afterInterrupt | closeParAwait =>
    simp only [driveStep]
    split
    · exact held
    · simpa only [settle_state, RunMachine.emit, RunMachine.updateRace] using held
  | trackChild =>
    simp only [driveStep]
    split
    · exact held
    · split
      · exact held
      · simpa only [modify_state, RunMachine.updateRace] using held
  | evaluate | resume | launch | interruptTarget | raceCancel | exitDone =>
    simp only [driveStep, launchEntrant, spawn]
    repeat' split
    all_goals exact held

include hooks in
/-- Unconditional evaluation supplies the contextual command contract.
Consumer: existing store-invariant histories. -/
theorem command (evaluate : ∀ m f yielding, P m.state →
      P (evaluator.evaluate interp m f yielding).machine.state)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (command : Cmd ν σ β ε δ ι α κ)
    (rest : List (Cmd ν σ β ε δ ι α κ)) (held : P m.state) :
    P (driveStep interp m command rest).1.state :=
  command_on interp P hooks.commands m command rest held
    (fun _ yielding f _ _ => iteration interp P evaluate m f yielding held)
    (fun _ yielding f _ _ => evaluate m f yielding held)

include hooks in
/-- Existing command induction transports the store predicate through every fuel prefix.
Consumer: allocation preservation at actual task and decision boundaries. -/
theorem drive (evaluate : ∀ m f yielding, P m.state →
      P (evaluator.evaluate interp m f yielding).machine.state)
    (fuel : Nat) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (commands : List (Cmd ν σ β ε δ ι α κ)) (held : P m.state) :
    P (driveState interp fuel m commands).1.state := by
  exact Lift.driveState_lift_unit interp (fun m _ => P m.state)
    (fun m cmd rest _ held => command interp P hooks evaluate m cmd rest held) fuel m commands held
end Commands
end Effect4.Machine.StatePreservation
