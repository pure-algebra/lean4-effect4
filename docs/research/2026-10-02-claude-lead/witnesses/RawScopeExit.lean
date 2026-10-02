import Effect4.Laws.Program.Typed.Assembly

/-!
# Falsifier candidate: `M6Ledger.step_deliver` is false at `4c219956`

STATUS: UNCOMPILED. Written at source level against `4c219956e9fa952a34bb37cb5f89ab0ce657f74c`;
never passed to Lean. Every proof below copies a compiled precedent:
`Test/Counterexamples/Machine/Semantics/M6Capstone.lean`, namespace `H1HaltAmendment`
(`valid`, `scheduler`, `observers`, `registration`, `callback_typed`, `queue`, `result_*` by `rfl`,
`input_refused`), and `Test/Program/ExitConnector.lean` (`scopeWorld`, a store holding one scope).
The statement refuted is the frozen one, `StepPreserves root rootTy (.deliver id yielding)`
(`Typed/Assembly.lean:1760`, `#proof_wanted` at `:1924`), at `root := .succeed (.lit .unit)`,
`rootTy := unit`, `id := Api.root`, `yielding := false`.

The defect. `TypedProg` admits a raw scope-exit marker as current code: its `scopeExit`
constructor (`Typed/Residual.lean:306`) needs only the scope's presence, the payload at the
current type and a typed continuation. `ReadCode` reads current code through `TypedProg`
(`Typed/Assembly.lean`), so a running fiber whose current code is that marker, read by a queued
`deliver`, is part of a typed configuration. The machine never consumes such a marker as a
counted operation:

* `prepareR` leaves it unchanged (`Laws/Program/DenoteR.lean:65`);
* `evaluateFiberR`'s `scopeExit` arm installs `badShapeExit` (`Laws/Program/EvaluateR.lean:184-187`:
  "a raw marker arriving as a counted operation is outside that protocol");
* `prepareScopedExitR` sees no marker on `.pure badShapeExit`, and `settle` queues `loop`.

`badShapeExit = failure (die badName)` (`Laws/Program/Denote.lean:44`) is refused by `ExitOk`'s
`NoShapeDefect` (`Typed/Admission.lean:25-33`) at every world and type. So `ReadCode` fails after
the step at every later world. The marker reaches current code legitimately only through the
saved resume slot inside one delivery (`popR` → `prepareScopedExitR`, same `evaluateR`).
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Test.Counterexamples.Machine.Semantics.RawScopeExit
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
open Effect4.Program.Denote Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

/-! ## The general half: `badShapeExit` is untyped everywhere -/

/-- `badShapeExit` carries the `badName` defect, which `NoShapeDefect` refuses. -/
theorem badShapeExit_untyped (w : W) (ty : EffTy) : ¬ ExitOk w ty badShapeExit := by
  intro h
  have shape := h.2 _ (List.mem_singleton_self _)
  exact shape.1 rfl

/-! ## The witness -/

def rootProgram : NativeEff := .succeed (.lit .unit)
def unitTy : EffTy := EffTy.pure .unit

/-- A raw scope-exit marker of scope 0, as current code. -/
def marker : RProgram :=
  .vis (.inr (.scopeExit emptyCtx 0 (.success .unit))) (fun _ => .pure (.success .unit))

/-- A store holding one sequential scope, 0 (`Test/Program/ExitConnector.lean`'s `scopeWorld`). -/
def scopeStore : Stores :=
  { Stores.empty with scopes := Stores.empty.scopes.make 0 .sequential, nextName := 1 }

def rootFiber : RFiber :=
  { RunFiber.make Api.root marker true (stores.budgetOf emptyCtx) emptyCtx with running := true }

def machine : RState :=
  { loadR rootProgram 20 20 with fibers := [rootFiber], nextId := 1, state := scopeStore }

def world : W :=
  { initialWorld unitTy with
    Γ := fun id => if id = Api.root then some unitTy else none
    state := scopeStore }

def command : RCmd := .deliver Api.root false
def commands : List RCmd := [command]

theorem member_root (f : RFiber) (member : f ∈ machine.fibers) : f = rootFiber := by
  change f ∈ [rootFiber] at member
  exact List.mem_singleton.mp member

theorem scopeStore_wf : scopeStore.WF := by decide +kernel

theorem live : ScopeLive world 0 := by decide

theorem valid : WorldValid unitTy world machine := by
  constructor
  · rfl
  · intro id
    change (if id = Api.root then some unitTy else none).isSome = true ↔ id ∈ [Api.root]
    rw [List.mem_singleton]
    by_cases here : id = Api.root
    · rw [if_pos here]
      exact ⟨fun _ => here, fun _ => rfl⟩
    · rw [if_neg here]
      exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (here h)⟩
  · intro key
    change false = true ↔ key.index < 0
    exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  · intro key
    change false = true ↔ key.index < 0
    exact ⟨fun h => Bool.noConfusion h, fun h => False.elim (Nat.not_lt_zero _ h)⟩
  · intro f member token parked
    obtain rfl := member_root f member
    cases parked
  · intro id token ty declared; cases declared
  · intro id token ty declared; cases declared
  · rfl
  · exact scopeStore_wf
  · exact ⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩
  · intro id ty declared
    change (if id = Api.root then some unitTy else none) = some ty at declared
    split at declared
    · cases declared; exact ⟨rfl, rfl⟩
    · cases declared
  · intro key ty declared; cases declared
  · intro key types declared; cases declared
  · intro id token ty declared; cases declared
  · rfl
  · exact WakeTyped.empty _ _
  · intro key cell h; cases h

theorem no_requests (id : FiberId) (token : Nat) : requestOfR machine id token = none := by
  unfold requestOfR
  cases lookup : machine.fiber? id with
  | none => rfl
  | some found =>
    obtain rfl := member_root found (List.mem_of_find?_eq_some lookup)
    rfl

theorem scheduler : SchedulerState machine := by
  constructor
  · decide +kernel
  · intro f member
    obtain rfl := member_root f member
    decide +kernel
  · exact List.nodup_nil
  · intro race member; cases member
  · intro race member; cases member
  · intro key member; cases member
  · intro id token request lookup; rw [no_requests] at lookup; cases lookup
  · intro id token request lookup; rw [no_requests] at lookup; cases lookup
  · intro f member
    obtain rfl := member_root f member
    rfl
  · intro f member parked
    obtain rfl := member_root f member
    exact False.elim (parked rfl)
  · intro f member token parked
    obtain rfl := member_root f member
    cases parked
  · intro f member exited
    obtain rfl := member_root f member
    cases exited
  · intro f member exited
    obtain rfl := member_root f member
    cases exited
  · intro f member deferred
    obtain rfl := member_root f member
    cases deferred
  · intro raceId race hr; cases hr
  · intro raceId race hr; cases hr
  · intro f member p hp
    obtain rfl := member_root f member
    cases hp
  · intro f member o ho
    obtain rfl := member_root f member
    cases ho

theorem observers : ObserverState (rootProgram : ProgramSource) world machine := by
  constructor
  · intro f member pending hp
    obtain rfl := member_root f member
    cases hp
  · intro f member observer ho
    obtain rfl := member_root f member
    cases ho

theorem registration : RegistrationState (rootProgram : ProgramSource) world machine := by
  intro f member race found
  obtain rfl := member_root f member
  cases found

/-- The marker is typed wherever scope 0 is present (as `H1HaltAmendment.callback_typed`). -/
theorem marker_typed (w : W) (hlive : ScopeLive w 0) :
    TypedProg (rootProgram : ProgramSource) w unitTy marker :=
  .scopeExit hlive ⟨trivial, trivial⟩ (fun _ _ _ => .pure ⟨trivial, trivial⟩)

/-- The root's frame, code included: the marker over the empty stack. -/
theorem root_saved : SavedOk (TypedProg (rootProgram : ProgramSource)) ExitOk
    (frameProtocols (rootProgram : ProgramSource)) world unitTy rootFiber.frame :=
  ⟨unitTy, marker_typed world live, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩

theorem typedState : TypedState (rootProgram : ProgramSource) unitTy world machine := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_, scheduler, observers, registration⟩
  · intro f member
    obtain rfl := member_root f member
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty declared
      change some unitTy = some ty at declared
      cases declared
      exact ⟨unitTy, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro p hp; cases hp
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro bucket hb; cases hb
    · intro key value ty lookup
      change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
      rw [Env.Context.getV_empty] at lookup; cases lookup
  · intro race member; cases member
  · -- the store: no promise, heap cell, Deferred cell or memo entry; one empty scope
    refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩, (fun i v h => nomatch h),
      ⟨(fun i v h => nomatch h)⟩, ⟨fun e he => ?_⟩, (fun v hv => nomatch hv), trivial⟩
    change e ∈ [⟨0, Effect4.Scope.make .sequential⟩] at he
    rw [List.mem_singleton] at he
    subst he
    exact ⟨⟨trivial⟩⟩
  · intro f member token parked
    obtain rfl := member_root f member
    cases parked

theorem machineTyped : MachineTyped (rootProgram : ProgramSource) unitTy world machine := by
  refine ⟨typedState, rfl, ?_, ⟨rfl, fun o ho => nomatch ho⟩⟩
  intro f member _ idle
  obtain rfl := member_root f member
  cases idle

/-- **The input is a typed configuration**: the running root's marker is read by the queued
`deliver` (`ReadCode`) and typed by `TypedProg.scopeExit` at the world whose store holds scope 0. -/
theorem config : ConfigTyped (rootProgram : ProgramSource) unitTy world machine commands := by
  refine ⟨machineTyped, ?_, ⟨?_, ?_, ?_, ?_, ⟨trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro f member _ _ _ ty declared
    obtain rfl := member_root f member
    change some unitTy = some ty at declared
    cases declared
    exact root_saved
  · intro c member
    change c ∈ [command] at member
    rw [List.mem_singleton] at member
    subst member
    trivial
  · intro c member
    change c ∈ [command] at member
    rw [List.mem_singleton] at member
    subst member
    exact ⟨rootFiber, rfl, rfl, rfl⟩
  · intro c member
    change c ∈ [command] at member
    rw [List.mem_singleton] at member
    subst member
    trivial
  · decide +kernel
  · intro key member; cases member
  · intro id token request lookup; rw [no_requests] at lookup; cases lookup
  · intro source exit observer member
    change .observe source exit observer ∈ [command] at member
    rw [List.mem_singleton] at member
    cases member
  · intro race child member
    change .enrollRace race child ∈ [command] at member
    rw [List.mem_singleton] at member
    cases member
  · intro host yielding race member
    change .afterInterrupt host yielding (.race race) ∈ [command] at member
    rw [List.mem_singleton] at member
    cases member
  · intro mode scope target interruptor extra member
    change .link mode scope target interruptor extra ∈ [command] at member
    rw [List.mem_singleton] at member
    cases member
  · intro source exit observer member
    change .observe source exit observer ∈ [command] at member
    rw [List.mem_singleton] at member
    cases member

/-! ## The step and its result -/

def result : RState × List RCmd :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine command []

/-- The root after the step: `badShapeExit` installed over the same stack, still running. -/
def badFiber : RFiber :=
  { rootFiber with frame := { rootFiber.frame with current := .pure badShapeExit } }

theorem result_queue : result.2 = [.loop Api.root false] := rfl
theorem result_root : result.1.fiber? Api.root = some badFiber := rfl

/-- **The output is no typed configuration at any world**: the queued `loop` reads the root's
code (`ReadCode`), the root is declared (`WorldValid.fibers`), and its code is `badShapeExit`. -/
theorem output_refused (w : W) :
    ¬ ConfigTyped (rootProgram : ProgramSource) unitTy w result.1 result.2 := by
  intro after
  have valid' := after.machine.typed.1
  have member : badFiber ∈ result.1.fibers := List.mem_of_find?_eq_some result_root
  obtain ⟨ty, declared⟩ := Option.isSome_iff_exists.mp
    ((valid'.fibers Api.root).mpr (List.mem_map_of_mem member))
  have reads : ReadsCode Api.root result.2 :=
    ⟨false, Or.inl (by rw [result_queue]; exact List.mem_singleton_self _)⟩
  obtain ⟨tin, code, _, _⟩ := after.code badFiber member rfl reads rfl ty declared
  exact badShapeExit_untyped w tin (TypedProg.pure_inv code)

/-- **`StepPreserves` for `deliver` is false** (the frozen `M6Ledger.step_deliver` at this
instance). -/
theorem step_deliver_false : ¬ StepPreserves (rootProgram : ProgramSource) unitTy command := by
  intro step
  obtain ⟨w', _, after⟩ := step world machine [] rfl config
  exact output_refused w' after

/-- The ledger goal's universal form is false. -/
theorem step_deliver_universal_false :
    ¬ ∀ (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (yielding : Bool),
      StepPreserves root rootTy (.deliver id yielding) :=
  fun steps => step_deliver_false (steps _ _ _ _)

end Test.Counterexamples.Machine.Semantics.RawScopeExit

#print axioms Test.Counterexamples.Machine.Semantics.RawScopeExit.config
#print axioms Test.Counterexamples.Machine.Semantics.RawScopeExit.output_refused
#print axioms Test.Counterexamples.Machine.Semantics.RawScopeExit.step_deliver_false
