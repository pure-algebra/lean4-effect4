import Effect4.Laws.Program.Typed.Commands.Registration

/-!
# Test.Program.RegistrationColumn — row 134(d)'s race/observer boundary

Placement: semantics Concept 4 (`reactive-scheduling`), scheduler step
preservation and step invariant lifting; `M6Ledger.step_registrationDone`. The general theorem
is `registrationDone_preserves`. These controls serve its repaired input boundary, decision
134(d), and the exact historical `E4-TYPED-CE-028` witness in
`docs/research/2026-10-01-landing/seat-D3/probes/Races.lean`, namespace `Registration`.

The race host is running its registration marker, with no pending answer and no deferred
interrupt. Its race token remains declared `nat`. A stored countdown on that same key is now
refused by `SchedulerState.raceObservers`, hence by `ConfigTyped`. Removing only that countdown
makes this concrete input typed; the actual command theorem supplies a typed result in an
extending world, whose host has a `void` pending record and is idle on the race token.

Reach: one constructed input and one command; the negative machine is not asserted reachable.
The positive control does not prove that registration establishes row 134(d), general reachability,
progress, fairness, host response, or generated-code agreement. It exercises one M6 command
premise on the M5 -> M6 -> M7 spine; it supplies no new capstone or ledger instance.
-/

set_option autoImplicit false

namespace Test.Program.RegistrationColumn
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

def rootProgram : NativeEff := .succeed (.lit (.nat 0))
def natTy : EffTy := EffTy.pure .nat

def marker : RProgram := .vis (.inr (.raceRegister 0)) Effects.Program.pure
theorem provenance (f : RSaved) (h1 : f.interruptedCause = none) (h2 : f.deferredInterrupt = false) :
    InterruptProvenance f := by
  refine ⟨fun c hc => ?_, fun hd => ?_⟩
  · rw [h1] at hc
    cases hc
  · rw [h2] at hd
    cases hd

theorem emptyPayload (w : W) (r : Effect4.Program.Typed.RRace) (ty : EffTy) (token : w.Θ r.host r.token = some ty)
    (failures : r.state.failures = []) (winner : r.state.winner = none)
    (accepted : r.state.accepted = none) (cleanup : r.state.cleanup = none)
    (live : ∀ id ∈ r.state.live, FiberColumnsBelow w id ty.answer ty.error)
    (programs : ∀ code ∈ r.programs, ∃ childTy, TypedProg (rootProgram : ProgramSource) w childTy code ∧
      Ty.subN childTy.answer ty.answer = true ∧ Ty.subN childTy.error ty.error = true) :
    RacePayload (rootProgram : ProgramSource) w r ty := by
  refine ⟨token, ?_, fun pair hp => ?_, fun e he => ?_, fun wait hw => ?_, live, programs⟩
  · rw [failures]
    exact ⟨failureFits_of_cause (fun _ h => nomatch h) (fun _ h => nomatch h),
      (fun _ h => nomatch h)⟩
  · rw [winner] at hp
    cases hp
  · rw [accepted] at he
    cases he
  · rw [cleanup] at hw
    cases hw

#print axioms emptyPayload

def fiber : RFiber :=
  { RunFiber.make Api.root marker true (stores.budgetOf emptyCtx) emptyCtx with
    running := true }

def race : Effect4.Program.Typed.RRace :=
  { id := 0, host := Api.root, token := 0, state := Supervision.RaceAllState.initial [],
    settled := false, programs := [], registering := true }

def machine : RState :=
  { loadR rootProgram 20 20 with fibers := [fiber], races := [race], nextToken := 1, nextRace := 1 }

def world : W :=
  { initialWorld natTy with Θ := fun id t => if id = Api.root ∧ t = 0 then some natTy else none }

theorem member {f : RFiber} (hf : f ∈ machine.fibers) : f = fiber := by
  change f ∈ [fiber] at hf
  exact List.mem_singleton.mp hf

theorem theta {id : FiberId} {t : Nat} {ty : EffTy} (h : world.Θ id t = some ty) :
    id = Api.root ∧ t = 0 ∧ ty = natTy := by
  change (if id = Api.root ∧ t = 0 then some natTy else none) = some ty at h
  by_cases c : id = Api.root ∧ t = 0
  · rw [if_pos c] at h
    cases h
    exact ⟨c.1, c.2, rfl⟩
  · rw [if_neg c] at h
    cases h

theorem valid : WorldValid natTy world machine := by
  have old := initial_world_valid_at natTy nativeServiceTy rootProgram 20 20
  refine
    { ids := rfl, fibers := old.fibers, heap := old.heap, promises := old.promises,
      tokens := ?_, tokenBound := ?_, tokenTargets := ?_, state := rfl, wf := old.wf,
      cells := old.cells, root := old.root,
      timers := WakeTyped.empty _ _, waiters := fun _ _ h => by cases h }
  · intro f hf token hp
    rw [member hf] at hp
    cases hp
  · intro id token ty h
    obtain ⟨_, rfl, _⟩ := theta h
    exact Nat.zero_lt_one
  · intro id token ty h
    obtain ⟨rfl, _, _⟩ := theta h
    rfl

theorem no_requests (id : FiberId) (token : Nat) : requestOfR machine id token = none := by
  unfold requestOfR
  cases hf : machine.fiber? id with
  | none => rfl
  | some found =>
    rw [member (List.mem_of_find?_eq_some hf)]
    rfl

theorem internalKeys_machine : Guard.internalKeys machine = [(Api.root, 0)] := rfl

theorem typedState : TypedState (rootProgram : ProgramSource) natTy world machine := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro f hf
    rw [member hf]
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty _
      exact ⟨ty, .nil ty, provenance _ rfl rfl⟩
    · intro p hp; cases hp
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro v hv; cases hv
    · intro key value ty lookup
      change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
      rw [Env.Context.getV_empty] at lookup
      cases lookup
  · intro r hr
    change r ∈ [race] at hr
    rw [List.mem_singleton.mp hr]
    exact ⟨natTy, emptyPayload world race natTy rfl rfl rfl rfl rfl (fun _ h => nomatch h)
      (fun _ h => nomatch h)⟩
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩,
      (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f hf token hp
    rw [member hf] at hp
    cases hp
  · constructor
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · intro f hf
      rw [member hf]
      exact Nat.zero_lt_one
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · intro r hr
      change r ∈ [race] at hr
      rw [List.mem_singleton.mp hr]
      exact Nat.zero_lt_one
    · intro r hr
      change r ∈ [race] at hr
      rw [List.mem_singleton.mp hr]
      exact ⟨fiber, rfl⟩
    · intro key hk
      rw [internalKeys_machine] at hk
      rw [List.mem_singleton.mp hk]
      exact Nat.zero_lt_one
    · intro id token request hr
      rw [no_requests] at hr
      cases hr
    · intro id token request hr
      rw [no_requests] at hr
      cases hr
    · intro f hf
      rw [member hf]
      rfl
    · intro f hf hp
      rw [member hf] at hp
      exact False.elim (hp rfl)
    · intro f hf token hp
      rw [member hf] at hp
      cases hp
    · intro f hf hx
      rw [member hf] at hx
      cases hx
    · intro f hf hx
      rw [member hf] at hx
      cases hx
    · intro f hf hd
      rw [member hf] at hd
      cases hd
    · intro raceId r hr f hf o ho
      rw [member hf] at ho
      cases ho
    · intro raceId r hr id hi
      have mem : r ∈ machine.races := List.mem_of_find?_eq_some hr
      change r ∈ [race] at mem
      rw [List.mem_singleton.mp mem] at hi
      cases hi
    · intro f hf p hp
      rw [member hf] at hp
      cases hp
    · intro f hf o ho
      rw [member hf] at ho
      cases ho
  · intro f hf p hp
    rw [member hf] at hp
    cases hp
  · intro f hf o ho
    rw [member hf] at ho
    cases ho
  · intro f hf raceId hm
    rw [member hf] at hm ⊢
    change some 0 = some raceId at hm
    cases hm
    exact ⟨race, natTy, rfl, rfl, rfl, natTy, rfl, .nil natTy, provenance _ rfl rfl⟩

theorem machine_typed : MachineTyped (rootProgram : ProgramSource) natTy world machine := by
  refine ⟨typedState, rfl, ?_, ⟨rfl, fun o ho => nomatch ho⟩, rfl⟩
  intro f hf _ idle
  rw [member hf] at idle
  cases idle

theorem config_typed : ConfigTyped (rootProgram : ProgramSource) natTy world machine
    [.registrationDone 0 false] := by
  refine ⟨machine_typed, ?_, ?_⟩
  · intro f _ _ reads
    obtain ⟨_, r⟩ := reads
    rcases r with r | r <;> (rw [List.mem_singleton] at r; cases r)
  · refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      ⟨trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨race, fiber, rfl, rfl, rfl, rfl, rfl⟩
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
    · intro source exit observer member
      rw [List.mem_singleton] at member
      cases member

def result :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine (.registrationDone 0 false) []

/-- CE-028's historical fiber, with its countdown still stored on the race key. -/
def historicalFiber : RFiber :=
  { RunFiber.make Api.root marker true (stores.budgetOf emptyCtx) emptyCtx with
    running := true, observers := [.countdown Api.root 0] }

def historicalMachine : RState :=
  { loadR rootProgram 20 20 with
    fibers := [historicalFiber]
    races := [race]
    nextToken := 1
    nextRace := 1 }

theorem only_countdown_removed :
    { historicalMachine with fibers := [{ historicalFiber with observers := [] }] } = machine := rfl

/-- The old witness is excluded by the exact new clause, without changing the race token's type. -/
theorem historical_scheduler_refused : ¬ SchedulerState historicalMachine := by
  intro scheduler
  have off := scheduler.raceObservers 0 race rfl historicalFiber
    (show historicalFiber ∈ historicalMachine.fibers from List.mem_singleton_self _)
    (.countdown Api.root 0)
    (show .countdown Api.root 0 ∈ historicalFiber.observers from List.mem_singleton_self _)
  exact off (show (race.host, race.token) ∈ Guard.observerKeys (.countdown Api.root 0) from
    List.mem_singleton_self _)

/-- `I` rejects the historical machine for every world and every queue through its scheduler clause. -/
theorem historical_config_refused (w : W) (commands : List RCmd) :
    ¬ ConfigTyped (rootProgram : ProgramSource) natTy w historicalMachine commands := by
  intro typed
  exact historical_scheduler_refused typed.machine.typed.2.2.2.1

/-- Concrete no-answer branch: the host is idle, its race key carries the `void` park,
no countdown remains to read that record, and the command leaves no queued work. -/
theorem parked : ∃ g, result.1.fibers = [g] ∧ result.1.fiber? Api.root = some g ∧
    g.id = Api.root ∧ g.pending = [⟨0, none, [], [], .void, false⟩] ∧
    g.observers = [] ∧ g.parked = .withGuard 0 ∧ g.running = false ∧ result.2 = [] :=
  ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem registration_flag_cleared :
    (result.1.race? 0).map (·.registering) = some false := rfl

/-- The current input predicate is inhabited, and the actual preservation theorem types the step. -/
theorem result_typed : ∃ w', world.leHost w' ∧
    ConfigTyped (rootProgram : ProgramSource) natTy w' result.1 result.2 := by
  exact registrationDone_preserves (rootProgram : ProgramSource) natTy 0 false
    world machine [] rfl config_typed

/-- Stepping the raw historical machine still produces the mismatched park. Its new rejection
comes from the input predicate, not a changed machine transition. -/
def historicalResult :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) historicalMachine (.registrationDone 0 false) []

theorem historical_parked : ∃ g, historicalResult.1.fibers = [g] ∧
    historicalResult.1.fiber? Api.root = some g ∧ g.id = Api.root ∧
    g.pending = [⟨0, none, [], [], .void, false⟩] ∧ g.observers = [.countdown Api.root 0] :=
  ⟨_, rfl, rfl, rfl, rfl, rfl⟩

end Test.Program.RegistrationColumn

#print axioms Test.Program.RegistrationColumn.provenance
#print axioms Test.Program.RegistrationColumn.member
#print axioms Test.Program.RegistrationColumn.theta
#print axioms Test.Program.RegistrationColumn.valid
#print axioms Test.Program.RegistrationColumn.no_requests
#print axioms Test.Program.RegistrationColumn.internalKeys_machine
#print axioms Test.Program.RegistrationColumn.typedState
#print axioms Test.Program.RegistrationColumn.machine_typed
#print axioms Test.Program.RegistrationColumn.config_typed
#print axioms Test.Program.RegistrationColumn.only_countdown_removed
#print axioms Test.Program.RegistrationColumn.historical_scheduler_refused
#print axioms Test.Program.RegistrationColumn.historical_config_refused
#print axioms Test.Program.RegistrationColumn.parked
#print axioms Test.Program.RegistrationColumn.registration_flag_cleared
#print axioms Test.Program.RegistrationColumn.result_typed
#print axioms Test.Program.RegistrationColumn.historical_parked
